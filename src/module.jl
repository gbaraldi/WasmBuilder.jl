# A WebAssembly module under construction: its types, functions (with their bodies as
# lists of instructions), globals, tags, linear memory, data segments and exports. Function and global
# indices are assigned when the module is written, so that imports and definitions can
# be added in any order.

"""
    Inst(op, imms...)

An instruction: its name (as in the text format, with `.` replaced by `_`) and its
immediates. Function, global and tag immediates are the objects themselves, resolved to
indices when the module is written.
"""
struct Inst
    op::Symbol
    imm::Tuple
end
Inst(op::Symbol, imm...) = Inst(op, imm)

"""
    Func

A function of a module, imported (`imported` is `(module, name)`) or defined, with its
type, locals beyond the parameters, and body.
"""
mutable struct Func
    idx::Int
    name::String
    type::TypeRef
    params::Vector{ValType}
    results::Vector{ValType}
    locals::Vector{ValType}
    body::Vector{Inst}
    imported::Union{Nothing,Tuple{String,String}}
end

"A global of a module: its type, mutability and constant initializer."
mutable struct Global
    idx::Int
    name::String
    type::ValType
    mutable::Bool
    init::Vector{Inst}
end

"An exception tag, with the function type of its payload."
mutable struct Tag
    idx::Int
    type::TypeRef
end

"The module's linear memory: its limits, in pages of 64 KiB."
mutable struct LinearMemory
    min::Int
    max::Union{Nothing,Int}
end

"""
    WModule()

A WebAssembly module under construction. All its types are defined in one recursion
group, so that types with the same structure are distinct (nominal), which the code
generator relies on to test for the Julia type of a value.
"""
mutable struct WModule
    types::Vector{SubType}
    functypes::Dict{Tuple{Vector{ValType},Vector{ValType}},TypeRef}
    funcs::Vector{Func}
    globals::Vector{Global}
    tags::Vector{Tag}
    "The linear memory, if the module has one (one at most)."
    memory::Union{Nothing,LinearMemory}
    datas::Vector{Vector{UInt8}}
    exports::Vector{Tuple{String,Any}}
    start::Union{Nothing,Func}
    "The functions referenced by `ref.func`, which must be declared."
    declared::Vector{Func}
    declared_set::Set{Func}
end

WModule() = WModule(SubType[], Dict{Tuple{Vector{ValType},Vector{ValType}},TypeRef}(),
                    Func[], Global[], Tag[], nothing, Vector{UInt8}[], Tuple{String,Any}[], nothing,
                    Func[], Set{Func}())

"Add the type definition `t`, returning a reference to it."
function add_type!(m::WModule, t::SubType)
    push!(m.types, t)
    return TypeRef(length(m.types) - 1)
end
add_type!(m::WModule, t::CompType; kw...) = add_type!(m, SubType(t; kw...))

"The type definition of `t`."
typedef(m::WModule, t::TypeRef) = m.types[t.idx+1]

"The (deduplicated) function type with `params` and `results`."
function functype!(m::WModule, params::Vector{ValType}, results::Vector{ValType})
    t = get(m.functypes, (params, results), nothing)
    t === nothing || return t
    # copies, so that the caller mutating its vectors does not change the key
    return m.functypes[(copy(params), copy(results))] =
        add_type!(m, FuncType(copy(params), copy(results)))
end

"Declare a function of the module named `name`, with an empty body."
function add_func!(m::WModule, name::AbstractString, params::Vector{ValType},
                   results::Vector{ValType})
    f = Func(-1, String(name), functype!(m, params, results), params, results, ValType[],
             Inst[], nothing)
    push!(m.funcs, f)
    return f
end

"""
Import a function `mod.name` with `params` and `results`. Importing the same name with
the same signature again returns the same function; with another signature, a distinct
import (a JavaScript host function can be imported at several types).
"""
function add_import!(m::WModule, mod::AbstractString, name::AbstractString,
                     params::Vector{ValType}, results::Vector{ValType})
    type = functype!(m, params, results)
    for f in m.funcs
        f.imported == (mod, name) && f.type == type && return f
    end
    f = Func(-1, String(name), type, params, results, ValType[],
             Inst[], (String(mod), String(name)))
    push!(m.funcs, f)
    return f
end

"Add a global with the initializer `init` (constant instructions)."
function add_global!(m::WModule, name::AbstractString, type::ValType, mutable::Bool,
                     init::Vector{Inst})
    g = Global(-1, String(name), type, mutable, init)
    push!(m.globals, g)
    g.idx = length(m.globals) - 1   # globals are never imported, so indices are final
    return g
end

"Add a tag whose payload has the types `params`."
function add_tag!(m::WModule, params::Vector{ValType})
    t = Tag(length(m.tags), functype!(m, params, ValType[]))
    push!(m.tags, t)
    return t
end

"""
    add_memory!(m, min; max=nothing) -> LinearMemory

Add the module's linear memory, of `min` pages of 64 KiB (growing to at most `max`). A
module has one memory at most; the load and store instructions address it.
"""
function add_memory!(m::WModule, min::Integer; max::Union{Nothing,Integer}=nothing)
    m.memory === nothing || throw(ArgumentError("the module has a memory already"))
    return m.memory = LinearMemory(min, max)
end

"Add a passive data segment, returning its index."
function add_data!(m::WModule, bytes::Vector{UInt8})
    push!(m.datas, bytes)
    return length(m.datas) - 1
end

"Export `item` (a `Func`, `Global`, `Tag` or the `LinearMemory`) as `name`."
add_export!(m::WModule, name::AbstractString, item) = push!(m.exports, (String(name), item))

"Declare `f` as referenced by `ref.func`."
function declare!(m::WModule, f::Func)
    f in m.declared_set && return
    push!(m.declared_set, f)
    push!(m.declared, f)
end

"Add a local of type `t` to the function `f`, returning its index."
function add_local!(f::Func, t::ValType)
    push!(f.locals, t)
    return length(f.params) + length(f.locals) - 1
end

"The type of the local `i` of `f`."
local_type(f::Func, i::Int) = i < length(f.params) ? f.params[i+1] : f.locals[i-length(f.params)+1]

# assign the function indices: imports first, as the index space requires
function assign_indices!(m::WModule)
    i = 0
    for f in m.funcs
        f.imported === nothing && continue
        f.idx = i
        i += 1
    end
    for f in m.funcs
        f.imported === nothing || continue
        f.idx = i
        i += 1
    end
    return m
end
