# The validity of a module beyond its function bodies (which the builder validates):
# type definitions, global initializers, exports, tags, the memory and the start function.

merr(item::AbstractString, op::Symbol, msg) =
    throw(WasmValidationError(item, 0, op, msg, Any[]))

# the instructions allowed in constant expressions (with extended-const arithmetic)
const CONST_OPS = Set([:i32_const, :i64_const, :f32_const, :f64_const, :ref_null,
                       :ref_func, :ref_i31, :struct_new, :struct_new_default, :array_new,
                       :array_new_default, :array_new_fixed, :any_convert_extern,
                       :extern_convert_any, :global_get, :i32_add, :i32_sub, :i32_mul,
                       :i64_add, :i64_sub, :i64_mul])

"""
    verify(m::WModule)

Check the validity of the module beyond its function bodies (validated by the
[`Builder`](@ref) as they are emitted): type definitions and their declared supertypes,
global initializers (constant expressions of the global's type, reading only earlier
immutable globals), tags, the memory's limits, exports (unique names) and the start
function (of type `[] -> []`). Throws a [`WasmValidationError`](@ref); [`to_bytes`](@ref) calls it.
"""
function verify(m::WModule)
    for (i, t) in enumerate(m.types)
        verify_type_refs(m, "type $(i-1)", t)
    end
    for (i, t) in enumerate(m.types)
        t.super === nothing && continue
        item, s = "type $(i-1)", t.super
        s.idx < i - 1 || merr(item, :type, "supertype $s must be defined before the type")
        st = typedef(m, s)
        st.final && merr(item, :type, "supertype $s is final")
        comp_subtype(m, t.comp, st.comp) || merr(item, :type, "does not match its supertype $s")
    end
    funcs, globals, tags = Set(m.funcs), Set(m.globals), Set(m.tags)
    for (i, t) in enumerate(m.tags)
        valid_heap(m, t.type) && typedef(m, t.type).comp isa FuncType &&
            isempty(typedef(m, t.type).comp.results) ||
            merr("tag $(i-1)", :tag, "the type of a tag is a function type without results")
    end
    for (i, g) in enumerate(m.globals)
        item = "global $(g.name)"
        g.idx == i - 1 || merr(item, :global, "index $(g.idx) at position $(i-1)")
        valid_valtype(m, g.type) || merr(item, :global, "invalid type $(g.type)")
        verify_const(m, item, g.init, g.type, i - 1)
    end
    mem = m.memory
    if mem !== nothing
        0 <= mem.min <= 65536 && (mem.max === nothing || mem.min <= mem.max <= 65536) ||
            merr("memory", :memory, "invalid limits $(mem.min)..$(something(mem.max, "")) (pages of 64 KiB, at most 65536)")
    end
    names = Set{String}()
    for (name, item) in m.exports
        where = "export \"$name\""
        name in names && merr(where, :export, "duplicate export name")
        push!(names, name)
        item isa Func && item in funcs || item isa Global && item in globals ||
            item isa Tag && item in tags || item isa LinearMemory && item === mem ||
            merr(where, :export, "not a function, global, tag or the memory of the module")
    end
    s = m.start
    if s !== nothing
        s isa Func && s in funcs || merr("start function", :start, "not a function of the module")
        isempty(s.params) && isempty(s.results) ||
            merr("start function $(s.name)", :start, "the start function must have type [] -> []")
    end
    return nothing
end

function verify_type_refs(m::WModule, item, t::SubType)
    t.super === nothing || valid_heap(m, t.super) ||
        merr(item, :type, "undefined supertype $(t.super)")
    c = t.comp
    ts = c isa FuncType ? [c.params; c.results] :
         c isa StructType ? [f.storage for f in c.fields] : [c.elem.storage]
    for x in ts
        valid_storage(m, x) || merr(item, :type, "invalid type $x")
    end
end

# a constant expression producing a value of type `t`, reading the first `nglobals` globals
function verify_const(m::WModule, item, insts::Vector{Inst}, t::ValType, nglobals::Int)
    f = Func(-1, item, TypeRef(-1), ValType[], ValType[t], ValType[], Inst[], nothing)
    b = Builder(m, f)
    b.constexpr = true
    try
        for inst in insts
            op = inst.op
            op in CONST_OPS || verr(b, op, "not a constant instruction")
            if op === :global_get && !isempty(inst.imm)
                g = inst.imm[1]
                g isa Global && 0 <= g.idx < nglobals && m.globals[g.idx+1] === g ||
                    verr(b, op, "only earlier globals can be read")
                g.mutable && verr(b, op, "global $(g.name) is mutable")
            end
            typecheck!(b, op, inst.imm)
            push!(f.body, inst)
        end
        pop_t!(b, :end, t)
        isempty(b.stack) || verr(b, :end, "$(length(b.stack)) values left")
    catch e
        e isa WasmValidationError || rethrow()
        merr(item, e.op, "initializer instruction $(e.pos) ($(e.op)): $(e.msg)")
    end
end
