# The binary encoding of a module.

function leb_u(io::IO, x::Integer)
    x = UInt64(x)
    while true
        b = UInt8(x & 0x7f)
        x >>= 7
        if x == 0
            write(io, b)
            return
        end
        write(io, b | 0x80)
    end
end

function leb_s(io::IO, x::Integer)
    x = Int64(x)
    while true
        b = UInt8(x & 0x7f)
        x >>= 7
        if (x == 0 && b & 0x40 == 0) || (x == -1 && b & 0x40 != 0)
            write(io, b)
            return
        end
        write(io, b | 0x80)
    end
end

function leb_s128(io::IO, x::Int128)
    while true
        b = UInt8(x & 0x7f)
        x >>= 7
        if (x == 0 && b & 0x40 == 0) || (x == -1 && b & 0x40 != 0)
            write(io, b)
            return
        end
        write(io, b | 0x80)
    end
end

function write_name(io::IO, s::AbstractString)
    leb_u(io, ncodeunits(s))
    write(io, codeunits(s))
end

function write_vec(f, io::IO, xs)
    leb_u(io, length(xs))
    foreach(x -> f(io, x), xs)
end

write_heap(io::IO, h::Symbol) = write(io, ABSTRACT_HEAPTYPES[h])
write_heap(io::IO, h::TypeRef) = leb_s(io, h.idx)   # s33

write_valtype(io::IO, t::NumType) = write(io, UInt8(t))
function write_valtype(io::IO, t::RefType)
    write(io, t.nullable ? 0x63 : 0x64)
    write_heap(io, t.heap)
end
write_storage(io::IO, t::PackedType) = write(io, UInt8(t))
write_storage(io::IO, t::ValType) = write_valtype(io, t)

function write_field(io::IO, f::FieldType)
    write_storage(io, f.storage)
    write(io, f.mutable ? 0x01 : 0x00)
end

function write_comp(io::IO, t::FuncType)
    write(io, 0x60)
    write_vec(write_valtype, io, t.params)
    write_vec(write_valtype, io, t.results)
end
function write_comp(io::IO, t::StructType)
    write(io, 0x5f)
    write_vec(write_field, io, t.fields)
end
function write_comp(io::IO, t::ArrayType)
    write(io, 0x5e)
    write_field(io, t.elem)
end

function write_subtype(io::IO, t::SubType)
    write(io, t.final ? 0x4f : 0x50)
    if t.super === nothing
        leb_u(io, 0)
    else
        leb_u(io, 1)
        leb_u(io, t.super.idx)
    end
    write_comp(io, t.comp)
end

## instructions

# the bits of an `iN.const` immediate, given in the signed or the unsigned range of N bits
function const_bits(::Type{T}, x::Integer) where {T<:Union{Int32,Int64}}
    U = unsigned(T)
    typemin(T) <= x <= typemax(U) || throw(ArgumentError("$x does not fit in $(sizeof(T) * 8) bits"))
    return x < 0 ? T(x) : reinterpret(T, U(x))
end

function write_blocktype(io::IO, bt)
    if bt === nothing || bt === :empty
        write(io, 0x40)
    elseif bt isa ValType
        write_valtype(io, bt)
    elseif bt isa TypeRef
        leb_s(io, bt.idx)
    else
        error("invalid block type $bt")
    end
end

function write_imm(io::IO, kind::Symbol, @nospecialize(x))
    if kind === :u32 || kind === :align || kind === :offset || kind === :memidx
        leb_u(io, x)
    elseif kind === :i32
        leb_s(io, const_bits(Int32, x))
    elseif kind === :i64
        leb_s(io, const_bits(Int64, x))
    elseif kind === :f32
        write(io, htol(reinterpret(UInt32, Float32(x))))
    elseif kind === :f64
        write(io, htol(reinterpret(UInt64, Float64(x))))
    elseif kind === :bt
        write_blocktype(io, x)
    elseif kind === :type
        leb_u(io, (x::TypeRef).idx)
    elseif kind === :heap || kind === :ref || kind === :refnull
        write_heap(io, x)
    elseif kind === :func
        leb_u(io, (x::Func).idx)
    elseif kind === :global
        leb_u(io, (x::Global).idx)
    elseif kind === :tag
        leb_u(io, (x::Tag).idx)
    elseif kind === :labels
        write_vec(leb_u, io, x)
    elseif kind === :valtypes
        write_vec(write_valtype, io, x)
    elseif kind === :castflags
        write(io, UInt8(x))
    elseif kind === :catches
        # (kind, tag or nothing, label): 0 catch, 1 catch_ref, 2 catch_all, 3 catch_all_ref
        leb_u(io, length(x))
        for (k, tag, label) in x
            write(io, UInt8(k))
            k < 2 && leb_u(io, (tag::Tag).idx)
            leb_u(io, label)
        end
    else
        error("unknown immediate kind $kind")
    end
end

function write_inst(io::IO, inst::Inst)
    info = get(INSTRUCTIONS, inst.op, nothing)
    info === nothing && error("unknown instruction $(inst.op)")
    kinds = info.imms
    write(io, info.code)
    length(kinds) == length(inst.imm) ||
        error("instruction $(inst.op) takes $(length(kinds)) immediates, got $(length(inst.imm))")
    for (k, x) in zip(kinds, inst.imm)
        write_imm(io, k, x)
    end
end

function write_expr(io::IO, insts::Vector{Inst})
    foreach(i -> write_inst(io, i), insts)
    write(io, 0x0b)
end

## sections

function write_section(f, io::IO, id::Integer)
    buf = IOBuffer()
    f(buf)
    bytes = take!(buf)
    write(io, UInt8(id))
    leb_u(io, length(bytes))
    write(io, bytes)
end

function write_locals(io::IO, locals::Vector{ValType})
    # runs of equal types
    runs = Tuple{Int,ValType}[]
    for t in locals
        if !isempty(runs) && runs[end][2] == t
            runs[end] = (runs[end][1] + 1, t)
        else
            push!(runs, (1, t))
        end
    end
    leb_u(io, length(runs))
    for (n, t) in runs
        leb_u(io, n)
        write_valtype(io, t)
    end
end

function write_limits(io::IO, mem::LinearMemory)
    write(io, mem.max === nothing ? 0x00 : 0x01)
    leb_u(io, mem.min)
    mem.max === nothing || leb_u(io, mem.max)
end

"""
    to_bytes(m::WModule; verify=true) -> Vector{UInt8}

The binary encoding of the module, checked by [`verify`](@ref) first unless `verify` is
false.
"""
function to_bytes(m::WModule; verify::Bool=true)
    verify && WasmBuilder.verify(m)
    assign_indices!(m)
    io = IOBuffer()
    write(io, UInt8[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00])
    imports = filter(f -> f.imported !== nothing, m.funcs)
    defined = filter(f -> f.imported === nothing, m.funcs)

    # types: one recursion group
    write_section(io, 1) do s
        leb_u(s, 1)
        write(s, 0x4e)
        write_vec(write_subtype, s, m.types)
    end
    isempty(imports) || write_section(io, 2) do s
        write_vec(s, imports) do s, f
            write_name(s, f.imported[1])
            write_name(s, f.imported[2])
            write(s, 0x00)
            leb_u(s, f.type.idx)
        end
    end
    write_section(io, 3) do s
        write_vec((s, f) -> leb_u(s, f.type.idx), s, defined)
    end
    m.memory === nothing || write_section(io, 5) do s
        leb_u(s, 1)
        write_limits(s, m.memory)
    end
    isempty(m.tags) || write_section(io, 13) do s
        write_vec(s, m.tags) do s, t
            write(s, 0x00)
            leb_u(s, t.type.idx)
        end
    end
    isempty(m.globals) || write_section(io, 6) do s
        write_vec(s, m.globals) do s, g
            write_valtype(s, g.type)
            write(s, g.mutable ? 0x01 : 0x00)
            write_expr(s, g.init)
        end
    end
    isempty(m.exports) || write_section(io, 7) do s
        write_vec(s, m.exports) do s, (name, item)
            write_name(s, name)
            if item isa Func
                write(s, 0x00); leb_u(s, item.idx)
            elseif item isa Global
                write(s, 0x03); leb_u(s, item.idx)
            elseif item isa Tag
                write(s, 0x04); leb_u(s, item.idx)
            elseif item isa LinearMemory
                write(s, 0x02); leb_u(s, 0)
            else
                error("cannot export $item")
            end
        end
    end
    m.start === nothing || write_section(io, 8) do s
        leb_u(s, m.start.idx)
    end
    isempty(m.declared) || write_section(io, 9) do s
        # one declarative segment of function indices
        leb_u(s, 1)
        leb_u(s, 3)
        write(s, 0x00)
        write_vec((s, f) -> leb_u(s, f.idx), s, m.declared)
    end
    isempty(m.datas) || write_section(io, 12) do s
        leb_u(s, length(m.datas))
    end
    write_section(io, 10) do s
        write_vec(s, defined) do s, f
            body = IOBuffer()
            write_locals(body, f.locals)
            write_expr(body, f.body)
            bytes = take!(body)
            leb_u(s, length(bytes))
            write(s, bytes)
        end
    end
    isempty(m.datas) || write_section(io, 11) do s
        write_vec(s, m.datas) do s, d
            leb_u(s, 1)    # passive
            leb_u(s, length(d))
            write(s, d)
        end
    end
    # names, for debugging (function names)
    write_section(io, 0) do s
        write_name(s, "name")
        sub = IOBuffer()
        all = sort(m.funcs; by=f -> f.idx)
        write_vec(sub, all) do sub, f
            leb_u(sub, f.idx)
            write_name(sub, f.name)
        end
        bytes = take!(sub)
        write(s, 0x01)
        leb_u(s, length(bytes))
        write(s, bytes)
    end
    return take!(io)
end
