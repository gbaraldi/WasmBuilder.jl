# The text format of a module, for reading generated code (not meant to round-trip
# exactly: names are informative, indices are those of the binary).

function show_heap(io::IO, h::HeapType)
    h isa Symbol ? print(io, h) : print(io, h.idx)
end

show_valtype(io::IO, t::NumType) = show(io, t)
function show_valtype(io::IO, t::RefType)
    print(io, "(ref ", t.nullable ? "null " : "")
    show_heap(io, t.heap)
    print(io, ")")
end
show_storage(io::IO, t::PackedType) = print(io, t === I8 ? "i8" : "i16")
show_storage(io::IO, t::ValType) = show_valtype(io, t)

function show_field(io::IO, f::FieldType)
    f.mutable && print(io, "(mut ")
    show_storage(io, f.storage)
    f.mutable && print(io, ")")
end

function show_comp(io::IO, t::FuncType)
    print(io, "(func")
    isempty(t.params) || (print(io, " (param"); foreach(p -> (print(io, " "); show_valtype(io, p)), t.params); print(io, ")"))
    isempty(t.results) || (print(io, " (result"); foreach(p -> (print(io, " "); show_valtype(io, p)), t.results); print(io, ")"))
    print(io, ")")
end
function show_comp(io::IO, t::StructType)
    print(io, "(struct")
    for f in t.fields
        print(io, " (field ")
        show_field(io, f)
        print(io, ")")
    end
    print(io, ")")
end
function show_comp(io::IO, t::ArrayType)
    print(io, "(array ")
    show_field(io, t.elem)
    print(io, ")")
end

function show_types(io::IO, ts)
    print(io, "(result")
    foreach(t -> (print(io, " "); show_valtype(io, t)), ts)
    print(io, ")")
end

# an immediate of the kind `kind`, preceded by a space (block types are written as in the
# text format, other indices as numbers)
function show_imm(io::IO, kind::Symbol, @nospecialize(x))
    (x === :empty || x === nothing) && return
    print(io, " ")
    if kind === :bt
        x isa TypeRef ? print(io, "(type ", x.idx, ")") : show_types(io, (x,))
    elseif kind === :valtypes
        show_types(io, x)
    elseif kind === :ref || kind === :refnull
        show_valtype(io, RefType(x, kind === :refnull))
    elseif kind === :memidx
        print(io, x)
    elseif kind === :labels
        join(io, x, " ")
    elseif kind === :catches
        join(io, map(x) do (k, tag, label)
            name = ("catch", "catch_ref", "catch_all", "catch_all_ref")[k+1]
            k < 2 ? "($name \$tag$(tag.idx) $label)" : "($name $label)"
        end, " ")
    elseif x isa Func || x isa Global
        print(io, "\$", x.name)
    elseif x isa Tag
        print(io, "\$tag", x.idx)
    elseif x isa TypeRef
        print(io, x.idx)
    elseif x isa RefType || x isa NumType
        show_valtype(io, x)
    else
        print(io, x)
    end
end

function show_inst(io::IO, i::Inst)
    info = get(INSTRUCTIONS, i.op, nothing)
    if info === nothing
        print(io, i.op)
        foreach(x -> show_imm(io, :unknown, x), i.imm)
    elseif i.op in (:br_on_cast, :br_on_cast_fail)
        flags, label, h1, h2 = i.imm
        print(io, info.text, " ", label, " ")
        show_valtype(io, RefType(h1, flags & 1 != 0))
        print(io, " ")
        show_valtype(io, RefType(h2, flags & 2 != 0))
    elseif haskey(MEMORY_ACCESSES, i.op)
        # memarg: the offset, then the alignment, each written when not the default
        align, offset = i.imm
        print(io, info.text)
        offset == 0 || print(io, " offset=", offset)
        align == MEMORY_ACCESSES[i.op] || print(io, " align=", 1 << align)
    else
        print(io, info.text)
        foreach((k, x) -> show_imm(io, k, x), info.imms, i.imm)
    end
end

function show_insts(io::IO, insts::Vector{Inst}, indent::Int)
    for i in insts
        i.op in (:end, :else) && (indent -= 1)
        print(io, "  "^indent)
        show_inst(io, i)
        println(io)
        i.op in (:block, :loop, :if, :else, :try_table) && (indent += 1)
    end
end

"""
    print_wat(io, m::WModule)

Print the module in (approximately) the text format.
"""
function print_wat(io::IO, m::WModule)
    assign_indices!(m)
    println(io, "(module")
    println(io, "  (rec")
    for (i, t) in enumerate(m.types)
        print(io, "    (type ", i - 1, " (sub ", t.final ? "final " : "")
        t.super === nothing || print(io, t.super.idx, " ")
        show_comp(io, t.comp)
        println(io, "))")
    end
    println(io, "  )")
    mem = m.memory
    mem === nothing || println(io, "  (memory ", mem.min, mem.max === nothing ? "" : " $(mem.max)", ")")
    for g in m.globals
        print(io, "  (global \$", g.name, " ", g.mutable ? "(mut " : "")
        show_valtype(io, g.type)
        println(io, g.mutable ? ")" : "")
        show_insts(io, g.init, 2)
        println(io, "  )")
    end
    for f in sort(m.funcs; by=f -> f.idx)
        print(io, "  (func \$", f.name, " (type ", f.type.idx, ")")
        f.imported === nothing || print(io, " (import \"", f.imported[1], "\" \"", f.imported[2], "\")")
        for (i, p) in enumerate(f.params)
            print(io, " (param ", i - 1, " ")
            show_valtype(io, p)
            print(io, ")")
        end
        for r in f.results
            print(io, " (result ")
            show_valtype(io, r)
            print(io, ")")
        end
        println(io)
        for (i, l) in enumerate(f.locals)
            print(io, "    (local ", length(f.params) + i - 1, " ")
            show_valtype(io, l)
            println(io, ")")
        end
        show_insts(io, f.body, 2)
        println(io, "  )")
    end
    for (name, item) in m.exports
        println(io, "  (export \"", name, "\" ", item isa Func ? "(func \$" : item isa Global ? "(global \$" :
                item isa LinearMemory ? "(memory " : "(tag ", item isa Tag ? item.idx : item isa LinearMemory ? 0 : item.name, "))")
    end
    m.start === nothing || println(io, "  (start \$", m.start.name, ")")
    println(io, ")")
end

Base.show(io::IO, ::MIME"text/plain", m::WModule) = print_wat(io, m)
