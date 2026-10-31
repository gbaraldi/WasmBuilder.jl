# The text format of a module, for reading generated code (not meant to round-trip
# exactly: names are informative, indices are those of the binary).

function show_heap(io::IO, ord::TypeOrder, h::HeapType)
    h isa Symbol ? print(io, h) : print(io, type_index(ord, h))
end

show_valtype(io::IO, ord::TypeOrder, t::NumType) = show(io, t)
function show_valtype(io::IO, ord::TypeOrder, t::RefType)
    print(io, "(ref ", t.nullable ? "null " : "")
    show_heap(io, ord, t.heap)
    print(io, ")")
end
show_storage(io::IO, ord::TypeOrder, t::PackedType) = print(io, t === I8 ? "i8" : "i16")
show_storage(io::IO, ord::TypeOrder, t::ValType) = show_valtype(io, ord, t)

function show_field(io::IO, ord::TypeOrder, f::FieldType)
    f.mutable && print(io, "(mut ")
    show_storage(io, ord, f.storage)
    f.mutable && print(io, ")")
end

function show_comp(io::IO, ord::TypeOrder, t::FuncType)
    print(io, "(func")
    isempty(t.params) || (print(io, " (param"); foreach(p -> (print(io, " "); show_valtype(io, ord, p)), t.params); print(io, ")"))
    isempty(t.results) || (print(io, " (result"); foreach(p -> (print(io, " "); show_valtype(io, ord, p)), t.results); print(io, ")"))
    print(io, ")")
end
function show_comp(io::IO, ord::TypeOrder, t::StructType)
    print(io, "(struct")
    for f in t.fields
        print(io, " (field ")
        show_field(io, ord, f)
        print(io, ")")
    end
    print(io, ")")
end
function show_comp(io::IO, ord::TypeOrder, t::ArrayType)
    print(io, "(array ")
    show_field(io, ord, t.elem)
    print(io, ")")
end

function show_types(io::IO, ord::TypeOrder, ts)
    print(io, "(result")
    foreach(t -> (print(io, " "); show_valtype(io, ord, t)), ts)
    print(io, ")")
end

# an immediate of the kind `kind`, preceded by a space (block types are written as in the
# text format, other indices as numbers)
function show_imm(io::IO, ord::TypeOrder, kind::Symbol, @nospecialize(x))
    (x === :empty || x === nothing) && return
    print(io, " ")
    if kind === :bt
        x isa TypeRef ? print(io, "(type ", type_index(ord, x), ")") : show_types(io, ord, (x,))
    elseif kind === :valtypes
        show_types(io, ord, x)
    elseif kind === :ref || kind === :refnull
        show_valtype(io, ord, RefType(x, kind === :refnull))
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
        print(io, type_index(ord, x))
    elseif x isa RefType || x isa NumType
        show_valtype(io, ord, x)
    else
        print(io, x)
    end
end

function show_inst(io::IO, ord::TypeOrder, i::Inst)
    info = get(INSTRUCTIONS, i.op, nothing)
    if info === nothing
        print(io, i.op)
        foreach(x -> show_imm(io, ord, :unknown, x), i.imm)
    elseif i.op in (:br_on_cast, :br_on_cast_fail)
        flags, label, h1, h2 = i.imm
        print(io, info.text, " ", label, " ")
        show_valtype(io, ord, RefType(h1, flags & 1 != 0))
        print(io, " ")
        show_valtype(io, ord, RefType(h2, flags & 2 != 0))
    elseif haskey(MEMORY_ACCESSES, i.op)
        # memarg: the offset, then the alignment, each written when not the default
        align, offset = i.imm
        print(io, info.text)
        offset == 0 || print(io, " offset=", offset)
        align == MEMORY_ACCESSES[i.op] || print(io, " align=", 1 << align)
    else
        print(io, info.text)
        foreach((k, x) -> show_imm(io, ord, k, x), info.imms, i.imm)
    end
end

function show_insts(io::IO, ord::TypeOrder, insts::Vector{Inst}, indent::Int)
    for i in insts
        i.op in (:end, :else) && (indent -= 1)
        print(io, "  "^indent)
        show_inst(io, ord, i)
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
    ord = TypeOrder(m)
    println(io, "(module")
    function show_type(i, indent)
        t = m.types[i+1]
        print(io, indent, "(type ", type_index(ord, TypeRef(i)), " (sub ", t.final ? "final " : "")
        t.super === nothing || print(io, type_index(ord, t.super), " ")
        show_comp(io, ord, t.comp)
        println(io, "))")
    end
    foreach(i -> show_type(i, "  "), ord.singles)
    if !isempty(ord.group)
        println(io, "  (rec")
        foreach(i -> show_type(i, "    "), ord.group)
        println(io, "  )")
    end
    mem = m.memory
    mem === nothing || println(io, "  (memory ", mem.min, mem.max === nothing ? "" : " $(mem.max)", ")")
    for g in m.globals
        print(io, "  (global \$", g.name, " ", g.mutable ? "(mut " : "")
        show_valtype(io, ord, g.type)
        println(io, g.mutable ? ")" : "")
        show_insts(io, ord, g.init, 2)
        println(io, "  )")
    end
    for f in sort(m.funcs; by=f -> f.idx)
        print(io, "  (func \$", f.name, " (type ", type_index(ord, f.type), ")")
        f.imported === nothing || print(io, " (import \"", f.imported[1], "\" \"", f.imported[2], "\")")
        for (i, p) in enumerate(f.params)
            print(io, " (param ", i - 1, " ")
            show_valtype(io, ord, p)
            print(io, ")")
        end
        for r in f.results
            print(io, " (result ")
            show_valtype(io, ord, r)
            print(io, ")")
        end
        println(io)
        for (i, l) in enumerate(f.locals)
            print(io, "    (local ", length(f.params) + i - 1, " ")
            show_valtype(io, ord, l)
            println(io, ")")
        end
        show_insts(io, ord, f.body, 2)
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
