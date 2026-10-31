# The order of a module's type definitions in its binary and their recursion groups.
#
# Function types made by `functype!` are structural: one per signature. Those that reference no
# defined type (their parameters and results are numbers or abstract references) are encoded
# first, each a recursion group of its own, so that they equal the same signature defined
# anywhere else: in particular the types of host functions, which an import must match. The
# other types, function types added with `add_type!` among them, form one recursion group, in
# definition order, and stay distinct from each other (nominal).

"""
    TypeOrder(m::WModule)

The binary order of the types of `m`: `singles` (definition indices encoded as recursion
groups of their own), then `group` (one recursion group), and `index`, the binary index of
each type by its definition index (1-based position, 0-based values).
"""
struct TypeOrder
    singles::Vector{Int}
    group::Vector{Int}
    index::Vector{Int}
end

standalone_valtype(t::ValType) = t isa NumType || t.heap isa Symbol

function TypeOrder(m::WModule)
    structural = Set{Int}(t.idx for t in values(m.functypes))
    supers = Set{Int}(t.super.idx for t in m.types if t.super !== nothing)
    singles, group = Int[], Int[]
    for (k, t) in enumerate(m.types)
        i = k - 1
        c = t.comp
        alone = i in structural && c isa FuncType && t.final && t.super === nothing && !(i in supers) &&
                all(standalone_valtype, c.params) && all(standalone_valtype, c.results)
        push!(alone ? singles : group, i)
    end
    index = Vector{Int}(undef, length(m.types))
    for (k, i) in enumerate(Iterators.flatten((singles, group)))
        index[i+1] = k - 1
    end
    return TypeOrder(singles, group, index)
end

"The binary index of the type `t`."
type_index(ord::TypeOrder, t::TypeRef) = ord.index[t.idx+1]
