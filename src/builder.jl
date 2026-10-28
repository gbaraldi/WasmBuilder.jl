# A builder of function bodies that validates every instruction as it is emitted, against
# the operand stack and the control frames (the validation algorithm of the spec's
# appendix), so that a code generator's mistakes are reported where they are made.

"""
    WasmValidationError

An instruction that does not validate, with the function, the position of the
instruction and the reason. For module-level errors (from [`verify`](@ref)), `func`
names the item and `pos` is 0.
"""
struct WasmValidationError <: Exception
    func::String
    pos::Int
    op::Symbol
    msg::String
    stack::Vector{Any}
end

function Base.showerror(io::IO, e::WasmValidationError)
    if e.pos == 0
        print(io, "WasmValidationError in ", e.func, ": ", e.msg)
        return
    end
    print(io, "WasmValidationError in function ", e.func, " at instruction ", e.pos, " (",
          e.op, "): ", e.msg)
    print(io, "\n  operand stack: [", join(map(t -> t === nothing ? "⊥" : string(t), e.stack), ", "), "]")
end

struct Frame
    kind::Symbol            # :func, :block, :loop, :if, :else, :try_table
    params::Vector{ValType}
    results::Vector{ValType}
    height::Int             # of the operand stack
    init_height::Int        # of the initialized locals (`Builder.inits`)
    unreachable::Bool
end

"""
    Builder(m::WModule, f::Func)

A builder appending to the body of the function `f` of the module `m`. Instructions are
emitted with [`emit!`](@ref) (and the control instructions with their own functions),
and validated as they are. [`finish!`](@ref) ends the body.
"""
mutable struct Builder
    mod::WModule
    func::Func
    stack::Vector{Union{Nothing,ValType}}
    frames::Vector{Frame}
    "The non-defaultable locals set so far, in order (forgotten at the end of their block)."
    inits::Vector{Int}
    initialized::BitSet
    "Whether the code is a constant expression (a global's initializer)."
    constexpr::Bool
end

function Builder(m::WModule, f::Func)
    b = Builder(m, f, Union{Nothing,ValType}[], Frame[], Int[], BitSet(), false)
    push!(b.frames, Frame(:func, ValType[], f.results, 0, 0, false))
    return b
end

const VALIDATE = Ref(true)

verr(b::Builder, op::Symbol, msg) =
    throw(WasmValidationError(b.func.name, length(b.func.body) + 1, op, msg, copy(b.stack)))

top_frame(b::Builder) = b.frames[end]

function push_t!(b::Builder, t::Union{Nothing,ValType})
    push!(b.stack, t)
end
push_ts!(b::Builder, ts) = foreach(t -> push_t!(b, t), ts)

# the type of the operand, `nothing` if unknown (in unreachable code)
function pop_any!(b::Builder, op::Symbol)
    f = top_frame(b)
    if length(b.stack) == f.height
        f.unreachable && return nothing
        verr(b, op, "operand stack underflow")
    end
    return pop!(b.stack)
end

function pop_t!(b::Builder, op::Symbol, expected::ValType)
    actual = pop_any!(b, op)
    actual === nothing || subtype(b.mod, actual, expected) ||
        verr(b, op, "expected $expected, got $actual")
    return actual
end

# the types of the operands popped (`nothing` for unknown ones)
function pop_ts!(b::Builder, op::Symbol, ts)
    vals = Vector{Union{Nothing,ValType}}(undef, length(ts))
    for i in reverse(eachindex(ts))
        vals[i] = pop_t!(b, op, ts[i])
    end
    return vals
end

# the type of an unknown reference operand: a reference to the bottom heap type
const BOT_REF = RefType(:bot, false)

function pop_ref!(b::Builder, op::Symbol)
    t = pop_any!(b, op)
    t === nothing && return BOT_REF
    t isa RefType || verr(b, op, "expected a reference, got $t")
    return t
end

function set_unreachable!(b::Builder)
    f = b.frames[end]
    resize!(b.stack, f.height)
    b.frames[end] = Frame(f.kind, f.params, f.results, f.height, f.init_height, true)
end

"Whether the code being emitted is unreachable (after a branch, `return`, ...)."
is_unreachable(b::Builder) = b.frames[end].unreachable

"The types of the operand stack (`nothing` for unknown ones in unreachable code)."
stack(b::Builder) = b.stack

append_inst!(b::Builder, op::Symbol, imm...) = push!(b.func.body, Inst(op, imm))

## locals: non-defaultable ones must be set before they are read

function check_local(b::Builder, op::Symbol, i)
    i isa Integer && 0 <= i < length(b.func.params) + length(b.func.locals) ||
        verr(b, op, "no local $i")
end

needs_init(b::Builder, i) = i >= length(b.func.params) && !defaultable(local_type(b.func, i))

function set_local!(b::Builder, i)
    if needs_init(b, i) && !(i in b.initialized)
        push!(b.inits, i)
        push!(b.initialized, i)
    end
end

function reset_locals!(b::Builder, height::Int)
    while length(b.inits) > height
        delete!(b.initialized, pop!(b.inits))
    end
end

## block types

"""
    blocktype(b, params, results)

The block type of a block taking `params` and producing `results`: empty, a value type,
or a function type of the module.
"""
function blocktype(b::Builder, params::Vector{ValType}, results::Vector{ValType})
    isempty(params) && isempty(results) && return :empty
    isempty(params) && length(results) == 1 && return results[1]
    return functype!(b.mod, params, results)
end

function blocktype_sig(b::Builder, bt, op::Symbol=:block)
    (bt === :empty || bt === nothing) && return ValType[], ValType[]
    if bt isa ValType
        valid_valtype(b.mod, bt) || verr(b, op, "invalid block type $bt")
        return ValType[], ValType[bt]
    end
    bt isa TypeRef && valid_heap(b.mod, bt) && typedef(b.mod, bt).comp isa FuncType ||
        verr(b, op, "invalid block type $bt")
    ft = typedef(b.mod, bt).comp::FuncType
    return ft.params, ft.results
end

label_types(f::Frame) = f.kind === :loop ? f.params : f.results

function label_frame(b::Builder, op::Symbol, depth::Integer)
    0 <= depth < length(b.frames) || verr(b, op, "invalid branch depth $depth")
    return b.frames[end-depth]
end

## control instructions

function push_frame!(b::Builder, kind::Symbol, params, results)
    push!(b.frames, Frame(kind, params, results, length(b.stack), length(b.inits), false))
    push_ts!(b, params)
end

function pop_frame!(b::Builder)
    f = pop!(b.frames)
    resize!(b.stack, f.height)
    reset_locals!(b, f.init_height)
    return f
end

"Begin a `block` with the block type `bt`."
function block!(b::Builder, bt=:empty)
    params, results = blocktype_sig(b, bt, :block)
    VALIDATE[] && pop_ts!(b, :block, params)
    append_inst!(b, :block, bt)
    push_frame!(b, :block, params, results)
end

"Begin a `loop` with the block type `bt`."
function loop!(b::Builder, bt=:empty)
    params, results = blocktype_sig(b, bt, :loop)
    VALIDATE[] && pop_ts!(b, :loop, params)
    append_inst!(b, :loop, bt)
    push_frame!(b, :loop, params, results)
end

"Begin an `if` (on an `i32` condition) with the block type `bt`."
function if!(b::Builder, bt=:empty)
    params, results = blocktype_sig(b, bt, :if)
    if VALIDATE[]
        pop_t!(b, :if, I32)
        pop_ts!(b, :if, params)
    end
    append_inst!(b, :if, bt)
    push_frame!(b, :if, params, results)
end

"Begin the `else` arm of the current `if`."
function else!(b::Builder)
    f = top_frame(b)
    f.kind === :if || verr(b, :else, "else outside of an if")
    end_check!(b, :else, f)
    pop_frame!(b)
    append_inst!(b, :else)
    push_frame!(b, :else, f.params, f.results)
end

function end_check!(b::Builder, op::Symbol, f::Frame)
    VALIDATE[] || return
    pop_ts!(b, op, f.results)
    length(b.stack) == f.height ||
        verr(b, op, "$(length(b.stack) - f.height) values left on the stack at the end of a $(f.kind)")
end

"End the current block, loop, if or try_table (the function body is ended by `finish!`)."
function end!(b::Builder)
    length(b.frames) > 1 ||
        verr(b, :end, isempty(b.frames) ? "the function is finished" :
                      "end! of the function body: use finish!")
    f = top_frame(b)
    # an if without else: its implicit empty else arm takes the params to the results
    f.kind === :if && !subtypes(b.mod, f.params, f.results) &&
        verr(b, :end, "an if without else must have params matching its results")
    end_check!(b, :end, f)
    pop_frame!(b)
    append_inst!(b, :end)
    push_ts!(b, f.results)
end

"End the function body (the final `end` is implicit in the binary format)."
function finish!(b::Builder)
    length(b.frames) == 1 || verr(b, :end, "$(length(b.frames) - 1) unclosed blocks at the end of the function")
    end_check!(b, :end, top_frame(b))
    pop!(b.frames)
    return b.func
end

"Branch to the label `depth` (0 is the innermost block)."
function br!(b::Builder, depth::Integer)
    f = label_frame(b, :br, depth)
    VALIDATE[] && pop_ts!(b, :br, label_types(f))
    append_inst!(b, :br, depth)
    set_unreachable!(b)
end

"Branch to the label `depth` if the `i32` on the stack is nonzero."
function br_if!(b::Builder, depth::Integer)
    f = label_frame(b, :br_if, depth)
    ts = label_types(f)
    if VALIDATE[]
        pop_t!(b, :br_if, I32)
        pop_ts!(b, :br_if, ts)
        push_ts!(b, ts)
    end
    append_inst!(b, :br_if, depth)
end

"Branch to `labels[i]` for `i` on the stack, or to `default`."
function br_table!(b::Builder, labels::Vector{Int}, default::Integer)
    ts = label_types(label_frame(b, :br_table, default))
    if VALIDATE[]
        pop_t!(b, :br_table, I32)
        for l in labels
            lts = label_types(label_frame(b, :br_table, l))
            length(lts) == length(ts) || verr(b, :br_table, "branch targets of different arities")
            # every target must accept the operands themselves
            push_ts!(b, pop_ts!(b, :br_table, lts))
        end
        pop_ts!(b, :br_table, ts)
    end
    append_inst!(b, :br_table, labels, default)
    set_unreachable!(b)
end

"Branch to `depth` if the reference on the stack is null; otherwise keep it, non-null."
function br_on_null!(b::Builder, depth::Integer)
    ts = label_types(label_frame(b, :br_on_null, depth))
    t = pop_ref!(b, :br_on_null)
    if VALIDATE[]
        pop_ts!(b, :br_on_null, ts)
        push_ts!(b, ts)
    end
    append_inst!(b, :br_on_null, depth)
    push_t!(b, RefType(t.heap, false))
end

"""
Branch to `depth` if the reference on the stack is not null, passing it (non-null) as the
label's last value; otherwise drop it.
"""
function br_on_non_null!(b::Builder, depth::Integer)
    op = :br_on_non_null
    ts = label_types(label_frame(b, op, depth))
    t = pop_ref!(b, op)
    if VALIDATE[]
        isempty(ts) && verr(b, op, "the target of br_on_non_null takes no reference")
        push_t!(b, RefType(t.heap, false))
        pop_ts!(b, op, ts)
        push_ts!(b, ts[1:end-1])
    end
    append_inst!(b, op, depth)
end

"""
    br_on_cast!(b, depth, rt1::RefType, rt2::RefType)

Branch to `depth` if the reference on the stack (of type `rt1`) is of type `rt2`;
otherwise keep it, of type `rt1` minus `rt2`.
"""
br_on_cast!(b::Builder, depth::Integer, rt1::RefType, rt2::RefType) =
    cast_branch!(b, :br_on_cast, depth, rt1, rt2)

"""
    br_on_cast_fail!(b, depth, rt1::RefType, rt2::RefType)

Branch to `depth` if the reference on the stack (of type `rt1`) is not of type `rt2`;
otherwise keep it, of type `rt2`.
"""
br_on_cast_fail!(b::Builder, depth::Integer, rt1::RefType, rt2::RefType) =
    cast_branch!(b, :br_on_cast_fail, depth, rt1, rt2)

function cast_branch!(b::Builder, op::Symbol, depth::Integer, rt1::RefType, rt2::RefType)
    ts = label_types(label_frame(b, op, depth))
    m = b.mod
    valid_valtype(m, rt1) && valid_valtype(m, rt2) || verr(b, op, "invalid types $rt1, $rt2")
    diff = RefType(rt1.heap, rt1.nullable && !rt2.nullable)   # rt1 \ rt2
    taken, kept = op === :br_on_cast ? (rt2, diff) : (diff, rt2)
    if VALIDATE[]
        subtype(m, rt2, rt1) || verr(b, op, "$rt2 is not a subtype of $rt1")
        isempty(ts) && verr(b, op, "the target of $op takes no reference")
        pop_t!(b, op, rt1)
        push_t!(b, taken)
        pop_ts!(b, op, ts)
        push_ts!(b, ts[1:end-1])
    else
        pop_any!(b, op)
    end
    append_inst!(b, op, UInt8(rt1.nullable) | UInt8(rt2.nullable) << 1, depth, rt1.heap, rt2.heap)
    push_t!(b, kept)
end

"Return from the function."
function return!(b::Builder)
    VALIDATE[] && pop_ts!(b, :return, b.frames[1].results)
    append_inst!(b, :return)
    set_unreachable!(b)
end

"Trap."
function unreachable!(b::Builder)
    append_inst!(b, :unreachable)
    set_unreachable!(b)
end

tag_params(b::Builder, op::Symbol, tag) =
    tag isa Tag ? (typedef(b.mod, tag.type).comp::FuncType).params : verr(b, op, "$tag is not a tag")

"Throw the exception `tag` with the payload on the stack."
function throw!(b::Builder, tag::Tag)
    VALIDATE[] && pop_ts!(b, :throw, tag_params(b, :throw, tag))
    append_inst!(b, :throw, tag)
    set_unreachable!(b)
end

"Rethrow the exception reference (`exnref`) on the stack."
function throw_ref!(b::Builder)
    VALIDATE[] && pop_t!(b, :throw_ref, RefType(:exn, true))
    append_inst!(b, :throw_ref)
    set_unreachable!(b)
end

"""
    try_table!(b, bt, catches)

Begin a `try_table` block with the handlers `catches`, `(kind, tag, label)` tuples: kind 0
`catch`, 1 `catch_ref`, 2 `catch_all`, 3 `catch_all_ref` (labels relative to outside the
`try_table`).
"""
function try_table!(b::Builder, bt, catches::Vector)
    params, results = blocktype_sig(b, bt, :try_table)
    if VALIDATE[]
        pop_ts!(b, :try_table, params)
        foreach(c -> check_catch(b, c), catches)
    end
    append_inst!(b, :try_table, bt, catches)
    push_frame!(b, :try_table, params, results)
end

# the values a handler passes to its label must match the label's types
function check_catch(b::Builder, c)
    op = :try_table
    c isa Union{Tuple,AbstractVector} && length(c) == 3 ||
        verr(b, op, "a catch is a (kind, tag, label) tuple")
    kind, tag, label = c
    kind in 0:3 || verr(b, op, "invalid catch kind $kind")
    ts = kind < 2 ? copy(tag_params(b, op, tag)) : ValType[]
    kind in (1, 3) && push!(ts, RefType(:exn, false))
    lts = label_types(label_frame(b, op, label))
    subtypes(b.mod, ts, lts) ||
        verr(b, op, "catch to label $label passes [$(join(ts, ", "))], the label takes [$(join(lts, ", "))]")
end

## calls

"Call the function `f`."
function call!(b::Builder, f::Func)
    VALIDATE[] && pop_ts!(b, :call, f.params)
    append_inst!(b, :call, f)
    push_ts!(b, f.results)
end

function func_type(b::Builder, op::Symbol, t)
    t isa TypeRef && valid_heap(b.mod, t) && typedef(b.mod, t).comp isa FuncType ||
        verr(b, op, "$t is not a function type")
    return typedef(b.mod, t).comp::FuncType
end

"Call the function reference on the stack, of function type `t`."
function call_ref!(b::Builder, t::TypeRef)
    ft = func_type(b, :call_ref, t)
    if VALIDATE[]
        pop_t!(b, :call_ref, RefType(t, true))
        pop_ts!(b, :call_ref, ft.params)
    end
    append_inst!(b, :call_ref, t)
    push_ts!(b, ft.results)
end

# a tail call returns the callee's results from the function
function check_tail_results(b::Builder, op::Symbol, results)
    subtypes(b.mod, results, b.func.results) ||
        verr(b, op, "the callee returns [$(join(results, ", "))], the function [$(join(b.func.results, ", "))]")
end

"Tail-call the function `f`."
function return_call!(b::Builder, f::Func)
    if VALIDATE[]
        pop_ts!(b, :return_call, f.params)
        check_tail_results(b, :return_call, f.results)
    end
    append_inst!(b, :return_call, f)
    set_unreachable!(b)
end

"Tail-call the function reference on the stack, of function type `t`."
function return_call_ref!(b::Builder, t::TypeRef)
    ft = func_type(b, :return_call_ref, t)
    if VALIDATE[]
        pop_t!(b, :return_call_ref, RefType(t, true))
        pop_ts!(b, :return_call_ref, ft.params)
        check_tail_results(b, :return_call_ref, ft.results)
    end
    append_inst!(b, :return_call_ref, t)
    set_unreachable!(b)
end

## other instructions: validated by their signatures

# the control instructions whose functions take the immediates of the instruction
const CONTROL = Dict{Symbol,Function}(
    :block => block!, :loop => loop!, :if => if!, :else => else!, :end => end!,
    :br => br!, :br_if => br_if!, :br_table => br_table!, :br_on_null => br_on_null!,
    :br_on_non_null => br_on_non_null!, :return => return!, :unreachable => unreachable!,
    :throw => throw!, :throw_ref => throw_ref!, :try_table => try_table!, :call => call!,
    :call_ref => call_ref!, :return_call => return_call!, :return_call_ref => return_call_ref!)

"""
    emit!(b, op, imms...)

Emit the instruction `op` with the immediates `imms`, validating it.
"""
function emit!(b::Builder, op::Symbol, imms...)
    c = get(CONTROL, op, nothing)
    if c !== nothing
        c(b, imms...)
    else
        typecheck!(b, op, imms)
        append_inst!(b, op, imms...)
    end
    return b
end

field_types(b::Builder, t::TypeRef) = (typedef(b.mod, t).comp::StructType).fields
array_elem(b::Builder, t::TypeRef) = (typedef(b.mod, t).comp::ArrayType).elem

function expect_struct(b::Builder, op, t)
    t isa TypeRef && typedef(b.mod, t).comp isa StructType || verr(b, op, "$t is not a struct type")
end
function expect_array(b::Builder, op, t)
    t isa TypeRef && typedef(b.mod, t).comp isa ArrayType || verr(b, op, "$t is not an array type")
end

function check_field_read(b, op, f::FieldType)
    packed = f.storage isa PackedType
    if op === :struct_get || op === :array_get
        packed && verr(b, op, "packed field read without sign extension")
    else
        packed || verr(b, op, "sign extension on a non-packed field")
    end
end

function imm_ok(m::WModule, kind::Symbol, @nospecialize(x))
    (kind === :u32 || kind === :align || kind === :offset) && return x isa Integer && 0 <= x <= typemax(UInt32)
    kind === :memidx && return x == 0
    kind === :i32 && return x isa Integer && typemin(Int32) <= x <= typemax(UInt32)
    kind === :i64 && return x isa Integer && typemin(Int64) <= x <= typemax(UInt64)
    (kind === :f32 || kind === :f64) && return x isa Real
    kind === :type && return x isa TypeRef && valid_heap(m, x)
    kind in (:heap, :ref, :refnull) && return valid_heap(m, x)
    kind === :func && return x isa Func
    kind === :global && return x isa Global
    kind === :valtypes && return x isa AbstractVector && all(t -> valid_valtype(m, t), x)
    return true
end

function check_imms(b::Builder, op::Symbol, info::OpInfo, imms)
    length(imms) == length(info.imms) ||
        verr(b, op, "$(length(info.imms)) immediates expected, got $(length(imms))")
    for (k, x) in zip(info.imms, imms)
        imm_ok(b.mod, k, x) || verr(b, op, "invalid immediate of kind $k: $(typeof(x)) $(x isa Union{Number,Symbol,TypeRef} ? x : "")")
    end
end

function typecheck!(b::Builder, op::Symbol, imms)
    m = b.mod
    info = get(INSTRUCTIONS, op, nothing)
    info === nothing && verr(b, op, "unknown instruction")
    check_imms(b, op, info, imms)
    if haskey(MEMORY_ACCESSES, op) || op === :memory_size || op === :memory_grow
        m.memory === nothing && verr(b, op, "the module has no memory")
        a = get(MEMORY_ACCESSES, op, nothing)
        a === nothing || imms[1] <= a || verr(b, op, "alignment 2^$(imms[1]) exceeds the natural alignment 2^$a")
    end
    if info.sig !== nothing
        pop_ts!(b, op, info.sig[1])
        push_ts!(b, info.sig[2])
        return
    end
    if op === :drop
        pop_any!(b, op)
    elseif op === :select
        pop_t!(b, op, I32)
        t2 = pop_any!(b, op); t1 = pop_any!(b, op)
        (t1 === nothing || t1 isa NumType) && (t2 === nothing || t2 isa NumType) ||
            verr(b, op, "untyped select on references")
        t1 !== nothing && t2 !== nothing && t1 !== t2 && verr(b, op, "select of $t1 and $t2")
        push_t!(b, something(t1, t2, Some(nothing)))
    elseif op === :select_t
        length(imms[1]) == 1 || verr(b, op, "select takes one type")
        t = imms[1][1]
        pop_t!(b, op, I32); pop_t!(b, op, t); pop_t!(b, op, t)
        push_t!(b, t)
    elseif op === :local_get
        i = imms[1]; check_local(b, op, i)
        needs_init(b, i) && !(i in b.initialized) &&
            verr(b, op, "local $i (of non-defaultable type $(local_type(b.func, i))) is read before it is set")
        push_t!(b, local_type(b.func, i))
    elseif op === :local_set
        i = imms[1]; check_local(b, op, i)
        pop_t!(b, op, local_type(b.func, i))
        set_local!(b, i)
    elseif op === :local_tee
        i = imms[1]; check_local(b, op, i)
        t = local_type(b.func, i)
        pop_t!(b, op, t)
        set_local!(b, i)
        push_t!(b, t)
    elseif op === :global_get
        push_t!(b, (imms[1]::Global).type)
    elseif op === :global_set
        g = imms[1]::Global
        g.mutable || verr(b, op, "global $(g.name) is immutable")
        pop_t!(b, op, g.type)
    elseif op === :ref_null
        push_t!(b, RefType(imms[1], true))
    elseif op === :ref_is_null
        pop_ref!(b, op)
        push_t!(b, I32)
    elseif op === :ref_as_non_null
        t = pop_ref!(b, op)
        push_t!(b, RefType(t.heap, false))
    elseif op === :ref_func
        f = imms[1]::Func
        b.constexpr || declare!(m, f)   # references in global initializers need no declaration
        push_t!(b, RefType(f.type, false))
    elseif op in (:ref_test, :ref_test_null, :ref_cast, :ref_cast_null)
        ht = imms[1]
        pop_t!(b, op, RefType(heap_top(m, ht), true))
        if op in (:ref_test, :ref_test_null)
            push_t!(b, I32)
        else
            push_t!(b, RefType(ht, op === :ref_cast_null))
        end
    elseif op === :any_convert_extern
        t = pop_t!(b, op, RefType(:extern, true))
        push_t!(b, RefType(:any, t !== nothing && t.nullable))
    elseif op === :extern_convert_any
        t = pop_t!(b, op, RefType(:any, true))
        push_t!(b, RefType(:extern, t !== nothing && t.nullable))
    elseif op === :struct_new
        t = imms[1]; expect_struct(b, op, t)
        pop_ts!(b, op, [unpacked(f.storage) for f in field_types(b, t)])
        push_t!(b, RefType(t, false))
    elseif op === :struct_new_default
        t = imms[1]; expect_struct(b, op, t)
        all(f -> defaultable(f.storage), field_types(b, t)) ||
            verr(b, op, "struct with non-defaultable fields")
        push_t!(b, RefType(t, false))
    elseif op in (:struct_get, :struct_get_s, :struct_get_u)
        t, i = imms; expect_struct(b, op, t)
        fs = field_types(b, t)
        0 <= i < length(fs) || verr(b, op, "no field $i in $t")
        check_field_read(b, op, fs[i+1])
        pop_t!(b, op, RefType(t, true))
        push_t!(b, unpacked(fs[i+1].storage))
    elseif op === :struct_set
        t, i = imms; expect_struct(b, op, t)
        fs = field_types(b, t)
        0 <= i < length(fs) || verr(b, op, "no field $i in $t")
        fs[i+1].mutable || verr(b, op, "field $i of $t is immutable")
        pop_t!(b, op, unpacked(fs[i+1].storage))
        pop_t!(b, op, RefType(t, true))
    elseif op === :array_new
        t = imms[1]; expect_array(b, op, t)
        pop_t!(b, op, I32)
        pop_t!(b, op, unpacked(array_elem(b, t).storage))
        push_t!(b, RefType(t, false))
    elseif op === :array_new_default
        t = imms[1]; expect_array(b, op, t)
        defaultable(array_elem(b, t).storage) ||
            verr(b, op, "array of non-defaultable elements $(array_elem(b, t).storage)")
        pop_t!(b, op, I32)
        push_t!(b, RefType(t, false))
    elseif op === :array_new_fixed
        t, n = imms; expect_array(b, op, t)
        et = unpacked(array_elem(b, t).storage)
        for _ in 1:n
            pop_t!(b, op, et)
        end
        push_t!(b, RefType(t, false))
    elseif op === :array_new_data
        t, d = imms; expect_array(b, op, t)
        check_data_array(b, op, t, d)
        pop_t!(b, op, I32); pop_t!(b, op, I32)
        push_t!(b, RefType(t, false))
    elseif op in (:array_get, :array_get_s, :array_get_u)
        t = imms[1]; expect_array(b, op, t)
        f = array_elem(b, t)
        check_field_read(b, op, f)
        pop_t!(b, op, I32)
        pop_t!(b, op, RefType(t, true))
        push_t!(b, unpacked(f.storage))
    elseif op === :array_set
        t = imms[1]; expect_array(b, op, t)
        f = array_elem(b, t)
        f.mutable || verr(b, op, "array $t is immutable")
        pop_t!(b, op, unpacked(f.storage))
        pop_t!(b, op, I32)
        pop_t!(b, op, RefType(t, true))
    elseif op === :array_fill
        t = imms[1]; expect_array(b, op, t)
        f = array_elem(b, t)
        f.mutable || verr(b, op, "array $t is immutable")
        pop_t!(b, op, I32)
        pop_t!(b, op, unpacked(f.storage))
        pop_t!(b, op, I32)
        pop_t!(b, op, RefType(t, true))
    elseif op === :array_copy
        t1, t2 = imms; expect_array(b, op, t1); expect_array(b, op, t2)
        array_elem(b, t1).mutable || verr(b, op, "array $t1 is immutable")
        storage_subtype(m, array_elem(b, t2).storage, array_elem(b, t1).storage) ||
            verr(b, op, "array.copy between incompatible arrays $t1 and $t2")
        pop_t!(b, op, I32); pop_t!(b, op, I32)
        pop_t!(b, op, RefType(t2, true))
        pop_t!(b, op, I32)
        pop_t!(b, op, RefType(t1, true))
    elseif op === :array_init_data
        t, d = imms; expect_array(b, op, t)
        array_elem(b, t).mutable || verr(b, op, "array $t is immutable")
        check_data_array(b, op, t, d)
        pop_t!(b, op, I32); pop_t!(b, op, I32); pop_t!(b, op, I32)
        pop_t!(b, op, RefType(t, true))
    else
        verr(b, op, "a control instruction: use its function")
    end
    return
end

# arrays initialized from a data segment have numeric (or vector) elements
function check_data_array(b::Builder, op::Symbol, t::TypeRef, d)
    array_elem(b, t).storage isa RefType && verr(b, op, "$op of a reference array")
    0 <= d < length(b.mod.datas) || verr(b, op, "no data segment $d")
end
