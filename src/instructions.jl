# The instruction set, in one table: for each instruction, its opcode, the kinds of its
# immediates, its name in the text format and, for the instructions with a fixed type, its
# signature. The table drives encoding, printing and the validation of simple instructions.

"An instruction of the table: opcode bytes, immediate kinds, text name, fixed signature."
struct OpInfo
    code::Vector{UInt8}
    imms::Tuple
    text::String
    sig::Union{Nothing,Tuple{Vector{ValType},Vector{ValType}}}
end

const INSTRUCTIONS = Dict{Symbol,OpInfo}()

"The natural alignment (log2 of bytes) of each load and store of the linear memory."
const MEMORY_ACCESSES = Dict{Symbol,Int}()

# the first components of the names written with a `.` in the text format
const TEXT_NAMESPACES = Set(["i32", "i64", "f32", "f64", "v128", "local", "global", "ref",
                             "struct", "array", "i31", "any", "extern", "table", "memory",
                             "elem", "data"])

"The name of the instruction `op` in the text format (`i32_add` is `i32.add`)."
function text_name(op::Symbol)
    s = string(op)
    i = findfirst('_', s)
    i !== nothing && s[1:i-1] in TEXT_NAMESPACES || return s
    return string(s[1:i-1], '.', s[i+1:end])
end

const NUMTYPES = Dict("i32" => I32, "i64" => I64, "f32" => F32, "f64" => F64)
const BINOPS = Set(["add", "sub", "mul", "div", "div_s", "div_u", "rem_s", "rem_u", "and",
                    "or", "xor", "shl", "shr_s", "shr_u", "rotl", "rotr", "min", "max",
                    "copysign"])
const UNOPS = Set(["clz", "ctz", "popcnt", "abs", "neg", "ceil", "floor", "trunc",
                   "nearest", "sqrt", "extend8_s", "extend16_s", "extend32_s"])
const RELOPS = Set(["eq", "ne", "lt", "lt_s", "lt_u", "gt", "gt_s", "gt_u", "le", "le_s",
                    "le_u", "ge", "ge_s", "ge_u"])

# the signature (params, results) of a numeric instruction, from its name
function numeric_sig(op::Symbol)
    parts = split(string(op), '_')
    t = get(NUMTYPES, parts[1], nothing)
    t === nothing && return nothing
    rest = join(parts[2:end], '_')
    src = nothing
    for p in parts[2:end]
        haskey(NUMTYPES, p) && (src = NUMTYPES[p])
    end
    src !== nothing && return (ValType[src], ValType[t])   # conversion
    rest in BINOPS && return (ValType[t, t], ValType[t])
    rest in UNOPS && return (ValType[t], ValType[t])
    rest == "eqz" && return (ValType[t], ValType[I32])
    rest in RELOPS && return (ValType[t, t], ValType[I32])
    return nothing
end

function definst!(op::Symbol, code, imms::Tuple=(); sig=numeric_sig(op), text=text_name(op))
    INSTRUCTIONS[op] = OpInfo(UInt8[code...], imms, text, sig)
end

fixedsig(params, results) = (ValType[params...], ValType[results...])

let
    # control (validated by their own functions in the builder)
    definst!(:unreachable, 0x00); definst!(:nop, 0x01; sig=fixedsig((), ()))
    definst!(:block, 0x02, (:bt,)); definst!(:loop, 0x03, (:bt,)); definst!(:if, 0x04, (:bt,))
    definst!(:else, 0x05); definst!(:end, 0x0b)
    definst!(:throw, 0x08, (:tag,)); definst!(:throw_ref, 0x0a)
    definst!(:br, 0x0c, (:u32,)); definst!(:br_if, 0x0d, (:u32,))
    definst!(:br_table, 0x0e, (:labels, :u32)); definst!(:return, 0x0f)
    definst!(:call, 0x10, (:func,)); definst!(:return_call, 0x12, (:func,))
    definst!(:call_ref, 0x14, (:type,)); definst!(:return_call_ref, 0x15, (:type,))
    definst!(:try_table, 0x1f, (:bt, :catches))
    definst!(:br_on_null, 0xd5, (:u32,)); definst!(:br_on_non_null, 0xd6, (:u32,))
    definst!(:br_on_cast, (0xfb, 0x18), (:castflags, :u32, :heap, :heap))
    definst!(:br_on_cast_fail, (0xfb, 0x19), (:castflags, :u32, :heap, :heap))

    # parametric, variables
    definst!(:drop, 0x1a); definst!(:select, 0x1b)
    definst!(:select_t, 0x1c, (:valtypes,); text="select")
    definst!(:local_get, 0x20, (:u32,)); definst!(:local_set, 0x21, (:u32,))
    definst!(:local_tee, 0x22, (:u32,))
    definst!(:global_get, 0x23, (:global,)); definst!(:global_set, 0x24, (:global,))

    # linear memory: loads and stores take a memarg, two immediates (the log2 of the
    # alignment, at most the natural one, and a constant offset added to the address)
    for (i, (op, t, a)) in enumerate(((:i32_load, I32, 2), (:i64_load, I64, 3), (:f32_load, F32, 2),
                                      (:f64_load, F64, 3), (:i32_load8_s, I32, 0), (:i32_load8_u, I32, 0),
                                      (:i32_load16_s, I32, 1), (:i32_load16_u, I32, 1), (:i64_load8_s, I64, 0),
                                      (:i64_load8_u, I64, 0), (:i64_load16_s, I64, 1), (:i64_load16_u, I64, 1),
                                      (:i64_load32_s, I64, 2), (:i64_load32_u, I64, 2)))
        definst!(op, 0x28 + i - 1, (:align, :offset); sig=fixedsig((I32,), (t,)))
        MEMORY_ACCESSES[op] = a
    end
    for (i, (op, t, a)) in enumerate(((:i32_store, I32, 2), (:i64_store, I64, 3), (:f32_store, F32, 2),
                                      (:f64_store, F64, 3), (:i32_store8, I32, 0), (:i32_store16, I32, 1),
                                      (:i64_store8, I64, 0), (:i64_store16, I64, 1), (:i64_store32, I64, 2)))
        definst!(op, 0x36 + i - 1, (:align, :offset); sig=fixedsig((I32, t), ()))
        MEMORY_ACCESSES[op] = a
    end
    definst!(:memory_size, 0x3f, (:memidx,); sig=fixedsig((), (I32,)))
    definst!(:memory_grow, 0x40, (:memidx,); sig=fixedsig((I32,), (I32,)))

    # numeric
    definst!(:i32_const, 0x41, (:i32,); sig=fixedsig((), (I32,)))
    definst!(:i64_const, 0x42, (:i64,); sig=fixedsig((), (I64,)))
    definst!(:f32_const, 0x43, (:f32,); sig=fixedsig((), (F32,)))
    definst!(:f64_const, 0x44, (:f64,); sig=fixedsig((), (F64,)))
    numeric = [
        :i32_eqz, :i32_eq, :i32_ne, :i32_lt_s, :i32_lt_u, :i32_gt_s, :i32_gt_u, :i32_le_s,
        :i32_le_u, :i32_ge_s, :i32_ge_u,
        :i64_eqz, :i64_eq, :i64_ne, :i64_lt_s, :i64_lt_u, :i64_gt_s, :i64_gt_u, :i64_le_s,
        :i64_le_u, :i64_ge_s, :i64_ge_u,
        :f32_eq, :f32_ne, :f32_lt, :f32_gt, :f32_le, :f32_ge,
        :f64_eq, :f64_ne, :f64_lt, :f64_gt, :f64_le, :f64_ge,
        :i32_clz, :i32_ctz, :i32_popcnt, :i32_add, :i32_sub, :i32_mul, :i32_div_s,
        :i32_div_u, :i32_rem_s, :i32_rem_u, :i32_and, :i32_or, :i32_xor, :i32_shl,
        :i32_shr_s, :i32_shr_u, :i32_rotl, :i32_rotr,
        :i64_clz, :i64_ctz, :i64_popcnt, :i64_add, :i64_sub, :i64_mul, :i64_div_s,
        :i64_div_u, :i64_rem_s, :i64_rem_u, :i64_and, :i64_or, :i64_xor, :i64_shl,
        :i64_shr_s, :i64_shr_u, :i64_rotl, :i64_rotr,
        :f32_abs, :f32_neg, :f32_ceil, :f32_floor, :f32_trunc, :f32_nearest, :f32_sqrt,
        :f32_add, :f32_sub, :f32_mul, :f32_div, :f32_min, :f32_max, :f32_copysign,
        :f64_abs, :f64_neg, :f64_ceil, :f64_floor, :f64_trunc, :f64_nearest, :f64_sqrt,
        :f64_add, :f64_sub, :f64_mul, :f64_div, :f64_min, :f64_max, :f64_copysign,
        :i32_wrap_i64, :i32_trunc_f32_s, :i32_trunc_f32_u, :i32_trunc_f64_s,
        :i32_trunc_f64_u, :i64_extend_i32_s, :i64_extend_i32_u, :i64_trunc_f32_s,
        :i64_trunc_f32_u, :i64_trunc_f64_s, :i64_trunc_f64_u, :f32_convert_i32_s,
        :f32_convert_i32_u, :f32_convert_i64_s, :f32_convert_i64_u, :f32_demote_f64,
        :f64_convert_i32_s, :f64_convert_i32_u, :f64_convert_i64_s, :f64_convert_i64_u,
        :f64_promote_f32, :i32_reinterpret_f32, :i64_reinterpret_f64, :f32_reinterpret_i32,
        :f64_reinterpret_i64,
        :i32_extend8_s, :i32_extend16_s, :i64_extend8_s, :i64_extend16_s, :i64_extend32_s]
    for (i, op) in enumerate(numeric)
        definst!(op, 0x45 + i - 1)
    end
    for (i, op) in enumerate((:i32_trunc_sat_f32_s, :i32_trunc_sat_f32_u,
                              :i32_trunc_sat_f64_s, :i32_trunc_sat_f64_u,
                              :i64_trunc_sat_f32_s, :i64_trunc_sat_f32_u,
                              :i64_trunc_sat_f64_s, :i64_trunc_sat_f64_u))
        definst!(op, (0xfc, i - 1))
    end

    # references
    definst!(:ref_null, 0xd0, (:heap,)); definst!(:ref_is_null, 0xd1)
    definst!(:ref_func, 0xd2, (:func,))
    definst!(:ref_eq, 0xd3; sig=fixedsig((RefType(:eq), RefType(:eq)), (I32,)))
    definst!(:ref_as_non_null, 0xd4)

    # GC; `ref_test_null` is `ref.test (ref null ht)` in the text format
    gc = [
        :struct_new => (0x00, (:type,)), :struct_new_default => (0x01, (:type,)),
        :struct_get => (0x02, (:type, :u32)), :struct_get_s => (0x03, (:type, :u32)),
        :struct_get_u => (0x04, (:type, :u32)), :struct_set => (0x05, (:type, :u32)),
        :array_new => (0x06, (:type,)), :array_new_default => (0x07, (:type,)),
        :array_new_fixed => (0x08, (:type, :u32)), :array_new_data => (0x09, (:type, :u32)),
        :array_get => (0x0b, (:type,)), :array_get_s => (0x0c, (:type,)),
        :array_get_u => (0x0d, (:type,)), :array_set => (0x0e, (:type,)),
        :array_fill => (0x10, (:type,)),
        :array_copy => (0x11, (:type, :type)), :array_init_data => (0x12, (:type, :u32)),
        :ref_test => (0x14, (:ref,)), :ref_cast => (0x16, (:ref,)),
        :any_convert_extern => (0x1a, ()), :extern_convert_any => (0x1b, ())]
    for (op, (code, imms)) in gc
        definst!(op, (0xfb, code), imms)
    end
    definst!(:array_len, (0xfb, 0x0f); sig=fixedsig((RefType(:array),), (I32,)))
    definst!(:ref_test_null, (0xfb, 0x15), (:refnull,); text="ref.test")
    definst!(:ref_cast_null, (0xfb, 0x17), (:refnull,); text="ref.cast")
    definst!(:ref_i31, (0xfb, 0x1c); sig=fixedsig((I32,), (RefType(:i31, false),)))
    definst!(:i31_get_s, (0xfb, 0x1d); sig=fixedsig((RefType(:i31),), (I32,)))
    definst!(:i31_get_u, (0xfb, 0x1e); sig=fixedsig((RefType(:i31),), (I32,)))
end
