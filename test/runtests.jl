using Test, WasmBuilder
import NodeJS_24_jll
const W = WasmBuilder

# Node.js 24 (WasmGC, exnref exceptions), or the executable named by WASMBUILDER_NODE
node_cmd() = haskey(ENV, "WASMBUILDER_NODE") ? `$(ENV["WASMBUILDER_NODE"])` : NodeJS_24_jll.node()

# validation by wasm-tools, independent of WasmBuilder's own, when it is installed
const HAS_WASM_TOOLS = W.wasm_tools() !== nothing
HAS_WASM_TOOLS || @info "wasm-tools not found: modules are validated by WasmBuilder only"
checkvalid(bytes) = HAS_WASM_TOOLS ? validate(bytes) : true

function node_run(bytes, js)
    dir = mktempdir()
    write(joinpath(dir, "m.wasm"), bytes)
    script = """
    const fs = require('fs');
    const bytes = fs.readFileSync('$(joinpath(dir, "m.wasm"))');
    WebAssembly.instantiate(bytes, {}).then(({instance}) => { const e = instance.exports; $js });
    """
    write(joinpath(dir, "run.js"), script)
    # exnref (`try_table`) is behind a flag in Node 24
    return strip(read(`$(node_cmd()) --experimental-wasm-exnref $(joinpath(dir, "run.js"))`, String))
end

@testset "WasmBuilder" begin
    m = WModule()
    # a struct {i32 tag; mut f64 x} and a subtype adding an i64
    base = add_type!(m, StructType([FieldType(I32, false)]); final=false)
    pt = add_type!(m, StructType([FieldType(I32, false), FieldType(F64, true)]); final=false, super=base)
    arr = add_type!(m, ArrayType(FieldType(F64, true)))

    # factorial with a loop: block { loop { br_if exit; ...; br loop } }
    f = add_func!(m, "fact", ValType[I64], ValType[I64])
    acc = add_local!(f, I64)
    b = Builder(m, f)
    emit!(b, :i64_const, 1); emit!(b, :local_set, acc)
    block!(b)
    loop!(b)
    emit!(b, :local_get, 0); emit!(b, :i64_const, 1); emit!(b, :i64_le_s); br_if!(b, 1)
    emit!(b, :local_get, acc); emit!(b, :local_get, 0); emit!(b, :i64_mul); emit!(b, :local_set, acc)
    emit!(b, :local_get, 0); emit!(b, :i64_const, 1); emit!(b, :i64_sub); emit!(b, :local_set, 0)
    br!(b, 0)
    end!(b)
    end!(b)
    emit!(b, :local_get, acc)
    finish!(b)
    add_export!(m, "fact", f)

    # struct and array round trip: sum of an array of n copies of x, stored through a struct
    g = add_func!(m, "sumfill", ValType[F64, I32], ValType[F64])
    s = add_local!(g, RefType(pt))
    a = add_local!(g, RefType(arr))
    i = add_local!(g, I32)
    acc2 = add_local!(g, F64)
    b = Builder(m, g)
    emit!(b, :i32_const, 7); emit!(b, :local_get, 0); emit!(b, :struct_new, pt); emit!(b, :local_set, s)
    emit!(b, :local_get, s); emit!(b, :struct_get, pt, 1); emit!(b, :local_get, 1); emit!(b, :array_new, arr)
    emit!(b, :local_set, a)
    block!(b); loop!(b)
    emit!(b, :local_get, i); emit!(b, :local_get, a); emit!(b, :array_len); emit!(b, :i32_ge_u); br_if!(b, 1)
    emit!(b, :local_get, acc2); emit!(b, :local_get, a); emit!(b, :local_get, i); emit!(b, :array_get, arr)
    emit!(b, :f64_add); emit!(b, :local_set, acc2)
    emit!(b, :local_get, i); emit!(b, :i32_const, 1); emit!(b, :i32_add); emit!(b, :local_set, i)
    br!(b, 0); end!(b); end!(b)
    # upcast and test
    emit!(b, :local_get, s); emit!(b, :ref_test, pt)
    if!(b, F64)
    emit!(b, :local_get, acc2)
    else!(b)
    emit!(b, :f64_const, -1.0)
    end!(b)
    finish!(b)
    add_export!(m, "sumfill", g)

    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test node_run(bytes, "console.log(e.fact(20n).toString(), e.sumfill(1.5, 4))") == "2432902008176640000 6"
    @test occursin("struct.new", sprint(print_wat, m))

    # validation errors at emission
    h = add_func!(m, "bad", ValType[I32], ValType[F64])
    b = Builder(m, h)
    @test_throws WasmValidationError emit!(b, :f64_add)
    emit!(b, :local_get, 0)
    @test_throws WasmValidationError emit!(b, :f64_neg)
    b = Builder(m, h)
    emit!(b, :local_get, 0)
    @test_throws WasmValidationError finish!(b)
    b = Builder(m, h)
    emit!(b, :i32_const, 0); emit!(b, :local_get, 0); 
    @test_throws WasmValidationError emit!(b, :struct_set, pt, 1)
    b = Builder(m, h)
    unreachable!(b)
    emit!(b, :f64_add)   # polymorphic stack
    finish!(b)
end

# a function `name` of `m` built by `body(b)`
function build(body, m, name, params=ValType[], results=ValType[]; export_=true)
    f = add_func!(m, name, params, results)
    b = Builder(m, f)
    body(b)
    finish!(b)
    export_ && add_export!(m, name, f)
    return f
end

# the error thrown by `body(b)` on a fresh function (of a scratch copy of the types of `m`)
function fails(body, m, params=ValType[], results=ValType[])
    f = add_func!(m, "scratch", params, results)
    try
        body(Builder(m, f))
        return false
    catch e
        e isa WasmValidationError || rethrow()
        return true
    finally
        filter!(g -> g !== f, m.funcs)
    end
end

const anyref = RefType(:any)
const exnref = RefType(:exn)

@testset "i32.const immediates (bug 1)" begin
    m = WModule()
    for (name, x) in [("u8", UInt8(255)), ("big", Int64(2147483648)), ("u32", typemax(UInt32)),
                      ("neg", Int8(-1))]
        build(b -> emit!(b, :i32_const, x), m, name, ValType[], ValType[I32])
    end
    build(b -> emit!(b, :i64_const, typemax(UInt64)), m, "u64", ValType[], ValType[I64])
    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test node_run(bytes, "console.log(e.u8(), e.big(), e.u32(), e.neg(), e.u64())") ==
          "255 -2147483648 -1 -1 -1n"
    enc(x) = (io = IOBuffer(); W.write_inst(io, Inst(:i32_const, x)); take!(io))
    @test enc(UInt8(255)) == [0x41, 0xff, 0x01]
    @test enc(Int64(2147483648)) == [0x41, 0x80, 0x80, 0x80, 0x80, 0x78]
    @test fails(b -> emit!(b, :i32_const, Int64(1) << 32), m)
    @test fails(b -> emit!(b, :i32_const, -(Int64(1) << 31) - 1), m)
end

@testset "end! on the function body (bug 2)" begin
    m = WModule()
    f = add_func!(m, "f", ValType[], ValType[I32])
    b = Builder(m, f)
    emit!(b, :i32_const, 1)
    @test_throws WasmValidationError end!(b)
    @test length(f.body) == 1
    finish!(b)
    @test_throws WasmValidationError end!(b)
    @test checkvalid(to_bytes(m))
end

@testset "br_table checks every target (bug 3)" begin
    m = WModule()
    two(b) = (block!(b, I64); block!(b, I32); emit!(b, :i32_const, 7); emit!(b, :i32_const, 0))
    @test fails(b -> (two(b); br_table!(b, [1], 0)), m)
    @test fails(b -> (two(b); br_table!(b, [0], 1)), m)
    # in unreachable code, the unknown operand matches both
    build(m, "f", ValType[], ValType[I64]) do b
        block!(b, I64); block!(b, I32)
        unreachable!(b)
        br_table!(b, [0], 1)
        end!(b)
        emit!(b, :drop); emit!(b, :i64_const, 0)
        end!(b)
    end
    @test checkvalid(to_bytes(m))
end

@testset "non-defaultable locals (bug 4)" begin
    m = WModule()
    s = add_type!(m, StructType([FieldType(I32, false)]))
    ref = RefType(s, false)
    setx(b, x) = (emit!(b, :i32_const, 1); emit!(b, :struct_new, s); emit!(b, :local_set, x))
    @test fails(m) do b
        emit!(b, :local_get, add_local!(b.func, ref))
    end
    @test fails(m) do b   # set in a block, unset after it
        x = add_local!(b.func, ref)
        block!(b); setx(b, x); end!(b)
        emit!(b, :local_get, x)
    end
    @test fails(m) do b   # set in the then arm, unset in the else arm
        x = add_local!(b.func, ref)
        emit!(b, :i32_const, 1); if!(b); setx(b, x); else!(b)
        emit!(b, :local_get, x)
    end
    build(m, "f", ValType[], ValType[I32]) do b
        x = add_local!(b.func, ref)
        y = add_local!(b.func, ref)
        setx(b, x)
        block!(b); emit!(b, :local_get, x); emit!(b, :drop); end!(b)
        emit!(b, :local_get, x); emit!(b, :local_tee, y); emit!(b, :drop)
        emit!(b, :local_get, y); emit!(b, :struct_get, s, 0)
    end
    @test checkvalid(to_bytes(m))
end

@testset "unknown references in unreachable code (bug 5)" begin
    m = WModule()
    @test fails(b -> (unreachable!(b); emit!(b, :ref_as_non_null); emit!(b, :i32_eqz)), m)
    @test fails(b -> (unreachable!(b); br_on_null!(b, 0); emit!(b, :i32_eqz)), m)
    build(b -> (unreachable!(b); emit!(b, :any_convert_extern)), m, "f", ValType[],
          ValType[RefType(:any, false)])
    build(b -> (unreachable!(b); emit!(b, :ref_as_non_null); emit!(b, :drop)), m, "g")
    @test checkvalid(to_bytes(m))
end

@testset "br_on_null checks its operand (bug 6)" begin
    m = WModule()
    f = add_func!(m, "f", ValType[I32], ValType[])
    b = Builder(m, f)
    block!(b); emit!(b, :local_get, 0)
    @test_throws WasmValidationError br_on_null!(b, 0)
    @test length(f.body) == 2
end

@testset "if without else (bug 7)" begin
    m = WModule()
    build(m, "f", ValType[I32], ValType[anyref]) do b
        emit!(b, :i32_const, 1); emit!(b, :ref_i31); emit!(b, :local_get, 0)
        if!(b, blocktype(b, ValType[RefType(:i31)], ValType[anyref]))
        end!(b)
    end
    @test checkvalid(to_bytes(m))
    @test fails(m, ValType[I32]) do b
        emit!(b, :i32_const, 1); emit!(b, :local_get, 0)
        if!(b, blocktype(b, ValType[I32], ValType[I64]))
        end!(b)
    end
end

@testset "try_table handlers (bug 8)" begin
    m = WModule()
    tag = add_tag!(m, ValType[I32])
    @test fails(b -> (block!(b, I32); try_table!(b, :empty, [(0, tag, 5)])), m)
    @test fails(b -> (block!(b, I64); try_table!(b, :empty, [(0, tag, 0)])), m)
    @test fails(b -> (block!(b, I32); try_table!(b, :empty, [(1, tag, 0)])), m)
    @test fails(b -> (block!(b, I32); try_table!(b, :empty, [(2, nothing, 0)])), m)
    @test fails(b -> (block!(b, exnref); try_table!(b, :empty, [(2, nothing, 0)])), m)
    @test fails(b -> (block!(b); try_table!(b, :empty, [(0, nothing, 0)])), m)
    # catch with the payload, and catch_all_ref to a label of a nullable exnref
    build(m, "catch", ValType[I32], ValType[I32]) do b
        block!(b, I32)
        try_table!(b, :empty, [(0, tag, 0)])
        emit!(b, :local_get, 0); throw!(b, tag)
        end!(b)
        emit!(b, :i32_const, -1)
        end!(b)
        emit!(b, :i32_const, 1); emit!(b, :i32_add)
    end
    build(m, "catch_all_ref", ValType[], ValType[exnref]) do b
        block!(b, exnref)
        try_table!(b, :empty, [(3, nothing, 0)])
        end!(b)
        emit!(b, :ref_null, :exn)
        end!(b)
    end
    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test node_run(bytes, "console.log(e.catch(41))") == "42"
end

@testset "extern conversions (bug 9)" begin
    m = WModule()
    @test fails(b -> (emit!(b, :ref_null, :func); emit!(b, :any_convert_extern)), m)
    @test fails(b -> (emit!(b, :ref_null, :extern); emit!(b, :extern_convert_any)), m)
    @test fails(b -> (emit!(b, :i32_const, 0); emit!(b, :any_convert_extern)), m)
    build(m, "f") do b
        emit!(b, :ref_null, :noextern); emit!(b, :any_convert_extern); emit!(b, :drop)
        emit!(b, :ref_null, :none); emit!(b, :extern_convert_any); emit!(b, :drop)
    end
    @test checkvalid(to_bytes(m))
end

@testset "array.new_default needs defaultable elements (bug 10)" begin
    m = WModule()
    s = add_type!(m, StructType(FieldType[]))
    nonnull = add_type!(m, ArrayType(FieldType(RefType(s, false), true)))
    nullable = add_type!(m, ArrayType(FieldType(RefType(s, true), true)))
    @test fails(b -> (emit!(b, :i32_const, 1); emit!(b, :array_new_default, nonnull)), m)
    build(b -> (emit!(b, :i32_const, 1); emit!(b, :array_new_default, nullable); emit!(b, :drop)), m, "f")
    @test checkvalid(to_bytes(m))
end

@testset "array.copy compares storage types (bug 11)" begin
    m = WModule()
    a8 = add_type!(m, ArrayType(FieldType(I8, true)))
    a16 = add_type!(m, ArrayType(FieldType(I16, true)))
    a32 = add_type!(m, ArrayType(FieldType(I32, true)))
    c8 = add_type!(m, ArrayType(FieldType(I8, false)))
    copy(dst, src) = b -> begin
        emit!(b, :ref_null, dst); emit!(b, :i32_const, 0)
        emit!(b, :ref_null, src); emit!(b, :i32_const, 0); emit!(b, :i32_const, 0)
        emit!(b, :array_copy, dst, src)
    end
    @test fails(copy(a8, a16), m)
    @test fails(copy(a16, a8), m)
    @test fails(copy(a32, a8), m)
    @test fails(copy(a8, a32), m)
    build(copy(a8, c8), m, "f")
    @test checkvalid(to_bytes(m))
end

@testset "array.init_data (bug 12)" begin
    m = WModule()
    add_data!(m, UInt8[1, 2, 3])
    mut8 = add_type!(m, ArrayType(FieldType(I8, true)))
    imm8 = add_type!(m, ArrayType(FieldType(I8, false)))
    refs = add_type!(m, ArrayType(FieldType(anyref, true)))
    init(t, d) = b -> begin
        emit!(b, :ref_null, t)
        foreach(_ -> emit!(b, :i32_const, 0), 1:3)
        emit!(b, :array_init_data, t, d)
    end
    @test fails(init(imm8, 0), m)
    @test fails(init(refs, 0), m)
    @test fails(init(mut8, 1), m)
    build(init(mut8, 0), m, "f")
    @test checkvalid(to_bytes(m))
end

@testset "subtype declarations (bug 13)" begin
    st(fields...) = StructType(collect(FieldType, fields))
    function bad(build)
        m = WModule()
        build(m)
        return (try verify(m); false catch e; e isa WasmValidationError end) &&
               (try to_bytes(m); false catch e; e isa WasmValidationError end)
    end
    @test bad(m -> add_type!(m, st(); super=add_type!(m, st())))               # final supertype
    @test bad(m -> add_type!(m, st(FieldType(F64, false));
                             super=add_type!(m, st(FieldType(I32, false)); final=false)))
    @test bad(m -> add_type!(m, st(); super=add_type!(m, st(FieldType(I32, false)); final=false)))
    @test bad(m -> add_type!(m, st(FieldType(RefType(:eq), true));             # mutable: invariant
                             super=add_type!(m, st(FieldType(anyref, true)); final=false)))
    @test bad(m -> add_type!(m, st(FieldType(I32, true));
                             super=add_type!(m, st(FieldType(I32, false)); final=false)))
    @test bad(m -> add_type!(m, ArrayType(FieldType(I8, false));
                             super=add_type!(m, ArrayType(FieldType(I32, false)); final=false)))
    @test bad(m -> add_type!(m, FuncType(ValType[RefType(:i31)], ValType[]);   # contravariant
                             super=add_type!(m, FuncType(ValType[RefType(:eq)], ValType[]); final=false)))
    @test bad(m -> add_type!(m, FuncType(ValType[], ValType[]);
                             super=add_type!(m, st(); final=false)))
    @test bad(m -> add_type!(m, st(); super=TypeRef(0)))                       # itself
    @test bad(m -> (add_type!(m, st(); final=false, super=TypeRef(1)); add_type!(m, st(); final=false)))
    m = WModule()   # a cycle: subtyping terminates, verify rejects it
    push!(m.types, SubType(st(); final=false, super=TypeRef(1)), SubType(st(); final=false, super=TypeRef(0)))
    add_type!(m, st())
    @test !heap_subtype(m, TypeRef(0), TypeRef(2))
    @test_throws WasmValidationError verify(m)
    @test to_bytes(m; verify=false) isa Vector{UInt8}
    # valid declarations
    m = WModule()
    sup = add_type!(m, st(FieldType(anyref, false), FieldType(I32, true)); final=false)
    add_type!(m, st(FieldType(RefType(:eq), false), FieldType(I32, true), FieldType(F64, false)); super=sup)
    fsup = add_type!(m, FuncType(ValType[RefType(:eq)], ValType[anyref]); final=false)
    add_type!(m, FuncType(ValType[anyref], ValType[RefType(:i31)]); super=fsup)
    asup = add_type!(m, ArrayType(FieldType(anyref, false)); final=false)
    add_type!(m, ArrayType(FieldType(RefType(:i31, false), false)); super=asup)
    @test verify(m) === nothing
    @test checkvalid(to_bytes(m))
end

@testset "module validity (bug 14)" begin
    function bad(build)
        m = WModule()
        build(m)
        return try to_bytes(m); false catch e; e isa WasmValidationError end
    end
    @test bad(m -> add_global!(m, "g", I32, false, [Inst(:i64_const, 1)]))
    @test bad(m -> add_global!(m, "g", I32, false, Inst[]))
    @test bad(m -> add_global!(m, "g", I32, false, [Inst(:i32_const, 1), Inst(:i32_const, 2)]))
    @test bad(m -> add_global!(m, "g", I32, false, [Inst(:i32_const, 1), Inst(:i32_const, 2), Inst(:i32_div_s)]))
    @test bad(m -> add_global!(m, "g", I32, false, [Inst(:i32_const, Int64(1) << 32)]))
    @test bad(m -> add_global!(m, "g", I32, false, [Inst(:global_get, add_global!(m, "h", I32, true, [Inst(:i32_const, 1)]))]))
    @test bad(m -> begin     # a later global
        g = add_global!(m, "g", I32, false, Inst[])
        h = add_global!(m, "h", I32, false, [Inst(:i32_const, 1)])
        push!(g.init, Inst(:global_get, h))
    end)
    @test bad(m -> begin
        f = build(b -> nothing, m, "f")
        add_export!(m, "f", f)
    end)
    @test bad(m -> (m.start = build(b -> nothing, m, "s", ValType[I32], ValType[])))
    @test bad(m -> add_export!(m, "x", WModule() |> m2 -> build(b -> nothing, m2, "f")))
    # valid: extended constants, earlier immutable globals, struct.new, ref.func
    m = WModule()
    s = add_type!(m, StructType([FieldType(I32, false), FieldType(RefType(:func), false)]))
    f = build(b -> nothing, m, "f")
    g = add_global!(m, "g", I32, false, [Inst(:i32_const, 2), Inst(:i32_const, 3), Inst(:i32_mul)])
    h = add_global!(m, "h", RefType(s, false), false, [Inst(:global_get, g), Inst(:ref_func, f), Inst(:struct_new, s)])
    add_export!(m, "h", h)
    m.start = f
    @test verify(m) === nothing
    @test isempty(m.declared)
    @test checkvalid(to_bytes(m))
end

@testset "imports keep their signatures (bug 15)" begin
    m = WModule()
    a = add_import!(m, "env", "log", ValType[I32], ValType[])
    @test add_import!(m, "env", "log", ValType[I32], ValType[]) === a
    c = add_import!(m, "env", "log", ValType[F64], ValType[])
    @test c !== a && c.params == ValType[F64]
    build(m, "f") do b
        emit!(b, :i32_const, 1); call!(b, a)
        emit!(b, :f64_const, 1.5); call!(b, c)
    end
    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test count(f -> f.imported !== nothing, m.funcs) == 2
end

@testset "throw_ref (bug 16)" begin
    m = WModule()
    tag = add_tag!(m, ValType[I32])
    @test fails(b -> (emit!(b, :i32_const, 0); throw_ref!(b)), m)
    # rethrow an exception caught by catch_all_ref, caught again by catch
    build(m, "rethrow", ValType[I32], ValType[I32]) do b
        block!(b, I32)
        try_table!(b, :empty, [(0, tag, 0)])
        block!(b, RefType(:exn, false))
        try_table!(b, :empty, [(3, nothing, 0)])
        emit!(b, :local_get, 0); throw!(b, tag)
        end!(b)
        unreachable!(b)
        end!(b)
        throw_ref!(b)
        end!(b)
        unreachable!(b)
        end!(b)
        emit!(b, :i32_const, 1); emit!(b, :i32_add)
    end
    build(m, "rethrow2", ValType[], ValType[]) do b
        emit!(b, :ref_null, :exn); emit!(b, :throw_ref)
    end
    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test node_run(bytes, "console.log(e.rethrow(41))") == "42"
end

@testset "branches on references, tail calls" begin
    m = WModule()
    s = add_type!(m, StructType([FieldType(I32, false)]))
    sref = RefType(s, false)
    # anyref of a struct with field 7 (flag != 0) or an i31
    function anyval(b)
        emit!(b, :local_get, 0)
        if!(b, anyref)
        emit!(b, :i32_const, 7); emit!(b, :struct_new, s)
        else!(b)
        emit!(b, :i32_const, 3); emit!(b, :ref_i31)
        end!(b)
    end
    build(m, "cast", ValType[I32], ValType[I32]) do b
        block!(b, sref)
        anyval(b)
        br_on_cast!(b, 0, anyref, sref)
        @test W.stack(b)[end] == anyref
        emit!(b, :drop); emit!(b, :i32_const, -1); return!(b)
        end!(b)
        emit!(b, :struct_get, s, 0)
    end
    build(m, "cast_fail", ValType[I32], ValType[I32]) do b
        block!(b, anyref)
        anyval(b)
        br_on_cast_fail!(b, 0, anyref, sref)
        @test W.stack(b)[end] == sref
        emit!(b, :struct_get, s, 0); return!(b)
        end!(b)
        emit!(b, :drop); emit!(b, :i32_const, -1)
    end
    build(m, "non_null", ValType[I32], ValType[I32]) do b
        block!(b, sref)
        emit!(b, :local_get, 0)
        if!(b, RefType(s))
        emit!(b, :i32_const, 5); emit!(b, :struct_new, s)
        else!(b)
        emit!(b, :ref_null, s)
        end!(b)
        br_on_non_null!(b, 0)
        emit!(b, :i32_const, -2); return!(b)
        end!(b)
        emit!(b, :struct_get, s, 0)
    end
    double = build(m, "double", ValType[I32], ValType[I32]) do b
        emit!(b, :local_get, 0); emit!(b, :i32_const, 2); emit!(b, :i32_mul)
    end
    build(b -> (emit!(b, :local_get, 0); return_call!(b, double)), m, "tail", ValType[I32], ValType[I32])
    build(m, "tail_ref", ValType[I32], ValType[I32]) do b
        emit!(b, :local_get, 0); emit!(b, :ref_func, double); return_call_ref!(b, double.type)
    end
    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test node_run(bytes, "console.log(e.cast(1), e.cast(0), e.cast_fail(1), e.cast_fail(0), " *
                          "e.non_null(1), e.non_null(0), e.tail(4), e.tail_ref(5))") ==
          "7 -1 7 -1 5 -2 8 10"
    @test fails(b -> (block!(b, sref); emit!(b, :ref_null, :func); br_on_cast!(b, 0, RefType(:func), sref)), m)
    @test fails(b -> (block!(b); emit!(b, :ref_null, s); br_on_non_null!(b, 0)), m)
    @test fails(b -> (emit!(b, :i32_const, 1); return_call!(b, double)), m, ValType[], ValType[I64])
end

@testset "text format names" begin
    m = WModule()
    s = add_type!(m, StructType([FieldType(I32, true)]))
    tag = add_tag!(m, ValType[])
    f = build(b -> nothing, m, "f")
    build(m, "g", ValType[I32], ValType[I32]) do b
        block!(b)
        emit!(b, :local_get, 0); br_if!(b, 0)
        emit!(b, :local_get, 0); br_table!(b, [0, 0], 0)
        end!(b)
        block!(b)
        block!(b, exnref)
        try_table!(b, :empty, [(0, tag, 1), (3, nothing, 0)])
        end!(b)
        emit!(b, :ref_null, :exn)
        end!(b)
        emit!(b, :drop)
        end!(b)
        block!(b)
        emit!(b, :ref_null, s); br_on_null!(b, 0); emit!(b, :ref_as_non_null)
        emit!(b, :ref_test_null, s); emit!(b, :drop)
        end!(b)
        emit!(b, :struct_new_default, s); emit!(b, :drop)
        emit!(b, :ref_null, :noextern); emit!(b, :any_convert_extern); emit!(b, :drop)
        emit!(b, :ref_func, f); call_ref!(b, f.type)
        emit!(b, :local_get, 0); emit!(b, :local_get, 0); emit!(b, :i32_const, 1)
        emit!(b, :select_t, ValType[I32])
        emit!(b, :local_get, 0); emit!(b, :i32_add)
    end
    build(b -> (emit!(b, :ref_null, :exn); throw_ref!(b)), m, "h")
    build(b -> return_call!(b, f), m, "t")
    @test checkvalid(to_bytes(m))
    wat = sprint(print_wat, m)
    for name in ["br_if 0", "br_table 0 0 0", "try_table (catch \$tag0 1) (catch_all_ref 0)",
                 "block (result (ref null exn))", "i32.add", "local.get 0", "struct.new_default 0",
                 "ref.as_non_null", "any.convert_extern", "br_on_null 0", "ref.test (ref null 0)",
                 "call_ref 1", "select (result i32)", "throw_ref", "return_call \$f", "ref.func \$f"]
        @test occursin(name, wat)
    end
    for name in ["br.", "try.", "select.", "call.", "return.", "throw.", "test_null"]
        @test !occursin(name, wat)
    end
end


@testset "linear memory" begin
    m = WModule()
    load(b) = (emit!(b, :i32_const, 0); emit!(b, :i32_load, 2, 0); emit!(b, :drop))
    @test fails(load, m)                    # no memory
    mem = add_memory!(m, 1; max=2)
    @test_throws ArgumentError add_memory!(m, 1)
    @test !fails(load, m)
    @test fails(b -> (emit!(b, :i32_const, 0); emit!(b, :i32_load, 3, 0); emit!(b, :drop)), m)  # over-aligned
    @test fails(b -> (emit!(b, :i32_const, 0); emit!(b, :i64_const, 1); emit!(b, :i32_store, 2, 0)), m)
    @test fails(b -> (emit!(b, :memory_size, 1); emit!(b, :drop)), m)
    # an i64 at 24 (offset 8 from 16), a byte at 3 (offset 3 from 0), read back and added
    build(m, "rw", ValType[I64], ValType[I64]) do b
        emit!(b, :i32_const, 16); emit!(b, :local_get, 0); emit!(b, :i64_store, 3, 8)
        emit!(b, :i32_const, 0); emit!(b, :i32_const, 0x1ff); emit!(b, :i32_store8, 0, 3)
        emit!(b, :i32_const, 24); emit!(b, :i64_load, 3, 0)
        emit!(b, :i32_const, 3); emit!(b, :i64_load8_u, 0, 0)
        emit!(b, :i64_add)
    end
    build(m, "grow", ValType[], ValType[I32]) do b
        emit!(b, :i32_const, 1); emit!(b, :memory_grow, 0); emit!(b, :drop); emit!(b, :memory_size, 0)
    end
    add_export!(m, "memory", mem)
    bytes = to_bytes(m)
    @test checkvalid(bytes)
    @test node_run(bytes, "console.log(e.rw(40n), e.grow(), e.memory.buffer.byteLength, new Uint8Array(e.memory.buffer)[24])") ==
          "295n 2 131072 40"
    enc(i) = (io = IOBuffer(); W.write_inst(io, i); take!(io))
    @test enc(Inst(:i64_store, 3, 8)) == [0x37, 0x03, 0x08]
    @test enc(Inst(:memory_grow, 0)) == [0x40, 0x00]
    wat = sprint(print_wat, m)
    for s in ["(memory 1 2)", "i64.store align=8 offset=8", "i32.store8 align=1 offset=3",
              "memory.grow 0", "(export \"memory\" (memory 0))"]
        @test occursin(s, wat)
    end
    # limits, and exporting a memory not the module's
    m2 = WModule()
    add_memory!(m2, 3; max=2)
    @test_throws WasmValidationError verify(m2)
    m2.memory = W.LinearMemory(1, nothing)
    add_export!(m2, "other", W.LinearMemory(1, nothing))
    @test_throws WasmValidationError verify(m2)
end
