# WasmBuilder.jl

[![CI](https://github.com/gbaraldi/WasmBuilder.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/gbaraldi/WasmBuilder.jl/actions/workflows/CI.yml)

A Julia library for building WebAssembly modules, as LLVM.jl is for LLVM IR: types,
functions, globals and instructions as Julia objects, a builder that validates every
instruction as it is appended, and an encoder to the binary format. It covers what a
compiler for a garbage-collected language targets:

- the GC proposal: structs, arrays, subtyping, `ref.test`/`ref.cast`, `i31`;
- typed function references, multi-value;
- exception handling (the `exnref` version: `try_table`, `throw`, `throw_ref`);
- passive data segments (`array.new_data`, `array.init_data`), start functions.

It has no dependencies and does not need an external toolchain. If `wasm-tools` is
installed, `validate` and `disassemble` use it for a second opinion. The first user is
[WasmCodegen.jl](https://github.com/gbaraldi/WasmCodegen.jl), a Julia-to-WasmGC compiler.

## Example

```julia
using WasmBuilder

m = WModule()
# a struct type: an immutable i32 tag and a mutable f64
point = add_type!(m, StructType([FieldType(I32, false), FieldType(F64, true)]))

# build a point, scale its field, read it back
f = add_func!(m, "scaled", ValType[F64, F64], ValType[F64])
p = add_local!(f, RefType(point))
b = Builder(m, f)               # validates every instruction as it is appended
emit!(b, :i32_const, 1)
emit!(b, :local_get, 0)
emit!(b, :struct_new, point)
emit!(b, :local_set, p)
emit!(b, :local_get, p)
emit!(b, :local_get, p); emit!(b, :struct_get, point, 1)
emit!(b, :local_get, 1); emit!(b, :f64_mul)
emit!(b, :struct_set, point, 1)
emit!(b, :local_get, p); emit!(b, :struct_get, point, 1)
finish!(b)
add_export!(m, "scaled", f)

bytes = to_bytes(m)             # verifies the module, then encodes it
print_wat(stdout, m)            # the text format
validate(bytes)                 # wasm-tools, if it is installed
```

A mistake is reported where the code generator makes it, with its backtrace, rather than
as a byte offset from an engine:

```julia
emit!(b, :f64_const, 1.0)
emit!(b, :i32_eqz)
# WasmValidationError in function bad at instruction 2 (i32_eqz): expected I32, got F64
```

## Design

- **Nominal types.** Type definitions are in one recursion group, so two struct types
  with the same fields are distinct types, as a source language's types need to be. Function
  types of numbers and abstract references made by `functype!` are recursion groups of their
  own, so that imports match the functions a host or another module provides.
- **Items, not indices.** Instructions refer to functions, globals and tags as objects.
  Indices are assigned when the module is written, so imports can be added at any point of
  code generation.
- **One instruction table** (`src/instructions.jl`) drives encoding, printing and
  validation.
- **Validation in two parts.** `Builder` checks each instruction against an operand stack
  and control frames, as the specification's validation algorithm does, including
  initialization of non-defaultable locals. `verify(m)` checks the rest: type definitions,
  constant expressions of globals, tags, exports, the start function.

See [DESIGN.md](DESIGN.md) for details, and what is not covered yet (tables and
`call_indirect`, linear memory, SIMD).

## Tests

`Pkg.test()` runs the modules it builds in Node.js 24 (from `NodeJS_24_jll`). It also
validates them with `wasm-tools` when it is on the `PATH`, in `~/.cargo/bin`, or named by
`WASM_TOOLS`.
