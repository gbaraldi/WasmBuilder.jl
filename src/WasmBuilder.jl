"""
    WasmBuilder

Building WebAssembly modules (with the GC, function references, exception handling and
multi-value proposals) in Julia, as LLVM.jl does for LLVM IR: types, modules, a builder
that validates instructions as they are emitted, the binary format and a text printer.
"""
module WasmBuilder

export NumType, I32, I64, F32, F64, V128, PackedType, I8, I16, TypeRef, RefType, ValType,
       FieldType, FuncType, StructType, ArrayType, SubType, HeapType,
       Inst, Func, Global, Tag, LinearMemory, WModule,
       add_type!, typedef, functype!, add_func!, add_import!, add_global!, add_tag!,
       add_memory!, add_data!, add_export!, add_local!, local_type, to_bytes,
       Builder, emit!, block!, loop!, if!, else!, end!, finish!, br!, br_if!, br_table!,
       br_on_null!, br_on_non_null!, br_on_cast!, br_on_cast_fail!, return!, unreachable!,
       throw!, throw_ref!, try_table!, call!, call_ref!, return_call!, return_call_ref!,
       blocktype, is_unreachable, subtype, heap_subtype, WasmValidationError, verify,
       print_wat, validate, disassemble

include("types.jl")
include("module.jl")
include("subtyping.jl")
include("instructions.jl")
include("builder.jl")
include("verify.jl")
include("encode.jl")
include("print.jl")
include("tools.jl")

end
