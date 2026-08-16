// TODO: Use MLIR-ROUNDTRIP once upstream supports shift operations on llvm.byte.
// RUN: veir-opt %s | filecheck %s

// Check that the shift amount may either be of the same type as the result, or a llvm.byte of the
// same width. (See OperationPtr.IsVerifiedLLVMShift)
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %0 = "llvm.mlir.poison"() : () -> !llvm.byte<64>
    %1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %2 = "llvm.mlir.constant"() <{ "value" = 42 : i64 }> : () -> i64
    %3 = "llvm.shl"(%0, %1) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    %4 = "llvm.lshr"(%0, %1) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    %5 = "llvm.ashr"(%0, %1) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    %6 = "llvm.shl"(%2, %1) : (i64, i64) -> i64
    %7 = "llvm.lshr"(%2, %1) : (i64, i64) -> i64
    %8 = "llvm.ashr"(%2, %1) : (i64, i64) -> i64
    "llvm.return"(%6) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.shl"(%{{.*}}, %{{.*}}) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
// CHECK: "llvm.lshr"(%{{.*}}, %{{.*}}) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
// CHECK: "llvm.ashr"(%{{.*}}, %{{.*}}) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
// CHECK: "llvm.shl"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK: "llvm.lshr"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
// CHECK: "llvm.ashr"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
