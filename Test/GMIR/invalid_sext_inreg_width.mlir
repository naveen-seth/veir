// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %x = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
  %sext = "gmir.g_sext_inreg"(%x) <{sz = 32 : i64}> : (i32) -> i32
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_sext_inreg: size must be less than the operand's width
