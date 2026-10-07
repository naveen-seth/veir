// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %sext = "gmir.g_sext_inreg"(%x) <{sz = 0 : i64}> : (i64) -> i64
}) : () -> ()

// CHECK: Error verifying input program: gmir.g_sext_inreg: size must be at least 1
