// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %sext = "gmir.g_sext_inreg"(%x) <{sz = 32 : i64}> : (i64) -> i64
}) : () -> ()

// CHECK: "gmir.g_sext_inreg"(%{{.*}}) <{"sz" = 32 : i64}> : (i64) -> i64
