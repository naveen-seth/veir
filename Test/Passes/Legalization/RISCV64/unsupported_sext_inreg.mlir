// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %sext = "gmir.g_sext_inreg"(%x) <{sz = 7 : i64}> : (i64) -> i64
    "test.test"(%sext) : (i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Lower `g_sext_inreg` to shifts, as LLVM does.
// CHECK: unable to legalize gmir.g_sext_inreg: no legalization rule matches
