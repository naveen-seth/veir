// RUN: veir-opt %s -p=legalize-riscv64,isel-riscv64,reconcile-cast,riscv-combine,dce | filecheck %s

// Like `gmir_add32.mlir`: an `i32` `g_sub` is selected to a single `riscv.subw`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %lhs = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %rhs = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %sub = "gmir.g_sub"(%lhs, %rhs) : (i32, i32) -> i32
    // CHECK:     "riscv.subw"({{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NOT: "riscv.sextw"
    "test.test"(%sub) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
