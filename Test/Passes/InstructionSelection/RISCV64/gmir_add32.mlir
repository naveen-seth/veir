// RUN: veir-opt %s -p=legalize-riscv64,isel-riscv64,reconcile-cast,riscv-combine,dce | filecheck %s

// An `i32` `gmir.g_add` is legalized to `g_trunc (g_sext_inreg (g_add (g_anyext a) (g_anyext b)) 32)`.
// The `i64` `g_add` only has a 32-bit user, so it is selected to `riscv.addw`, and `riscv-combine`
// drops the `sext.w` of `g_sext_inreg`.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> (), sym_name = "foo"}> ({
  ^bb0(%a: i32, %b: i32):
    %0 = "gmir.g_add"(%a, %b) : (i32, i32) -> i32
    // CHECK:      %[[A:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[ADD:.*]] = "riscv.addw"(%[[A]], %[[B]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[ADD]]) : (!riscv.reg) -> i32
    // CHECK-NOT:  "riscv.add"(
    // CHECK-NOT:  "riscv.sextw"
    "test.test"(%0) : (i32) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
