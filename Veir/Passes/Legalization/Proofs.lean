module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_decide

/--
Prove the correctness of the custom `i32` `g_add` legalization of RISC-V 64, which sign-extends the
wide result from bit 31. `g_sext_inreg x 32` on `i64` is `sext (trunc x 32) 64`.
-/
theorem add_widening_sext_inreg_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nsw nuw : Bool) :
    LLVM.Int.add i i' nsw nuw ⊒
      LLVM.Int.trunc (LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind)) 64 (by grind)) 32 false false (by grind) := by
  veir_bv_decide

/-- The `g_sub` version of `add_widening_sext_inreg_32_64`. -/
theorem sub_widening_sext_inreg_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nsw nuw : Bool) :
    LLVM.Int.sub i i' nsw nuw ⊒
      LLVM.Int.trunc (LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.sub
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind)) 64 (by grind)) 32 false false (by grind) := by
  veir_bv_decide

end Veir.Data.LLVM

end
