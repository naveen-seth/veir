module

public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.PatternRewriter.Puddle.Builders

public section

/-! This file contains Puddle matcher fragments for legal GMIR operations. -/

namespace Veir

/--
Puddle matcher for a binary `opcode` operation (`g_add`, `g_sub`) that is legal according to `info`.
-/
def matchLegalBinop (info : LegalizerInfo) (opcode : GMIR) :
    Puddle.MatchProg.Builder
      (Puddle.Handle OpCode .type × Puddle.Handle OpCode .value × Puddle.Handle OpCode .value) := do
  let type ← Puddle.MatchProg.type (Attr := TypeAttr)
  let lhs ← Puddle.MatchProg.value type
  let rhs ← Puddle.MatchProg.value type
  let root ← Puddle.MatchProg.root (.gmir opcode) #[lhs, rhs] #[type]
  Puddle.MatchProg.matchNative (root.properties, type) fun (props, type) =>
    info.isLegal opcode props #[type] #[type, type]
  return (type, lhs, rhs)

end Veir
