import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25402
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.and, [2, 5]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [0, 9]⟩,
        ⟨GateOp.or, [0, 8]⟩,
        ⟨GateOp.and, [10, 12]⟩,
        ⟨GateOp.not, [13]⟩,
        ⟨GateOp.and, [11, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25402

theorem PEqualNP.Outside.L_meta_25402 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409655 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25402.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25402.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
