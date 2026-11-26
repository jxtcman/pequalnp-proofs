import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25435
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [4, 2]⟩,
        ⟨GateOp.not, [2]⟩,
        ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.and, [9, 7]⟩,
        ⟨GateOp.or, [5, 11]⟩,
        ⟨GateOp.and, [6, 10]⟩,
        ⟨GateOp.or, [13, 12]⟩,
        ⟨GateOp.not, [14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25435

theorem PEqualNP.Outside.L_meta_25435 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549387 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25435.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25435.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
