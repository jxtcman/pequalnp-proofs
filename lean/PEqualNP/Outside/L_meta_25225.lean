import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25225
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.not, [4]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.and, [2, 9]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [10, 12]⟩,
        ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.and, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25225

theorem PEqualNP.Outside.L_meta_25225 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (49819 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25225.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25225.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
