import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25229
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.not, [0]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [5, 7]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.or, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25229

theorem PEqualNP.Outside.L_meta_25229 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50073 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25229.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25229.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
