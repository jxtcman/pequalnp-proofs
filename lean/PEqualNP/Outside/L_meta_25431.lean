import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25431
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.not, [6]⟩,
        ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [1, 9]⟩,
        ⟨GateOp.and, [7, 11]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [8, 12]⟩,
        ⟨GateOp.and, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25431

theorem PEqualNP.Outside.L_meta_25431 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (14897085 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25431.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25431.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
