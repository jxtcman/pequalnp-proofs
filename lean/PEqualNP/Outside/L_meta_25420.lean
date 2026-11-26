import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25420
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.or, [3, 7]⟩,
        ⟨GateOp.or, [2, 9]⟩,
        ⟨GateOp.or, [4, 6]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [3, 13]⟩,
        ⟨GateOp.and, [12, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25420

theorem PEqualNP.Outside.L_meta_25420 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6508348 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25420.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25420.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
