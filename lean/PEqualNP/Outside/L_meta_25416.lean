import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25416
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.and, [5, 5]⟩,
        ⟨GateOp.not, [3]⟩,
        ⟨GateOp.and, [7, 9]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [3, 12]⟩,
        ⟨GateOp.or, [10, 13]⟩,
        ⟨GateOp.or, [14, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25416

theorem PEqualNP.Outside.L_meta_25416 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6507959 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25416.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25416.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
