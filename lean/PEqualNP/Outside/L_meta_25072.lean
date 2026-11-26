import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25072
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 3]⟩,
        ⟨GateOp.or, [0, 1]⟩,
        ⟨GateOp.or, [1, 5]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.and, [5, 7]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.or, [11, 12]⟩,
        ⟨GateOp.or, [6, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_25072

theorem PEqualNP.Outside.L_meta_25072 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649917 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25072.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25072.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
