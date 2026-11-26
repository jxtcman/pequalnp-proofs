import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25154
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [3, 5]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [4, 7]⟩,
        ⟨GateOp.and, [1, 8]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.or, [10, 12]⟩,
        ⟨GateOp.not, [13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_25154

theorem PEqualNP.Outside.L_meta_25154 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34634582443 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25154.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25154.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
