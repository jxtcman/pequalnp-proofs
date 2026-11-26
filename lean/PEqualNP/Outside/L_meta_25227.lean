import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25227
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.not, [0]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.or, [6, 8]⟩,
        ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.or, [0, 12]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.and, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25227

theorem PEqualNP.Outside.L_meta_25227 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (49840 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25227.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25227.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
