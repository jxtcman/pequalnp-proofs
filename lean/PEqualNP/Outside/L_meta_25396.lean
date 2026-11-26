import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25396
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 2]⟩,
        ⟨GateOp.and, [3, 0]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [5, 1]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.not, [8]⟩,
        ⟨GateOp.and, [10, 6]⟩,
        ⟨GateOp.and, [11, 1]⟩,
        ⟨GateOp.or, [0, 13]⟩,
        ⟨GateOp.or, [12, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25396

theorem PEqualNP.Outside.L_meta_25396 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408639 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25396.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25396.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
