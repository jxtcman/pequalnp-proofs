import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25390
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [0, 6]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.or, [0, 5]⟩,
        ⟨GateOp.not, [10]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.and, [9, 11]⟩,
        ⟨GateOp.or, [8, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_25390

theorem PEqualNP.Outside.L_meta_25390 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408118 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25390.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25390.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
