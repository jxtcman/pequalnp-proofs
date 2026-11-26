import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24591
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [3, 6]⟩,
        ⟨GateOp.and, [4, 7]⟩,
        ⟨GateOp.or, [5, 8]⟩,
        ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [9, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [0, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_24591

theorem PEqualNP.Outside.L_meta_24591 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549951 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24591.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24591.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
