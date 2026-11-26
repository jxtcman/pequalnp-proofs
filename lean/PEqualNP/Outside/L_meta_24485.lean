import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24485
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [6, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [9, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_24485

theorem PEqualNP.Outside.L_meta_24485 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114493 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24485.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24485.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
