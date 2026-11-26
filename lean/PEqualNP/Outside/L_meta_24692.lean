import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24692
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.or, [2, 5]⟩,
        ⟨GateOp.or, [0, 6]⟩,
        ⟨GateOp.or, [7, 8]⟩,
        ⟨GateOp.or, [0, 10]⟩,
        ⟨GateOp.and, [9, 10]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.or, [12, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_24692

theorem PEqualNP.Outside.L_meta_24692 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (444 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24692.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24692.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
