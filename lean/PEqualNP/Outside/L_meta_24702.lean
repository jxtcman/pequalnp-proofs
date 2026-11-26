import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24702
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [0, 1]⟩,
        ⟨GateOp.and, [0, 2]⟩,
        ⟨GateOp.or, [5, 6]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.and, [0, 9]⟩,
        ⟨GateOp.or, [7, 10]⟩,
        ⟨GateOp.not, [12]⟩,
        ⟨GateOp.or, [11, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_24702

theorem PEqualNP.Outside.L_meta_24702 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16825 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24702.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24702.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
