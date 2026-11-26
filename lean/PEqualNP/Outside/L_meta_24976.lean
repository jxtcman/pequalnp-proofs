import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24976
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.not, [1]⟩,
        ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.or, [4, 5]⟩,
        ⟨GateOp.and, [1, 9]⟩,
        ⟨GateOp.or, [8, 10]⟩,
        ⟨GateOp.not, [5]⟩,
        ⟨GateOp.and, [6, 12]⟩,
        ⟨GateOp.or, [11, 13]⟩ ],
    output := 14 }

end PEqualNP.Outside.L_meta_24976

theorem PEqualNP.Outside.L_meta_24976 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6410045 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24976.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24976.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
