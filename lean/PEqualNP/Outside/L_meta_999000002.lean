import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_999000002
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [0, 3]⟩,
        ⟨GateOp.and, [4, 5]⟩ ],
    output := 6 }

end PEqualNP.Outside.L_meta_999000002

theorem PEqualNP.Outside.L_meta_999000002 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin 2 => (9 : ℕ).testBit (2 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_999000002.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_999000002.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
