import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20801
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [4, 3]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.or, [8, 10]⟩,
        ⟨GateOp.or, [0, 11]⟩ ],
    output := 12 }

end PEqualNP.Outside.L_meta_20801

theorem PEqualNP.Outside.L_meta_20801 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_20801.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20801.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
