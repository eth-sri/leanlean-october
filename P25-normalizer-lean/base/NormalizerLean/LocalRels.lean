module

public import NormalizerLean.RelBasic

@[expose] public section

/-!
# The local relations hold: `localRels_mem_Gamma0`

Computed with w ↦ the Fricke element and s ↦ S_h, then transferred to an arbitrary Atkin–Lehner
element by `lift_mem_iff_of_cosets`.  The integer matrices below were computed exactly in sympy
(`(14)` is proved symbolically in `RelBasic.lean`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- Tactic for the numerical cases: evaluate the word as a product of explicit rational matrices. -/
macro "rel_compute" a:term:max b:term:max c:term:max d:term:max hs:term:max : tactic =>
  `(tactic| (
    simp only [bracket, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, locF]
    refine mem_Gamma0R_of_entries $a $b $c $d ?_ (by norm_num)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_pow, coe_S]
    rw [$hs:term]
    norm_num [adjugate_fin_two_of, mul_fin_two, pow_succ]))

end

end NormalizerLean
