/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Positive-degree irreducible integer equations remain irreducible over Q.
Primitive denominator-cleared divisors give an elementary Gauss argument. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An irreducible integer polynomial of positive total degree remains irreducible over `ℚ`. -/
theorem rational_map_irreducible_of_integer {n : ℕ}
    (f : IntegerPolynomial n) (hir : Irreducible f) (hd : 0 < f.totalDegree) :
    Irreducible (rationalEquation f) := by
  have hdegree : (rationalEquation f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hf0 : rationalEquation f ≠ 0 := by
    aesop
  have hunit : ¬ IsUnit (rationalEquation f) := by
    intro hu
    have he := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  refine ⟨hunit, ?_⟩
  intro q r he
  by_cases hqu : IsUnit q
  grind
  by_cases hru : IsUnit r
  grind
  have hq0 : q ≠ 0 := by grind
  have hr0 : r ≠ 0 := by grind
  have hqd := totalDegree_pos_of_ne_zero_of_not_isUnit hq0 hqu
  have hrd := totalDegree_pos_of_ne_zero_of_not_isUnit hr0 hru
  obtain ⟨g, a, hgprim, ha, hmodel⟩ := exists_primitive_integer_model q hq0
  have hgdegree := rational_scalar_model_degree ha hq0 hmodel
  have hdivQ : rationalEquation g ∣ rationalEquation f := by
    aesop
  obtain ⟨u, hu⟩ := hgprim.rational_map_dvd_iff.mp hdivQ
  have hg0 : g ≠ 0 := by grind
  have hu0 : u ≠ 0 := by grind
  rcases hir.isUnit_or_isUnit hu with hgu | huu
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp hgu).2
    omega
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp huu).2
    grind [totalDegree_mul_of_isDomain, add_zero]

end
end CCDN
