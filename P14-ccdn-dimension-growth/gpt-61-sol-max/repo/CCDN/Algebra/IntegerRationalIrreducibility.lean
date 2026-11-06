/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Positive-degree irreducible integer equations remain irreducible over Q.
Primitive denominator-cleared divisors give an elementary Gauss argument. -/

public section
namespace CCDN
open MvPolynomial

/-- An irreducible integer polynomial of positive total degree remains irreducible over `ℚ`. -/
theorem rational_map_irreducible_of_integer {n : ℕ}
    (f : CCDN.IntegerPolynomial n) (hir : Irreducible f) (hd : 0 < f.totalDegree) :
    Irreducible (CCDN.rationalPolynomial f) := by
  have hdegree : (CCDN.rationalPolynomial f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  have hf0 : CCDN.rationalPolynomial f ≠ 0 := by
    aesop
  have hunit : ¬ IsUnit (CCDN.rationalPolynomial f) := by
    intro hu
    have he := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hdegree] at he
    omega
  refine ⟨hunit, ?_⟩
  intro q r he
  by_cases hqu : IsUnit q
  · exact Or.inl hqu
  by_cases hru : IsUnit r
  · exact Or.inr hru
  have hq0 : q ≠ 0 := fun hh => hf0 (by simp [he, hh])
  have hr0 : r ≠ 0 := fun hh => hf0 (by simp [he, hh])
  have hqd := totalDegree_pos_of_ne_zero_of_not_isUnit hq0 hqu
  have hrd := totalDegree_pos_of_ne_zero_of_not_isUnit hr0 hru
  have hsum : q.totalDegree + r.totalDegree = f.totalDegree := by
    simp_all [totalDegree_mul_of_isDomain]
  obtain ⟨g, a, hgprim, ha, hmodel⟩ := exists_primitive_integer_model q hq0
  have hgdegree := rational_scalar_model_degree ha hq0 hmodel
  have hdivQ : CCDN.rationalPolynomial g ∣ CCDN.rationalPolynomial f := by
    simp_all
  obtain ⟨u, hu⟩ := hgprim.rational_map_dvd_iff.mp hdivQ
  have hu0 : u ≠ 0 := fun hh => hir.ne_zero (by simp [hu, hh])
  rcases hir.isUnit_or_isUnit hu with hgu | huu
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp hgu).2
    rw [hgdegree] at hh
    omega
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp huu).2
    have hedeg : f.totalDegree = g.totalDegree + u.totalDegree := by
      grind [totalDegree_mul_of_isDomain]
    rw [hgdegree, hh, add_zero] at hedeg
    omega

end CCDN
