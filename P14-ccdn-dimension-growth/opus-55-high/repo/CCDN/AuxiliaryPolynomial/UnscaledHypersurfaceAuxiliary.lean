/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousSlice
import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.HypersurfaceCoefficientDichotomy
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ProjectiveIntegerHeight
import CCDN.Plane.UnscaledModelCount

/-! The ordinary homogenization provides an affine auxiliary without a
scaling-prime hypothesis and transfers the coefficient-height dichotomy. -/

namespace CCDN
open MvPolynomial

section
variable {n : ℕ}

/-- The ordinary homogenization (scaling factor one) of an integer polynomial has the same
coefficient height as the polynomial. -/
lemma integerCoefficientHeight_scaledHomogenize_one (d : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    integerCoefficientHeight (scaledHomogenize d 1 f) = integerCoefficientHeight f := by
  have hupper : (integerCoefficientHeight (scaledHomogenize d 1 f) : ℝ) ≤
      integerCoefficientHeight f := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    by_cases hm : ∃ k, homogenizedExponent d k = m
    · obtain ⟨k, rfl⟩ := hm
      simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
        coefficient_abs_le_integerCoefficientHeight f k
    · have hz : (scaledHomogenize d 1 f).coeff m = 0 := by
        simp only [scaledHomogenize, coeff_sum]
        simp_all
      rw [hz, Int.cast_zero, abs_zero]
      positivity
  have hlower : (integerCoefficientHeight f : ℝ) ≤
      integerCoefficientHeight (scaledHomogenize d 1 f) := by
    apply integerCoefficientHeight_le _ (Nat.cast_nonneg _)
    intro m
    simpa [scaledHomogenize_coefficient, one_pow, one_mul] using
      coefficient_abs_le_integerCoefficientHeight (scaledHomogenize d 1 f)
        (homogenizedExponent d m)
  exact_mod_cast hupper.antisymm hlower

end

section
variable {n M : ℕ} (f : MvPolynomial (Fin n) ℤ)

/-- If a form `G` is not divisible by the ordinary homogenization of a nonzero primitive integer
polynomial `f`, then its dehomogenization at `x₀ = 1` is not divisible by `f`. -/
lemma unscaled_auxiliary_not_dvd
    (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    (G : MvPolynomial (Fin (n + 1)) ℤ) (hGhom : G.IsHomogeneous M)
    (hGnd : ¬ scaledHomogenize f.totalDegree 1 f ∣ G) :
    ¬ f ∣ homogeneousSlice n 1 G := by
  have hslice : homogeneousSlice n 1 (scaledHomogenize f.totalDegree 1 f) = f := by
    simp [homogeneousSlice_scaledHomogenize 1 f le_rfl, one_pow, map_one, one_mul]
  have hndQ := rational_homogeneousSlice_not_dvd one_ne_zero
    (scaledHomogenize_homogeneous 1 f le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    hGhom (hprim.scaledHomogenize_one _) (by grind) hGnd
  rw [hslice] at hndQ
  exact fun h => hndQ (map_dvd (map (Int.castRingHom ℚ)) h)

lemma unscaled_auxiliary_vanishes
    (G : MvPolynomial (Fin (n + 1)) ℤ)
    (hGhom : G.IsHomogeneous M) {B : ℝ} (hB : 1 ≤ B)
    (hGzero : ∀ P : ProjectivePoint n, P.mulHeight ≤ B →
      P ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (scaledHomogenize f.totalDegree 1 f)) →
      P ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) G)) :
    ∀ x : IntPoint n, InBox x B → eval x f = 0 →
      eval x (homogeneousSlice n 1 G) = 0 := by
  intro x hx hxf
  let v : IntPoint (n + 1) := Fin.cons 1 x
  have hv0 : v ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    exact one_ne_zero hh
  let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
  have hvbox (j : Fin (n + 1)) : |(v j : ℝ)| ≤ B := by
    refine Fin.cases ?_ (fun k => hx k) j
    aesop
  have hPB := projective_integer_height_le v hv0 hvbox
  have hvF : eval v (scaledHomogenize f.totalDegree 1 f) = 0 := by
    rw [scaledHomogenize_eval _ _ le_rfl, hxf, mul_zero]
  have hPF : P ∈ projectiveZeroLocus
      (map (Int.castRingHom ℚ) (scaledHomogenize f.totalDegree 1 f)) := by
    apply (mem_projectiveZeroLocus_mk ((scaledHomogenize_homogeneous 1 f le_rfl).map _) _ _).mpr
    have hh := congrArg (Int.castRingHom ℚ) hvF
    rwa [map_eval, map_zero] at hh
  have hcast := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp (hGzero P hPB hPF)
  rw [homogeneousSlice_eval]
  apply Int.cast_injective (α := ℚ)
  change (Int.castRingHom ℚ) (eval v G) = (Int.castRingHom ℚ) 0
  rwa [map_eval, map_zero]

end

variable {n : ℕ} {B : ℝ}

/-- Either the affine equation has controlled coefficient height, or a
degree-at-most-d nonmultiple vanishes on every bounded integer zero. -/
theorem affine_coefficient_height_dichotomy
    (f : MvPolynomial (Fin n) ℤ) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((n + f.totalDegree).choose f.totalDegree) +
      ((n + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree * Real.log B ∨
    ∃ g, IsBoxAuxiliary f g B ∧ g.totalDegree ≤ f.totalDegree := by
  rcases projective_coefficient_height_dichotomy (scaledHomogenize f.totalDegree 1 f)
      (scaledHomogenize_homogeneous 1 f le_rfl) (scaledHomogenize_ne_zero _ one_ne_zero hf0) hB with
    hheight | ⟨G, _, hGhom, hGzero, hGnd⟩
  · simp_all [integerCoefficientHeight_scaledHomogenize_one]
  · right
    let g := homogeneousSlice n 1 G
    have hgnd : ¬ f ∣ g := unscaled_auxiliary_not_dvd f hf0 hprim G hGhom hGnd
    exact ⟨g, ⟨fun h => hgnd (by rw [h]; exact dvd_zero _), hgnd,
      unscaled_auxiliary_vanishes f G hGhom hB hGzero⟩, homogeneousSlice_degree_le (1 : ℤ) hGhom⟩

