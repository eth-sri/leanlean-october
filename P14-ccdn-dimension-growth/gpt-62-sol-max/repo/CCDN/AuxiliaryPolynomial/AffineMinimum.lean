/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.ScaledAffineAuxiliary
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Algebra.ScaledHomogenizationPrimitive

/-! The same two height estimates control the affine auxiliary degree for ordinary
homogenization and for prime scaling. Only the radius comparison changes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The two affine estimates share the factor `d^(4 - 1/(n+1)) B^(1/d^(1/(n+1)))`.
One uses the logarithm of the radius and the other the weighted bad-prime factor. -/
def affineAuxiliaryDegreeExpression (n d : ℕ) (B L b : ℝ) : ℝ :=
  auxDegreeScale n d * B ^ (1 / degreeRoot n d) *
    (min (1 + Real.log B / d) (b / L ^ heightExponent n d) + 2)

abbrev affineScaleConstant (n : ℕ) : ℝ :=
  max (badPrimeHeightConstant n (n + 2)) (Real.exp 1)

/-- The constant for the affine degree bound when the radius comparison has loss `A`. -/
def affineMinimumConstant (n : ℕ) (A : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n * (affineScaleConstant n * max A 1)

private lemma affineScaleConstant_one_le (n : ℕ) : 1 ≤ affineScaleConstant n :=
  (Real.one_le_exp (by norm_num)).trans (le_max_right _ _)

lemma affineMinimumConstant_one_le (n : ℕ) (A : ℝ) : 1 ≤ affineMinimumConstant n A :=
  one_le_mul_of_one_le_of_one_le (hypersurfaceAbsoluteAuxiliaryConstant_one_le n)
    (one_le_mul_of_one_le_of_one_le (affineScaleConstant_one_le n) (le_max_right _ _))

abbrev affineMinimumAuxiliaryBound (n d : ℕ) (A B L b : ℝ) : ℝ :=
  affineMinimumConstant n A * affineAuxiliaryDegreeExpression n d B L b

section

variable {n : ℕ}
  (f : MvPolynomial (Fin (n + 2)) ℤ)
include n f

/-- Using a positive integer scaling, the excess radius factor is a power of `B/a`. -/
theorem scaled_affine_auxiliary_minimum (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {a : ℤ} (ha : 1 ≤ a) (hprim : PrimitiveIntegerPolynomial (scaledHomogenize f.totalDegree a f))
    {A B : ℝ} (hB : 1 ≤ B) (haB : (a : ℝ) ≤ B)
    (hpower : (B / (a : ℝ)) ^ scaleExponent n f.totalDegree ≤ A)
    (hbad : hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree a f) ≤
      Real.exp 1 * hypersurfaceBadPrimeFactor f) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f))
        (hypersurfaceBadPrimeFactor f) := by
  have hf := hir.ne_zero
  obtain ⟨g, hg, hgdegree⟩ := scaled_affine_auxiliary f hir hd (by omega : a ≠ 0) hprim hB
    (by rwa [abs_of_nonneg (by exact_mod_cast (show 0 ≤ a by omega))])
  refine ⟨g, hg, hgdegree.trans ?_⟩
  let d := f.totalDegree
  let F := scaledHomogenize d a f
  let b := hypersurfaceBadPrimeFactor f
  let bF := hypersurfaceBadPrimeFactor F
  let H := (integerCoefficientHeight F : ℝ)
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let Y := (a : ℝ) ^ d
  let q := heightExponent n d
  let S := (a : ℝ) ^ scaleExponent n d
  let Q := B ^ (1 / degreeRoot n d)
  let E := auxDegreeScale n d
  let K := affineScaleConstant n
  let M := min (1 + Real.log B / d) (b / L ^ q)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hY : 1 ≤ Y := one_le_pow₀ ha1
  have hYH : Y * L ≤ H := scaledHomogenize_leading_height_lower f ha
  have hb := hypersurfaceBadPrimeFactor_nonneg f
  have hM : 0 ≤ M := by have := Real.log_nonneg hB; positivity
  have hK : 1 ≤ K := affineScaleConstant_one_le n
  have hS : 0 < S := by positivity
  have hYpow : Y ^ q = S := by
    dsimp only [Y, q, S, scaleExponent, heightExponent]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    congr 1
    field_simp [show (d : ℝ) ≠ 0 by positivity]
  have hcoef : bF / H ^ q * S ≤ K * M := by
    rw [show M = _ from rfl, mul_min_of_nonneg _ _ (zero_le_one.trans hK)]
    apply le_min
    · have ht := hypersurface_badPrime_height_transfer (n := n) F
        ((scaledHomogenize_homogeneous a f le_rfl).totalDegree
          (scaledHomogenize_ne_zero d (by omega : a ≠ 0) hf)) hd hY
        ((le_mul_of_one_le_right (show 0 ≤ Y by positivity) hL).trans hYH)
      change bF / H ^ q ≤ _ / Y ^ q at ht
      rw [hYpow, le_div_iff₀ hS] at ht
      have hlog : Real.log Y / (d : ℝ) ^ 2 = Real.log (a : ℝ) / d := by
        dsimp only [Y]
        rw [Real.log_pow]
        field_simp
      rw [hlog] at ht
      refine ht.trans ?_
      gcongr
      exact le_max_left _ _
    · calc
        _ ≤ Real.exp 1 * b / (Y * L) ^ q * S := by gcongr
        _ = Real.exp 1 * (b / L ^ q) := by
          rw [Real.mul_rpow (by positivity) (by positivity), hYpow]; field_simp
        _ ≤ _ := by gcongr; exact le_max_right _ _
  let J := K * max A 1
  have hJ : 1 ≤ J := one_le_mul_of_one_le_of_one_le hK (le_max_right _ _)
  have hmain : auxMainTerm n d B bF H ≤ J * (E * Q) * M := calc
    _ = E * (bF / H ^ q * S) * (B ^ boxExponent n d / S) := by
      change E * B ^ boxExponent n d * (bF / H ^ q) = _
      field_simp
    _ ≤ E * (K * M) * (Q * max A 1) := by
      rw [show B ^ boxExponent n d / S = _ from box_power_div_scale n hd ha0 (by linarith)]
      gcongr
      exact hpower.trans (le_max_left _ _)
    _ = _ := by dsimp only [J]; ring
  have hrest := (auxDegree_remainder_le (n := n) hd hB le_rfl).trans
    (le_mul_of_one_le_left (show 0 ≤ 2 * (E * Q) by positivity) hJ)
  unfold hypersurfaceAuxiliaryDegreeBound affineMinimumAuxiliaryBound affineMinimumConstant
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  change auxMainTerm n d B bF H + _ + _ ≤ J * (E * Q * (M + 2))
  linarith only [hmain, hrest]

end

end
end CCDN
