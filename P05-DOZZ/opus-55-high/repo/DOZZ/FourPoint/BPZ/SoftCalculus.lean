/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic

/-! # Calculus of the softened distance factor

For `a ε : ℝ` and `x : ℂ` the softened distance factor `z ↦ (|x - z|² + ε²)^a` is a smooth
function of `z`, viewed as a point of the real two-dimensional space `ℂ`, wherever
`N = |x - z|² + ε²` is positive. We record its first and second real derivatives as the
continuous (multi)linear maps `bpzSoftDeriv` and `bpzSoftDeriv2`, prove the derivative
formulas and the operator-norm bounds, compute the Wirtinger combinations of the derivatives
(which at `ε = 0` become the meromorphic expressions `a |x - z|^{2a} / (z - x)` and
`a (a - 1) |x - z|^{2a} / (z - x)²`), and prove joint continuity in `(ε, z)`. -/

@[expose] public section

open Complex
open scoped ComplexConjugate

namespace DOZZ.Proofs

/-- The real `z`-derivative of `(|x − z|² + ε²)^a`: `h ↦ −2a N^{a−1} ⟨x − z, h⟩`. -/
noncomputable def bpzSoftDeriv (a ε : ℝ) (x z : ℂ) : ℂ →L[ℝ] ℝ :=
  (-2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)) • innerSL ℝ (x - z)

/-- The second real `z`-derivative:
`(h, k) ↦ 4a(a−1) N^{a−2} ⟨x−z,h⟩⟨x−z,k⟩ + 2a N^{a−1} ⟨h,k⟩`.

The last term is the real inner product viewed as an `ℝ`-bilinear map; the `id` records the
(definitional) identification of `innerSL ℝ`, a map that is conjugate-linear over the trivially
conjugated `ℝ`, with an ordinary bilinear map. -/
noncomputable def bpzSoftDeriv2 (a ε : ℝ) (x z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (4 * a * (a - 1) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 2)) •
      (innerSL ℝ (x - z)).smulRight (innerSL ℝ (x - z)) +
    (2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1)) •
      (id (innerSL ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)

/-! ### Coordinates -/

/-- The real inner product on `ℂ` in coordinates. -/
theorem bpzSoft_innerSL_apply (u h : ℂ) : innerSL ℝ u h = u.re * h.re + u.im * h.im := by
  rw [innerSL_apply_apply, Complex.inner]
  simp
  ring

/-- The bilinear form `id (innerSL ℝ)` used in `bpzSoftDeriv2`, in coordinates. -/
theorem bpzSoft_innerBilin_apply (h k : ℂ) :
    (id (innerSL ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) h k = h.re * k.re + h.im * k.im :=
  bpzSoft_innerSL_apply h k

/-- Cauchy–Schwarz for the real inner product on `ℂ`, in coordinates. -/
theorem bpzSoft_abs_inner_le (u h : ℂ) : |u.re * h.re + u.im * h.im| ≤ ‖u‖ * ‖h‖ := by
  rw [← bpzSoft_innerSL_apply, innerSL_apply_apply]
  exact abs_real_inner_le_norm u h

/-- The softened base `|x - z|² + ε²` is nonnegative. -/
theorem bpzSoft_normSq_add_nonneg (ε : ℝ) (u : ℂ) : 0 ≤ Complex.normSq u + ε ^ 2 :=
  add_nonneg (Complex.normSq_nonneg u) (sq_nonneg ε)
section
variable (a ε : ℝ)

/-- The first derivative in coordinates. -/
theorem bpzSoftDeriv_apply (x z h : ℂ) :
    bpzSoftDeriv a ε x z h =
      -2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) *
        ((x - z).re * h.re + (x - z).im * h.im) := by
  simp only [bpzSoftDeriv, smul_apply, smul_eq_mul, bpzSoft_innerSL_apply]
section
variable (x z h k : ℂ)

/-- The second derivative in coordinates. -/
theorem bpzSoftDeriv2_apply :
    bpzSoftDeriv2 a ε x z h k =
      4 * a * (a - 1) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 2) *
          (((x - z).re * h.re + (x - z).im * h.im) * ((x - z).re * k.re + (x - z).im * k.im)) +
        2 * a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) * (h.re * k.re + h.im * k.im) := by
  simp only [bpzSoftDeriv2, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, bpzSoft_innerBilin_apply,
    bpzSoft_innerSL_apply]

/-- The second derivative is a symmetric bilinear form. -/
theorem bpzSoftDeriv2_symm :
    bpzSoftDeriv2 a ε x z h k = bpzSoftDeriv2 a ε x z k h := by
  rw [bpzSoftDeriv2_apply, bpzSoftDeriv2_apply]
  ring

end

end

/-! ### Derivatives -/

/-- The derivative of the softened base `z ↦ |x - z|² + ε²`. -/
theorem bpzSoft_hasFDerivAt_base (ε : ℝ) (x z : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.normSq (x - w) + ε ^ 2)
      ((-2 : ℝ) • innerSL ℝ (x - z)) z := by
  have h1 : HasFDerivAt (fun w : ℂ => x - w) (-(ContinuousLinearMap.id ℝ ℂ)) z :=
    (hasFDerivAt_id z).const_sub x
  have e : (fun w : ℂ => Complex.normSq (x - w) + ε ^ 2) = fun w : ℂ => ‖x - w‖ ^ 2 + ε ^ 2 := by
    funext w
    rw [Complex.normSq_eq_norm_sq]
  rw [e]
  refine ((h1.norm_sq).add_const _).congr_fderiv ?_
  ext h
  simp
  ring
section
variable (a ε : ℝ) (x z : ℂ)
section
variable (hN : 0 < Complex.normSq (x - z) + ε ^ 2)
include hN

/-- `bpzSoftDeriv` is the `z`-derivative of `z ↦ (|x - z|² + ε²)^a` where `N > 0`. -/
theorem hasFDerivAt_bpzSoft :
    HasFDerivAt (fun w : ℂ => (Complex.normSq (x - w) + ε ^ 2) ^ a) (bpzSoftDeriv a ε x z) z := by
  refine ((bpzSoft_hasFDerivAt_base ε x z).rpow_const (Or.inl hN.ne')).congr_fderiv ?_
  ext h
  simp only [bpzSoftDeriv_apply, smul_apply, smul_eq_mul,
    bpzSoft_innerSL_apply]
  ring

/-- `bpzSoftDeriv2` is the `z`-derivative of `bpzSoftDeriv` where `N > 0`. -/
theorem hasFDerivAt_bpzSoftDeriv :
    HasFDerivAt (fun w : ℂ => bpzSoftDeriv a ε x w) (bpzSoftDeriv2 a ε x z) z := by
  have hc : HasFDerivAt (fun w : ℂ => -2 * a * (Complex.normSq (x - w) + ε ^ 2) ^ (a - 1))
      ((4 * a * (a - 1) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 2)) • innerSL ℝ (x - z)) z := by
    refine (((bpzSoft_hasFDerivAt_base ε x z).rpow_const (p := a - 1)
      (Or.inl hN.ne')).const_mul _).congr_fderiv ?_
    ext h
    have e : a - 1 - 1 = a - 2 := by ring
    simp only [e, smul_apply, smul_eq_mul, bpzSoft_innerSL_apply]
    ring
  have hL : HasFDerivAt (fun w => innerSL ℝ (x - w))
      ((id (innerSL ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).comp _) z :=
    (id (innerSL ℝ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_sub x)
  refine (hc.smul hL).congr_fderiv ?_
  ext h k
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.id_apply, bpzSoftDeriv2_apply, bpzSoft_innerBilin_apply,
    map_neg, smul_eq_mul, bpzSoft_innerSL_apply, neg_mul, mul_neg]
  ring

end

/-! ### Norm bounds -/

/-- Operator-norm bound on the first derivative. -/
theorem norm_bpzSoftDeriv_le :
    ‖bpzSoftDeriv a ε x z‖ ≤ 2 * |a| * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) * ‖x - z‖ := by
  have hp : 0 ≤ (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) :=
    Real.rpow_nonneg (bpzSoft_normSq_add_nonneg ε _) _
  unfold bpzSoftDeriv
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hp]
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]

/-- Operator-norm bound on the second derivative: the factor `|x - z|² ≤ N` absorbs one power
of `N`. -/
theorem norm_bpzSoftDeriv2_le (hN : 0 < Complex.normSq (x - z) + ε ^ 2) :
    ‖bpzSoftDeriv2 a ε x z‖ ≤
      (4 * |a * (a - 1)| + 2 * |a|) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) := by
  set N := Complex.normSq _ + ε ^ 2
  have hP : 0 ≤ N ^ (a - 2) := Real.rpow_nonneg hN.le _
  have hQ : N ^ (a - 1) = N ^ (a - 2) * N := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add hN, Real.rpow_one]
  have hu : ‖x - z‖ ^ 2 ≤ N := by
    rw [← Complex.normSq_eq_norm_sq]
    exact le_add_of_nonneg_right (sq_nonneg ε)
  have hQ0 : 0 ≤ N ^ (a - 1) := Real.rpow_nonneg hN.le _
  have hM : 0 ≤ (4 * |a * (a - 1)| + 2 * |a|) * N ^ (a - 1) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun h => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
  rw [bpzSoftDeriv2_apply, Real.norm_eq_abs]
  have hhk := bpzSoft_abs_inner_le h k
  have hnh := norm_nonneg h
  have hnk := norm_nonneg k
  have hnu : 0 ≤ ‖x - z‖ := norm_nonneg _
  have habs1 : |4 * a * (a - 1) * N ^ (a - 2)| = 4 * |a * (a - 1)| * N ^ (a - 2) := by
    rw [mul_assoc 4 a _, abs_mul, abs_mul, abs_of_nonneg hP]
    norm_num
  have habs2 : |2 * a * N ^ (a - 1)| = 2 * |a| * N ^ (a - 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hQ0]
    norm_num
  have hprod : |((x - z).re * h.re + (x - z).im * h.im) *
        ((x - z).re * k.re + (x - z).im * k.im)| ≤ ‖x - z‖ ^ 2 * (‖h‖ * ‖k‖) := by
    rw [abs_mul]
    calc |(x - z).re * h.re + (x - z).im * h.im| * |(x - z).re * k.re + (x - z).im * k.im|
        ≤ (‖x - z‖ * ‖h‖) * (‖x - z‖ * ‖k‖) :=
          mul_le_mul (bpzSoft_abs_inner_le (x - z) h) (bpzSoft_abs_inner_le (x - z) k) (abs_nonneg _) (mul_nonneg hnu hnh)
      _ = ‖x - z‖ ^ 2 * (‖h‖ * ‖k‖) := by ring
  calc |4 * a * (a - 1) * N ^ (a - 2) *
          (((x - z).re * h.re + (x - z).im * h.im) * ((x - z).re * k.re + (x - z).im * k.im)) +
        2 * a * N ^ (a - 1) * (h.re * k.re + h.im * k.im)|
      ≤ |4 * a * (a - 1) * N ^ (a - 2) *
          (((x - z).re * h.re + (x - z).im * h.im) * ((x - z).re * k.re + (x - z).im * k.im))| +
        |2 * a * N ^ (a - 1) * (h.re * k.re + h.im * k.im)| := abs_add_le ..
    _ = (4 * |a * (a - 1)| * N ^ (a - 2)) *
          |((x - z).re * h.re + (x - z).im * h.im) * ((x - z).re * k.re + (x - z).im * k.im)| +
        (2 * |a| * N ^ (a - 1)) * |h.re * k.re + h.im * k.im| := by
      rw [abs_mul, abs_mul (2 * a * N ^ (a - 1)), habs1, habs2]
    _ ≤ (4 * |a * (a - 1)| * N ^ (a - 2)) * (‖x - z‖ ^ 2 * (‖h‖ * ‖k‖)) +
        (2 * |a| * N ^ (a - 1)) * (‖h‖ * ‖k‖) := by
      gcongr
    _ ≤ (4 * |a * (a - 1)| * N ^ (a - 2)) * (N * (‖h‖ * ‖k‖)) +
        (2 * |a| * N ^ (a - 1)) * (‖h‖ * ‖k‖) := by
      gcongr
    _ = (4 * |a * (a - 1)| + 2 * |a|) * N ^ (a - 1) * ‖h‖ * ‖k‖ := by
      rw [hQ]
      ring

/-! ### Wirtinger derivatives -/

/-- Wirtinger form of the first derivative. -/
theorem bpzSoftDeriv_wirtinger :
    ((bpzSoftDeriv a ε x z 1 : ℂ) - Complex.I * (bpzSoftDeriv a ε x z Complex.I : ℂ)) / 2 =
      -((a * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 1) : ℝ) : ℂ) * conj (x - z) := by
  rw [bpzSoftDeriv_apply, bpzSoftDeriv_apply]
  apply Complex.ext <;> simp <;> ring

/-- Wirtinger form of the second derivative. -/
theorem bpzSoftDeriv2_wirtinger :
    ((bpzSoftDeriv2 a ε x z 1 1 : ℂ) - 2 * Complex.I * (bpzSoftDeriv2 a ε x z 1 Complex.I : ℂ) -
        (bpzSoftDeriv2 a ε x z Complex.I Complex.I : ℂ)) / 4 =
      ((a * (a - 1) * (Complex.normSq (x - z) + ε ^ 2) ^ (a - 2) : ℝ) : ℂ) * conj (x - z) ^ 2 := by
  rw [bpzSoftDeriv2_apply, bpzSoftDeriv2_apply, bpzSoftDeriv2_apply]
  apply Complex.ext <;> simp [pow_two] <;> ring

end
section
variable (a : ℝ)
section
variable {x z : ℂ}
section
variable (hxz : x ≠ z)
include hxz

/-- At `ε = 0` and `x ≠ z` the Wirtinger derivatives are the meromorphic expressions. -/
theorem bpzSoftDeriv_wirtinger_zero :
    ((bpzSoftDeriv a 0 x z 1 : ℂ) - Complex.I * (bpzSoftDeriv a 0 x z Complex.I : ℂ)) / 2 =
      ((a * Complex.normSq (x - z) ^ a : ℝ) : ℂ) / (z - x) := by
  rw [bpzSoftDeriv_wirtinger]
  have hu := sub_ne_zero.mpr hxz
  have hz : (z - x : ℂ) = -(x - z) := by ring
  have hc : conj (x - z) ≠ 0 := (map_ne_zero _).mpr hu
  have hNc : ((Complex.normSq (x - z) : ℝ) : ℂ) = (x - z) * conj (x - z) :=
    (Complex.mul_conj _).symm
  have hpow :=
    Real.rpow_sub_one (Complex.normSq_pos.mpr hu).ne' a
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [hpow, hz]
  push_cast
  rw [hNc]
  field_simp

/-- Second-order version of `bpzSoftDeriv_wirtinger_zero`. -/
theorem bpzSoftDeriv2_wirtinger_zero :
    ((bpzSoftDeriv2 a 0 x z 1 1 : ℂ) - 2 * Complex.I * (bpzSoftDeriv2 a 0 x z 1 Complex.I : ℂ) -
        (bpzSoftDeriv2 a 0 x z Complex.I Complex.I : ℂ)) / 4 =
      ((a * (a - 1) * Complex.normSq (x - z) ^ a : ℝ) : ℂ) / (z - x) ^ 2 := by
  rw [bpzSoftDeriv2_wirtinger]
  have hu := sub_ne_zero.mpr hxz
  have hz : (z - x : ℂ) = -(x - z) := by ring
  have hc : conj (x - z) ≠ 0 := (map_ne_zero _).mpr hu
  have hNc : ((Complex.normSq (x - z) : ℝ) : ℂ) = (x - z) * conj (x - z) :=
    (Complex.mul_conj _).symm
  have hpow : Complex.normSq (x - z) ^ (a - 2) =
      Complex.normSq (x - z) ^ a / Complex.normSq (x - z) ^ 2 := by
    rw [Real.rpow_sub (Complex.normSq_pos.mpr hu), Real.rpow_two]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [hpow, hz]
  push_cast
  rw [hNc]
  field_simp

end

end
section
variable (x : ℂ) {ε₀ : ℝ} {z₀ : ℂ}
section
variable (hN : 0 < Complex.normSq (x - z₀) + ε₀ ^ 2)
include hN

/-! ### Joint continuity in `(ε, z)` -/

/-- Joint continuity in `(ε, z)` where `N > 0`. -/
theorem continuousAt_bpzSoftDeriv :
    ContinuousAt (fun p : ℝ × ℂ => bpzSoftDeriv a p.1 x p.2) (ε₀, z₀) := by
  have hbase : ContinuousAt (fun p => Complex.normSq (x - p.2) + p.1 ^ 2) (ε₀, z₀) := by
    fun_prop
  have hc : ContinuousAt
      (fun p => -2 * a * (Complex.normSq (x - p.2) + p.1 ^ 2) ^ (a - 1)) (ε₀, z₀) :=
    continuousAt_const.mul (hbase.rpow_const (Or.inl hN.ne'))
  have hL : Continuous (fun p : ℝ × ℂ => innerSL ℝ (x - p.2)) :=
    (innerSL ℝ).continuous.comp (continuous_const.sub continuous_snd)
  exact hc.smul hL.continuousAt

/-- Joint continuity in `(ε, z)` of the second derivative where `N > 0`. -/
theorem continuousAt_bpzSoftDeriv2 :
    ContinuousAt (fun p : ℝ × ℂ => bpzSoftDeriv2 a p.1 x p.2) (ε₀, z₀) := by
  have hbase : ContinuousAt (fun p => Complex.normSq (x - p.2) + p.1 ^ 2) (ε₀, z₀) := by
    fun_prop
  have hc2 : ContinuousAt
      (fun p => 4 * a * (a - 1) * (Complex.normSq (x - p.2) + p.1 ^ 2) ^ (a - 2))
      (ε₀, z₀) :=
    continuousAt_const.mul (hbase.rpow_const (Or.inl hN.ne'))
  have hc1 : ContinuousAt
      (fun p => 2 * a * (Complex.normSq (x - p.2) + p.1 ^ 2) ^ (a - 1)) (ε₀, z₀) :=
    continuousAt_const.mul (hbase.rpow_const (Or.inl hN.ne'))
  have hL : Continuous (fun p : ℝ × ℂ => innerSL ℝ (x - p.2)) :=
    (innerSL ℝ).continuous.comp (continuous_const.sub continuous_snd)
  have hS :=
    (ContinuousLinearMap.smulRightL ℝ ℂ _).continuous₂.comp₂ hL hL
  exact (hc2.smul hS.continuousAt).add (hc1.smul continuousAt_const)

end

end

end

end DOZZ.Proofs
