/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RealSecondParent
public import DOZZ.Hypergeom.Planar.TaylorIntegral
public import DOZZ.Hypergeom.Planar.DifferenceIntegral
public import DOZZ.Hypergeom.Planar.RieszNormalization
public import DOZZ.Hypergeom.Planar.DerivativeIntegrable
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! The pure Wirtinger integral follows from the real second derivative and the mixed Riesz
convolution. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

private theorem continuousAt_realGamma_of_pos (x : ℝ) (hx : 0 < x) :
    ContinuousAt Real.Gamma x := by
  have hnoPole : ∀ m : ℕ, x ≠ -(m : ℂ) := by
    intro m hm
    have hxEq : x = -(m : ℝ) := by exact_mod_cast hm
    linarith
  have hGamma : ContinuousAt (fun y : ℝ => Complex.Gamma (y : ℂ)) x :=
    (Complex.continuousAt_Gamma (x : ℂ) hnoPole).comp
      Complex.continuous_ofReal.continuousAt
  exact Complex.continuous_re.continuousAt.comp hGamma

private noncomputable def planarRieszCoefficientReal (k β : ℝ) : ℝ :=
  ((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
    (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
      Real.Gamma ((β - k) / 2) /
        (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
          Real.Gamma (1 + (k - β) / 2)))

private noncomputable def planarWirtingerTargetReal (k β : ℝ) : ℝ :=
  ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
    planarRieszCoefficientReal k β

private theorem planarWirtingerKernel_reflection (k β : ℝ) (u : ℂ) :
    DOZZ.planarWirtingerKernel k β 1 (star u) =
      star (DOZZ.planarWirtingerKernel k β 1 u) := by
  rw [DOZZ.planarWirtingerKernel, DOZZ.planarWirtingerKernel]
  have hsub : star u - 1 = star (u - 1) := by simp
  have hnum : ‖star u - 1‖ ^ k = ‖u - 1‖ ^ k := by
    rw [hsub, norm_star]
  simp_all

private theorem half_cancel (x : ℝ) : x * (1 / 2) + x * (-1 / 2) = 0 := by ring
section
variable (k β : ℝ)

private theorem planarRealSecondDifferenceLimit_decompose (u : ℂ)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    planarRealSecondDifferenceLimit k β u =
      2 * ((k / 2) * (k / 2 - 1) *
          (DOZZ.planarWirtingerKernel k β 1 u).re +
        (k / 2) ^ 2 * DOZZ.planarMixedKernel k β 1 u) := by
  let v := u - 1
  let r := ‖u‖
  let s := ‖v‖
  have hv : v ≠ 0 := by
    positivity
  have hr : 0 < r := by positivity
  have hs : 0 < s := by positivity
  have hrβ : 0 < r ^ β := Real.rpow_pos_of_pos hr β
  have hW : (DOZZ.planarWirtingerKernel k β 1 u).re =
      r ^ (-β) * (((s ^ k : ℝ) : ℂ) / v ^ 2).re := by
    unfold DOZZ.planarWirtingerKernel
    have hshift : (1 : ℂ) - u = -v := by ring
    rw [hshift, neg_sq]
    have hdiv : (((s ^ k : ℝ) : ℂ) / (v ^ 2 * ((r ^ β : ℝ) : ℂ))) =
        (((s ^ k : ℝ) : ℂ) / v ^ 2) / (r ^ β : ℝ) := by
      ring
    rw [hdiv, Complex.div_ofReal_re, Real.rpow_neg (norm_nonneg u)]
    ring
  have hsqre : (v ^ 2).re = 2 * v.re ^ 2 - s ^ 2 := by
    rw [pow_two, Complex.mul_re]
    have hnorm : s ^ 2 = v.re ^ 2 + v.im ^ 2 := by
      calc
        s ^ 2 = Complex.normSq v := by
          dsimp [s]
          exact (Complex.normSq_eq_norm_sq v).symm
        _ = v.re ^ 2 + v.im ^ 2 := by simp [Complex.normSq_apply, pow_two]
    linear_combination hnorm
  have hsqnorm : Complex.normSq (v ^ 2) = s ^ 4 := by
    rw [pow_two, Complex.normSq_mul, Complex.normSq_eq_norm_sq]
    linarith
  have hRe : (((s ^ k : ℝ) : ℂ) / v ^ 2).re =
      s ^ (k - 4) * (2 * v.re ^ 2 - s ^ 2) := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    rw [hsqre, hsqnorm]
    simp
    calc
      s ^ k * (2 * v.re ^ 2 - s ^ 2) / s ^ 4 =
          (s ^ k / s ^ 4) * (2 * v.re ^ 2 - s ^ 2) := by ring
      _ = s ^ (k - 4) * (2 * v.re ^ 2 - s ^ 2) := by
        have hpow : s ^ k / s ^ (4 : ℕ) = s ^ (k - 4) := by
          rw [← Real.rpow_natCast s 4]
          exact (Real.rpow_sub hs k 4).symm
        rw [hpow]
  have hM : DOZZ.planarMixedKernel k β 1 u =
      r ^ (-β) * s ^ (k - 2) := by
    unfold DOZZ.planarMixedKernel
    have hshift : u - (1 : ℂ) = v := by rfl
    rw [hshift, div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
    dsimp [r, s]
    ring
  have hpow₁ : (s ^ (2 : ℕ)) ^ (k / 2 - 2) = s ^ (k - 4) := by
    have hbase : s ^ (2 : ℕ) = s ^ (2 : ℝ) := by simp
    calc
      (s ^ (2 : ℕ)) ^ (k / 2 - 2) = (s ^ (2 : ℝ)) ^ (k / 2 - 2) := by
        rw [hbase]
      _ = s ^ (2 * (k / 2 - 2)) := (Real.rpow_mul hs.le 2 _).symm
      _ = s ^ (k - 4) := by ring
  have hpow₂ : (s ^ (2 : ℕ)) ^ (k / 2 - 1) = s ^ (k - 2) := by
    have hbase : s ^ (2 : ℕ) = s ^ (2 : ℝ) := by simp
    calc
      (s ^ (2 : ℕ)) ^ (k / 2 - 1) = (s ^ (2 : ℝ)) ^ (k / 2 - 1) := by
        rw [hbase]
      _ = s ^ (2 * (k / 2 - 1)) := (Real.rpow_mul hs.le 2 _).symm
      _ = s ^ (k - 2) := by ring
  have hpowAdd : s ^ (k - 4) * s ^ (2 : ℕ) = s ^ (k - 2) := by
    calc
      s ^ (k - 4) * s ^ (2 : ℕ) = s ^ (k - 4) * s ^ (2 : ℝ) := by
        exact congrArg (fun x : ℝ => s ^ (k - 4) * x)
          (Real.rpow_natCast s 2).symm
      _ = s ^ ((k - 4) + 2) := (Real.rpow_add hs _ 2).symm
      _ = s ^ (k - 2) := by ring
  rw [planarRealSecondDifferenceLimit, hW, hRe, hM, hpow₁, hpow₂]
  dsimp [r, v]
  ring_nf
  have hpowAddNF : s ^ (-4 + k) * s ^ (2 : ℝ) = s ^ (-2 + k) := by
    simpa [sub_eq_add_neg, add_comm] using hpowAdd
  simp_rw [← hpowAddNF]
  let R := ‖u‖ ^ (-β)
  let S := s ^ (-4 + k)
  have hR : R = ‖u‖ ^ (-β) := rfl
  have hS : S = s ^ (-4 + k) := rfl
  simp_rw [← hR, ← hS]
  ring_nf
  have hpair : R * k ^ 2 * S * s ^ (2 : ℝ) * (1 / 2) +
      R * k ^ 2 * S * s ^ 2 * (-1 / 2) = 0 := by
    have hs2 : s ^ (2 : ℝ) = s ^ (2 : ℕ) := Real.rpow_natCast s 2
    calc
      _ = R * k ^ 2 * S * s ^ (2 : ℝ) * (1 / 2) +
          R * k ^ 2 * S * s ^ (2 : ℝ) * (-1 / 2) := by
            exact congrArg
              (fun x : ℝ => R * k ^ 2 * S * s ^ (2 : ℝ) * (1 / 2) +
                R * k ^ 2 * S * x * (-1 / 2)) hs2.symm
      _ = 0 := half_cancel _
  conv_rhs =>
    rw [add_assoc]
    arg 2
    rw [hpair]
  simp
section
variable (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2)
include hk hβ hβ₂

private theorem planarWirtinger_integral_at_one_from_parent (A : ℝ)
    (hA : (A : ℂ) = DOZZ.planarGaussConstant k β)
    (hsecond : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      (2 + k - β) * (1 + k - β) * A) :
    (k / 2) * (k / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β := by
  let W : ℂ → ℂ := fun u => DOZZ.planarWirtingerKernel k β 1 u
  let M : ℂ → ℝ := fun u => DOZZ.planarMixedKernel k β 1 u
  let q := k / 2
  let p := q * (q - 1)
  let α : ℝ := 2 + k - β
  let X := ∫ u : ℂ, (W u).re
  let m := ∫ u : ℂ, M u
  have hWInt : Integrable W volume := by
    apply (integrable_planarWirtingerKernel_iff k β hk 1 (by norm_num)).2
    simp_all
  have hMData := planar_mixed_integral k β hk hβ hβ₂ 1 (by norm_num)
  have hMInt : Integrable M volume := by tauto
  have hXInt : Integrable (fun u : ℂ => (W u).re) volume := hWInt.re
  have hdecompAE : (fun u : ℂ => planarRealSecondDifferenceLimit k β u) =ᵐ[volume]
      fun u => 2 * (p * (W u).re + q ^ 2 * M u) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
    simpa [p, q, W, M] using planarRealSecondDifferenceLimit_decompose k β u hu0 hu1
  have hdecomp : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      2 * (p * X + q ^ 2 * m) := by
    calc
      _ = ∫ u : ℂ, 2 * (p * (W u).re + q ^ 2 * M u) := integral_congr_ae hdecompAE
      _ = 2 * ((∫ u : ℂ, p * (W u).re) + (∫ u : ℂ, q ^ 2 * M u)) := by
        rw [integral_const_mul, integral_add (hXInt.const_mul p) (hMInt.const_mul _)]
      _ = 2 * (p * X + q ^ 2 * m) := by
        rw [integral_const_mul, integral_const_mul]
  have hreflection : ∀ u : ℂ, W (star u) = star (W u) := by
    intro u
    exact planarWirtingerKernel_reflection k β u
  have hcomp : (∫ u : ℂ, W (star u)) = ∫ u : ℂ, W u := by
    change (∫ u : ℂ, W (Complex.conjLIE u)) = _
    exact (LinearIsometryEquiv.measurePreserving Complex.conjLIE).integral_comp
      Complex.conjLIE.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding W
  have hstar : (∫ u : ℂ, W (star u)) = star (∫ u : ℂ, W u) := by
    calc
      _ = ∫ u : ℂ, star (W u) := integral_congr_ae (Filter.Eventually.of_forall hreflection)
      _ = _ := by simpa using (integral_conj (f := W))
  have hWself : star (∫ u : ℂ, W u) = ∫ u : ℂ, W u := hstar.symm.trans hcomp
  have hWreal : (∫ u : ℂ, W u) = (X : ℂ) := by
    calc
      _ = (((∫ u : ℂ, W u).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp hWself).symm
      _ = (X : ℂ) := by
        change Complex.ofReal ((∫ u : ℂ, W u).re) =
          Complex.ofReal (∫ u : ℂ, (W u).re)
        exact congrArg Complex.ofReal (integral_re hWInt).symm
  have hMvalue : ((q ^ 2 * m : ℝ) : ℂ) = ((α : ℂ) / 2) ^ 2 *
      DOZZ.planarGaussConstant k β := by
    simpa [M, m, q, α, norm_one, Real.one_rpow] using hMData.2
  have hsecond' : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      α * (α - 1) * A := by
    calc
      _ = (2 + k - β) * (1 + k - β) * A := hsecond
      _ = α * (α - 1) * A := by linarith
  have hbalance : Complex.ofReal (α * (α - 1) * A) =
      Complex.ofReal (2 * (p * X + q ^ 2 * m)) := by
    calc
      _ = Complex.ofReal (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) :=
        congrArg Complex.ofReal hsecond'.symm
      _ = _ := congrArg Complex.ofReal hdecomp
  have htarget : Complex.ofReal (p * X) =
      Complex.ofReal ((α / 2) * (α / 2 - 1)) * DOZZ.planarGaussConstant k β := by
    have hcoeff : ((α : ℂ) / 2) ^ 2 = Complex.ofReal ((α / 2) ^ 2) := by
      push_cast
      ring
    have hbalanceReal : α * (α - 1) * A = 2 * (p * X + q ^ 2 * m) :=
      Complex.ofReal_injective hbalance
    have hsolve : p * X = α * (α - 1) / 2 * A - q ^ 2 * m := by
      linear_combination (-1 / 2 : ℝ) * hbalanceReal
    calc
      _ = Complex.ofReal _ :=
        congrArg Complex.ofReal hsolve
      _ = Complex.ofReal _ - Complex.ofReal _ :=
        Complex.ofReal_sub ..
      _ = Complex.ofReal (α * (α - 1) / 2) * (A : ℂ) - Complex.ofReal (q ^ 2 * m) := by
        rw [Complex.ofReal_mul]
      _ = Complex.ofReal (α * (α - 1) / 2) * DOZZ.planarGaussConstant k β -
          ((α : ℂ) / 2) ^ 2 * DOZZ.planarGaussConstant k β := by grind
      _ = Complex.ofReal _ * DOZZ.planarGaussConstant k β -
          Complex.ofReal _ * DOZZ.planarGaussConstant k β := by tauto
      _ = Complex.ofReal (α * (α - 1) / 2 - (α / 2) ^ 2) *
          DOZZ.planarGaussConstant k β := by
        rw [Complex.ofReal_sub]
        ring
      _ = _ := by
        have hcoef : α * (α - 1) / 2 - (α / 2) ^ 2 =
            (α / 2) * (α / 2 - 1) := by ring
        rw [hcoef]
  rw [hWreal]
  simpa [p, q, α] using htarget

private theorem planarWirtinger_integral_at_one_value (hβne : β ≠ k + 1) :
    (k / 2) * (k / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β := by
  rcases lt_or_gt_of_ne hβne with hTaylor | hDifference
  · let A := ∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u
    have hA : A = DOZZ.planarGaussConstant k β := by
      simpa [A, norm_one, Real.one_rpow, integral_complex_ofReal] using
        ((planar_taylor_integral k β hk hβ hβ₂ hTaylor) 1).2
    exact planarWirtinger_integral_at_one_from_parent k β hk hβ hβ₂ A hA
      (by simpa [A] using (planarTaylor_real_second_derivative_relation k β hk hβ hβ₂ hTaylor))
  · let A := ∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u
    have hA : A = DOZZ.planarGaussConstant k β := by
      simpa [A, norm_one, Real.one_rpow, integral_complex_ofReal] using
        ((planar_difference_integral k β hk hDifference hβ₂) 1).2
    have hsecond := planarDifference_real_second_derivative_relation k β hk
      (by linarith) hβ₂ hDifference
    exact planarWirtinger_integral_at_one_from_parent k β hk hβ hβ₂ A hA
      (by assumption)

private theorem planarWirtinger_integral_tendsto_parameter :
    Tendsto (fun b : ℝ => ∫ u : ℂ, DOZZ.planarWirtingerKernel k b 1 u)
      (𝓝 β) (𝓝 (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := by
  let δ := min ((β - k) / 2) ((2 - β) / 2)
  let βlo := β - δ
  let βhi := β + δ
  let B : ℂ → ℝ := fun u =>
    ‖u‖ ^ (-βlo) * ‖u - 1‖ ^ (k - 2) +
      ‖u‖ ^ (-βhi) * ‖u - 1‖ ^ (k - 2)
  have hδ : 0 < δ := by positivity
  have hklo : k < βlo := by
    grind
  have hhi₂ : βhi < 2 := by
    grind
  have hβlo : βlo < β := by linarith
  have hβhi : β < βhi := by linarith
  have hparam : ∀ᶠ b : ℝ in 𝓝 β, βlo < b ∧ b < βhi := by
    filter_upwards [Ioo_mem_nhds hβlo hβhi] with b hb
    assumption
  have hlowInt := positive_riesz_convolution_integrable k βlo hk hklo
    (by linarith)
    (1 : ℂ) (by norm_num)
  have hhighInt := positive_riesz_convolution_integrable k βhi hk
    (by linarith) hhi₂
    (1 : ℂ) (by norm_num)
  have hBInt : Integrable B volume := by
    fun_prop
  have hmeas : ∀ᶠ b : ℝ in 𝓝 β,
      AEStronglyMeasurable (DOZZ.planarWirtingerKernel k b 1) volume := by
    filter_upwards [hparam] with b hb
    have hi : Integrable (DOZZ.planarWirtingerKernel k b 1) volume :=
      (integrable_planarWirtingerKernel_iff k b hk 1 (by norm_num)).2
        ⟨by linarith, by linarith⟩
    exact hi.aestronglyMeasurable
  have hbound : ∀ᶠ b : ℝ in 𝓝 β, ∀ᵐ u ∂volume,
      ‖DOZZ.planarWirtingerKernel k b 1 u‖ ≤ B u := by
    filter_upwards [hparam] with b hb
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
    have hrpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hnorm' : ‖DOZZ.planarWirtingerKernel k b 1 u‖ =
        ‖u‖ ^ (-b) * ‖u - 1‖ ^ (k - 2) := by
      rw [(norm_planarWirtingerKernel_eq k b 1 u hu0 hu1), div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg u)]
      ring
    rw [hnorm']
    by_cases hrle : ‖u‖ ≤ 1
    · have hpow : ‖u‖ ^ (-b) ≤ ‖u‖ ^ (-βhi) :=
        Real.rpow_le_rpow_of_exponent_ge hrpos hrle (by linarith)
      have hsnonneg : 0 ≤ ‖u - 1‖ ^ (k - 2) := Real.rpow_nonneg (norm_nonneg _) _
      calc
        ‖u‖ ^ (-b) * ‖u - 1‖ ^ (k - 2) ≤
            ‖u‖ ^ (-βhi) * ‖u - 1‖ ^ (k - 2) := mul_le_mul_of_nonneg_right hpow hsnonneg
        _ ≤ B u := by
          dsimp [B]
          exact le_add_of_nonneg_left (mul_nonneg
            (Real.rpow_nonneg (norm_nonneg u) _) hsnonneg)
    · have hrge : 1 ≤ ‖u‖ := le_of_not_ge hrle
      have hpow : ‖u‖ ^ (-b) ≤ ‖u‖ ^ (-βlo) :=
        Real.rpow_le_rpow_of_exponent_le hrge (by linarith)
      have hsnonneg : 0 ≤ ‖u - 1‖ ^ (k - 2) := Real.rpow_nonneg (norm_nonneg _) _
      calc
        ‖u‖ ^ (-b) * ‖u - 1‖ ^ (k - 2) ≤
            ‖u‖ ^ (-βlo) * ‖u - 1‖ ^ (k - 2) := mul_le_mul_of_nonneg_right hpow hsnonneg
        _ ≤ B u := by
          exact le_add_of_nonneg_right (mul_nonneg
            (Real.rpow_nonneg (norm_nonneg u) _) hsnonneg)
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun b => DOZZ.planarWirtingerKernel k b 1 u) (𝓝 β)
      (𝓝 (DOZZ.planarWirtingerKernel k β 1 u)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
    have hpow : Tendsto (fun b => ‖u‖ ^ b) (𝓝 β) (𝓝 (‖u‖ ^ β)) :=
      (Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu0)).tendsto
    have hpowC : Tendsto (fun b => ((‖u‖ ^ b : ℝ) : ℂ))
        (𝓝 β) (𝓝 ((‖u‖ ^ β : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hpow
    have hdenom : Tendsto (fun b => (1 - u) ^ 2 * ((‖u‖ ^ b : ℝ) : ℂ))
        (𝓝 β) (𝓝 ((1 - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ))) :=
      tendsto_const_nhds.mul hpowC
    have hdenom0 : (1 - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hu1)))
      exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hu0) β).ne'
    let N := (‖u - 1‖ ^ k : ℝ)
    have hkernel : Tendsto
        (fun b => N / ((1 - u) ^ 2 * ((‖u‖ ^ b : ℝ) : ℂ)))
        (𝓝 β) (𝓝 (N / ((1 - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ)))) := by
      exact tendsto_const_nhds.div hdenom hdenom0
    simpa [N, DOZZ.planarWirtingerKernel] using hkernel
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
    hmeas hbound hBInt hlim

end

end

private theorem planarWirtingerTargetReal_continuousAt (k : ℝ) (hk : 0 < k)
    (hk1 : k < 1) :
    ContinuousAt (planarWirtingerTargetReal k) (k + 1) := by
  let qA : ℝ → ℝ := fun b => (2 + k - b) / 2
  let N : ℝ → ℝ := fun b =>
    Real.Gamma (1 - b / 2) * Real.Gamma (k / 2) * Real.Gamma ((b - k) / 2)
  let D : ℝ → ℝ := fun b =>
    Real.Gamma (b / 2) * Real.Gamma (1 - k / 2) * Real.Gamma (1 + (k - b) / 2)
  have hqA : ContinuousAt qA (k + 1) := by
    fun_prop
  have hqA0 : qA (k + 1) ≠ 0 := by
    grind
  have harg1 : ContinuousAt (fun b : ℝ => 1 - b / 2) (k + 1) := by fun_prop
  have harg2 : ContinuousAt (fun b : ℝ => b / 2) (k + 1) := by fun_prop
  have harg3 : ContinuousAt (fun b : ℝ => (b - k) / 2) (k + 1) := by fun_prop
  have harg6 : ContinuousAt (fun b : ℝ => 1 + (k - b) / 2) (k + 1) := by fun_prop
  have hΓ1 : ContinuousAt (fun b : ℝ => Real.Gamma (1 - b / 2)) (k + 1) := by
    have hp : 0 < 1 - (k + 1) / 2 := by linarith
    exact (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg1 (by ring)
  have hΓ2 : ContinuousAt (fun b : ℝ => Real.Gamma (b / 2)) (k + 1) := by
    have hp : 0 < (k + 1) / 2 := by linarith
    exact (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg2 (by ring)
  have hΓ3 : ContinuousAt (fun b : ℝ => Real.Gamma ((b - k) / 2)) (k + 1) := by
    have hp : 0 < ((k + 1) - k) / 2 := by norm_num
    exact (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg3 (by ring)
  have hΓ6 : ContinuousAt (fun b : ℝ => Real.Gamma (1 + (k - b) / 2)) (k + 1) := by
    have hp : 0 < 1 + (k - (k + 1)) / 2 := by norm_num
    have hcomp := (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg6 (by ring)
    change ContinuousAt (Real.Gamma ∘ fun b : ℝ => 1 + (k - b) / 2) _
    exact hcomp
  have hN : ContinuousAt N (k + 1) := by
    dsimp [N]
    exact hΓ1.mul continuousAt_const |>.mul hΓ3
  have hD : ContinuousAt D (k + 1) := by
    dsimp [D]
    exact hΓ2.mul continuousAt_const |>.mul hΓ6
  have hDpos : 0 < D (k + 1) := by
    dsimp [D]
    have hp2 : 0 < (k + 1) / 2 := by linarith
    have hp5 : 0 < 1 - k / 2 := by linarith
    have hp6 : 0 < 1 + (k - (k + 1)) / 2 := by norm_num
    exact mul_pos (mul_pos (Real.Gamma_pos_of_pos hp2) (Real.Gamma_pos_of_pos hp5))
      (Real.Gamma_pos_of_pos hp6)
  have hbase : ContinuousAt (fun b : ℝ => Real.pi * (N b / D b)) (k + 1) :=
    continuousAt_const.mul (hN.div hD hDpos.ne')
  have hfactor : ContinuousAt (fun b : ℝ => (k / 2) ^ 2 / (qA b) ^ 2) (k + 1) :=
    continuousAt_const.div (hqA.pow 2) (pow_ne_zero 2 hqA0)
  have hcoeff : ContinuousAt (fun b : ℝ => qA b * (qA b - 1)) (k + 1) :=
    by fun_prop
  have htarget : ContinuousAt (fun b : ℝ =>
      qA b * (qA b - 1) * ((k / 2) ^ 2 / (qA b) ^ 2 * (Real.pi * (N b / D b))))
      (k + 1) := by fun_prop
  have hfun : (fun b : ℝ => planarWirtingerTargetReal k b) =
      (fun b => qA b * (qA b - 1) *
        ((k / 2) ^ 2 / (qA b) ^ 2 * (Real.pi * (N b / D b)))) := by
    funext b
    simp only [planarWirtingerTargetReal, planarRieszCoefficientReal, qA, N, D]
    ring
  simpa only [hfun] using htarget
section
variable (k β : ℝ)
section
variable (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2)
include hk hβ hβ₂

private theorem planarWirtingerTargetReal_eq :
    ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β =
      (planarWirtingerTargetReal k β : ℂ) := by
  have hGauss : (planarRieszCoefficientReal k β) =
      DOZZ.planarGaussConstant k β := by
    simpa [planarRieszCoefficientReal] using
      positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂
  let a := (2 + k - β) / 2
  have hcast : ((2 + k - β) / 2) *
      ((2 + k - β) / 2 - 1) =
        Complex.ofReal (a * (a - 1)) := by
    aesop
  calc
    _ = Complex.ofReal _ * DOZZ.planarGaussConstant k β := by tauto
    _ = Complex.ofReal _ *
        Complex.ofReal _ := by tauto
    _ = Complex.ofReal _ :=
      by norm_cast
    _ = Complex.ofReal _ := by
      rfl

private theorem planarWirtinger_integral_at_one_value_all :
    (k / 2) * (k / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β := by
  by_cases hβne : β ≠ k + 1
  · exact planarWirtinger_integral_at_one_value k β hk hβ hβ₂ hβne
  · have hβeq : β = k + 1 := by
      simp_all
    subst β
    have hk1 : k < 1 := by linarith
    let l := 𝓝[≠] (k + 1)
    let L : ℝ → ℂ := fun b =>
      ((k / 2) * (k / 2 - 1) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k b 1 u)
    let R : ℝ → ℂ := fun b => (planarWirtingerTargetReal k b : ℂ)
    have hDCT := planarWirtinger_integral_tendsto_parameter k (k + 1) hk
      (by linarith) (by linarith)
    have hleftFull : Tendsto L (𝓝 (k + 1))
        (𝓝 (L (k + 1))) := by
      have hconst : Tendsto (fun _ =>
          (((k / 2) * (k / 2 - 1) : ℝ) : ℂ)) (𝓝 (k + 1))
          (𝓝 (((k / 2) * (k / 2 - 1) : ℝ) : ℂ)) := tendsto_const_nhds
      exact hconst.mul hDCT
    have hleft : Tendsto L l (𝓝 (L (k + 1))) := hleftFull.mono_left nhdsWithin_le_nhds
    have hrightFull : Tendsto R (𝓝 (k + 1)) (𝓝 (R (k + 1))) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (planarWirtingerTargetReal_continuousAt k hk hk1).tendsto
    have hright : Tendsto R l (𝓝 (R (k + 1))) := hrightFull.mono_left nhdsWithin_le_nhds
    have hinterval : ∀ᶠ b : ℝ in l, k < b ∧ b < 2 := by
      have hlow : ∀ᶠ b : ℝ in l, k < b :=
        (eventually_gt_nhds (show k < k + 1 by linarith)).filter_mono nhdsWithin_le_nhds
      have hhigh : ∀ᶠ b : ℝ in l, b < 2 :=
        (eventually_lt_nhds (show k + 1 < 2 by linarith)).filter_mono nhdsWithin_le_nhds
      simp_all
    have heq : L =ᶠ[l] R := by
      filter_upwards [hinterval, self_mem_nhdsWithin] with b hb hbe
      have hvalue := planarWirtinger_integral_at_one_value k b hk hb.1 hb.2
        (by assumption)
      have htarget := planarWirtingerTargetReal_eq k b hk hb.1 hb.2
      aesop
    have hlim : L (k + 1) = R (k + 1) :=
      tendsto_nhds_unique (hleft.congr' heq) hright
    have hlim' : ((k : ℂ) / 2) * ((k : ℂ) / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k (k + 1) 1 u) =
          (planarWirtingerTargetReal k (k + 1) : ℂ) := by
      aesop
    have htarget := planarWirtingerTargetReal_eq k (k + 1) hk
      (by linarith) (by linarith)
    exact hlim'.trans htarget.symm

end
section
variable (hk : 0 < k) (hβ : k < β) (ξ z : ℂ) (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r) (hz : ξ * (r : ℂ) = z)
include hk hβ hξ hr hz

private theorem planarWirtingerKernel_rotated_scale (v : ℂ) :
    DOZZ.planarWirtingerKernel k β z (ξ * (r • v)) =
      (ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
        DOZZ.planarWirtingerKernel k β 1 v := by
  have hβpos : 0 < β := lt_trans hk hβ
  by_cases hv0 : v = 0
  · subst v
    simp [DOZZ.planarWirtingerKernel, Real.zero_rpow, ne_of_gt hβpos]
  · by_cases hv1 : v = 1
    · subst v
      simp [DOZZ.planarWirtingerKernel, hz, Real.zero_rpow, ne_of_gt hk]
    · have hξ0 : ξ ≠ 0 := by
        aesop
      have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hnormV : ‖ξ * (r • v)‖ = r * ‖v‖ := by
        rw [norm_mul, hξ, one_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hdiff : ξ * (r • v) - ξ * (r : ℂ) = ξ * (r : ℂ) * (v - 1) := by
        change ξ * ((r : ℂ) * v) - ξ * (r : ℂ) = ξ * (r : ℂ) * (v - 1)
        ring
      have hnormDiff : ‖ξ * (r • v) - z‖ = r * ‖v - 1‖ := by
        aesop
      have hden : (z - ξ * (r • v)) ^ 2 = ξ ^ 2 * (r : ℂ) ^ 2 * (1 - v) ^ 2 := by
        grind
      have hnumPow : (r * ‖v - 1‖) ^ k = r ^ k * ‖v - 1‖ ^ k :=
        Real.mul_rpow hr.le (norm_nonneg (v - 1))
      have hdenPow : (r * ‖v‖) ^ β = r ^ β * ‖v‖ ^ β :=
        Real.mul_rpow hr.le (norm_nonneg v)
      have hrpow : r ^ k = r ^ (k - β - 2) * (r ^ β * r ^ 2) := by
        calc
          r ^ k = r ^ ((k - β - 2) + (β + 2)) := by
            simp
          _ = r ^ (k - β - 2) * r ^ (β + 2) := Real.rpow_add hr ..
          _ = r ^ (k - β - 2) * (r ^ β * r ^ 2) := by
            rw [Real.rpow_add hr β 2]
            simp
      rw [DOZZ.planarWirtingerKernel, DOZZ.planarWirtingerKernel,
        hnormDiff, hnormV, hden, hnumPow, hdenPow]
      have hnormvpos : 0 < ‖v‖ ^ β :=
        by positivity
      have hnormdiffpos : 0 < ‖v - 1‖ ^ k :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv1)) k
      have hxi2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ0
      have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
      have hrβ : r ^ β ≠ 0 := by positivity
      have hcv : (1 - v) ^ 2 ≠ 0 := by positivity
      field_simp [hxi2, hr2, hrβ, hnormvpos.ne', hcv, hnormdiffpos.ne']
      rw [hrpow]
      push_cast
      ring

private theorem planarWirtingerKernel_integral_scale :
    (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
      (ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) := by
  let g : ℂ → ℂ := fun u => DOZZ.planarWirtingerKernel k β z (ξ * u)
  have hrotation : (∫ u : ℂ, g u) =
      (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) := by
    change (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z _) = _
    let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
    simpa using
      (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
        ((rotation c).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding)
        (fun u : ℂ => DOZZ.planarWirtingerKernel k β z u)
  have hscaling : (∫ u : ℂ, g (r • u)) =
      (((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) * (∫ u : ℂ, g u) := by
    have h := Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)
    simp_all
  have hpoint : (fun u : ℂ => g (r • u)) = fun u =>
      (ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
        DOZZ.planarWirtingerKernel k β 1 u := by
    funext u
    exact planarWirtingerKernel_rotated_scale k β hk hβ ξ z hξ r hr hz u
  rw [hpoint, integral_const_mul] at hscaling
  rw [hrotation] at hscaling
  have hmul := congrArg (fun x : ℂ => (r ^ 2 : ℝ) * x) hscaling
  have hrpow : r ^ 2 * r ^ (k - β - 2) = r ^ (k - β) := by
    rw [← Real.rpow_natCast r 2]
    calc
      _ = r ^ (2 + (k - β - 2)) := (Real.rpow_add hr 2 _).symm
      _ = _ := by simp
  have hrpowC : ((r ^ 2 : ℝ) : ℂ) * (r ^ (k - β - 2) : ℝ) =
      (r ^ (k - β) : ℝ) := by
    norm_cast
  have hleft : (r ^ 2 : ℝ) *
      ((ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) =
      (ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) := by
    grind
  have hr2 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by aesop
  simp_all

end

theorem planar_wirtinger_integral (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, z ≠ 0 → Integrable (DOZZ.planarWirtingerKernel k β z) volume ∧
      (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
        ((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
          (‖z‖ ^ (2 + k - β) : ℝ) / z ^ 2 *
            DOZZ.planarGaussConstant k β := by
  intro z hz
  constructor
  · exact (integrable_planarWirtingerKernel_iff k β hk z hz).2 ⟨hβ, hβ₂⟩
  · let r := ‖z‖
    let ξ := z / (r : ℂ)
    have hr : 0 < r := by positivity
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hξ : ‖ξ‖ = 1 := by
      aesop
    have hξ0 : ξ ≠ 0 := by
      positivity
    have hξr : ξ * (r : ℂ) = z := by
      aesop
    have hzsq : z ^ 2 = ξ ^ 2 * (r : ℂ) ^ 2 := by
      grind
    have hrpow : r ^ (2 + k - β) = r ^ 2 * r ^ (k - β) := by
      rw [← Real.rpow_natCast r 2]
      calc
        r ^ (2 + k - β) = r ^ (2 + (k - β)) := by ring
        _ = r ^ (2 : ℝ) * r ^ (k - β) := Real.rpow_add hr 2 _
    have hrpowC : (r ^ (2 + k - β) : ℝ) =
        (r ^ 2 : ℝ) * r ^ (k - β) := by
      exact hrpow
    have hfactor : (ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) =
        (r ^ (2 + k - β) : ℝ) / z ^ 2 := by
      rw [hrpowC, hzsq]
      have hξ2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ0
      have hr2 : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hrC
      field_simp [hξ2, hr2]
      simp
    have hscale := planarWirtingerKernel_integral_scale k β hk hβ
      ξ z hξ r hr hξr
    have hbase := planarWirtinger_integral_at_one_value_all k β hk hβ hβ₂
    have hvalue : (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
        ((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
          (r ^ (2 + k - β) : ℝ) / z ^ 2 *
            DOZZ.planarGaussConstant k β := by
      calc
        _ = (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
            ((ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) *
              (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := by simp_all
        _ = ((ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ)) *
            ((k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
              (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := by ring
        _ = ((ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ)) *
            (((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
              DOZZ.planarGaussConstant k β) := by
                simp_all
        _ = _ := by grind
    simpa [r] using hvalue

end

end DOZZ.Proofs
