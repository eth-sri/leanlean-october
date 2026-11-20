/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.ZeroMass
public import DOZZ.FourPoint.Dual.NegativePowerDifference
import Mathlib.Tactic

/-! # Inverse-power differences and finite nonnegative expectations -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Two almost-sure additive comparisons bound the difference of finite expectations. -/
theorem reflected_lintegral_toReal_difference_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F G R : Ω → ℝ≥0∞)
    (hFm : AEMeasurable F P) (hGm : AEMeasurable G P)
    (hF : (∫⁻ ω, F ω ∂P) ≠ ⊤) (hG : (∫⁻ ω, G ω ∂P) ≠ ⊤)
    (hR : (∫⁻ ω, R ω ∂P) ≠ ⊤)
    (hFG : ∀ᵐ ω ∂P, F ω ≤ G ω + R ω)
    (hGF : ∀ᵐ ω ∂P, G ω ≤ F ω + R ω) :
    |(∫⁻ ω, F ω ∂P).toReal - (∫⁻ ω, G ω ∂P).toReal| ≤
      (∫⁻ ω, R ω ∂P).toReal := by
  have h1 := lintegral_mono_ae hFG
  have h2 := lintegral_mono_ae hGF
  rw [lintegral_add_left' hGm] at h1
  rw [lintegral_add_left' hFm] at h2
  have hr1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hG, hR⟩) h1
  have hr2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hF, hR⟩) h2
  rw [ENNReal.toReal_add hG hR] at hr1
  rw [ENNReal.toReal_add hF hR] at hr2
  exact abs_le.mpr ⟨by linarith only [hr2], by linarith only [hr1]⟩

/-- Adding a nonnegative mass has a first-order inverse-power error controlled by the
retained mass, including the literal ENNReal totalizations. -/
theorem reflected_ennreal_inverse_add_bound (p : ℝ) (hp : 0 < p) (S I : ℝ≥0∞)
    (hS : S ≠ 0) (hSt : S ≠ ⊤) (hIt : I ≠ ⊤) :
    S ^ (-p) ≤ (S + I) ^ (-p) + ENNReal.ofReal p * I * S ^ (-(p + 1)) := by
  have hs : 0 < S.toReal := ENNReal.toReal_pos hS hSt
  have ht : S + I ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hSt, hIt⟩
  have hsz : S + I ≠ 0 := ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hS) le_self_add)
  have hrt : (S + I) ^ (-p) + ENNReal.ofReal p * I * S ^ (-(p + 1)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.rpow_ne_top_of_ne_zero hsz ht,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt)
        (ENNReal.rpow_ne_top_of_ne_zero hS hSt)⟩
  apply (ENNReal.toReal_le_toReal (ENNReal.rpow_ne_top_of_ne_zero hS hSt) hrt).mp
  rw [ENNReal.toReal_add (ENNReal.rpow_ne_top_of_ne_zero hsz ht)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt)
      (ENNReal.rpow_ne_top_of_ne_zero hS hSt)),
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_add hSt hIt, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.toReal_rpow]
  have hh := dual_negative_power_lipschitz p S.toReal S.toReal (S.toReal + I.toReal)
    hp hs le_rfl (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  rw [show -p - 1 = -(p + 1) by ring,
    show S.toReal - (S.toReal + I.toReal) = -I.toReal by ring,
    abs_neg, abs_of_nonneg ENNReal.toReal_nonneg] at hh
  have hl := (le_abs_self (S.toReal ^ (-p) - (S.toReal + I.toReal) ^ (-p))).trans hh
  nlinarith only [hl]

/-- A relative mass error, with a common quarter-mass lower bound, gives a relative
inverse-power error. -/
theorem reflected_real_inverse_relative_bound (p d S T : ℝ) (hp : 0 < p)
    (hS : 0 < S) (hT : S / 4 ≤ T) (hd : |T - S| ≤ d * S) :
    |T ^ (-p) - S ^ (-p)| ≤ (p * (1 / 4 : ℝ) ^ (-(p + 1)) * d) * S ^ (-p) := by
  have hlow : 0 < S / 4 := by positivity
  have hh := dual_negative_power_lipschitz p (S / 4) T S hp hlow hT (by linarith only [hS])
  have he : (S / 4) ^ (-p - 1) * S = (1 / 4 : ℝ) ^ (-(p + 1)) * S ^ (-p) := by
    rw [show S / 4 = (1 / 4 : ℝ) * S by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hS.le]
    have hpw : S ^ (-p - 1) * S = S ^ (-p) := by
      calc
        _ = S ^ (-p - 1) * S ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = S ^ (-p - 1 + 1) := (Real.rpow_add hS _ _).symm
        _ = _ := by congr 1; ring
    rw [mul_assoc, hpw, show -p - 1 = -(p + 1) by ring]
  calc
    _ ≤ p * (S / 4) ^ (-p - 1) * (d * S) :=
      hh.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = _ := by
      calc
        _ = (p * d) * ((S / 4) ^ (-p - 1) * S) := by ring
        _ = _ := by rw [he]; ring

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Bound the inverse-moment error after discarding a region by its weighted deleted mass. -/
theorem inverse_lintegral_split_bound (S F I : Ω → ℝ≥0∞) (p C : ℝ) (hp : 0 < p) (hC : 0 ≤ C)
    (hS : AEMeasurable S P) (hF : AEMeasurable F P)
    (hSt : (∫⁻ ω, S ω ^ (-p) ∂P) ≠ ∞)
    (hI : (∫⁻ ω, I ω * S ω ^ (-(p + 1)) ∂P) ≤ ENNReal.ofReal C)
    (h : ∀ᵐ ω ∂P, S ω ≠ 0 ∧ F ω ≠ ∞ ∧ F ω = S ω + I ω) :
    |(∫⁻ ω, S ω ^ (-p) ∂P).toReal - (∫⁻ ω, F ω ^ (-p) ∂P).toReal| ≤ p * C := by
  let R := fun ω => ENNReal.ofReal p * (I ω * S ω ^ (-(p + 1)))
  have hle : ∀ᵐ ω ∂P, F ω ^ (-p) ≤ S ω ^ (-p) := h.mono fun ω ⟨_, _, hw⟩ =>
    ennreal_rpow_antitone_of_nonpos (le_self_add.trans_eq hw.symm) (neg_nonpos.mpr hp.le)
  have hcomp : ∀ᵐ ω ∂P, S ω ^ (-p) ≤ F ω ^ (-p) + R ω := by
    filter_upwards [h] with ω ⟨hs, hf, he⟩
    rw [he, ENNReal.add_ne_top] at hf
    rw [he]
    simpa only [R, mul_assoc] using reflected_ennreal_inverse_add_bound p hp (S ω) (I ω) hs hf.1 hf.2
  have hb : (∫⁻ ω, R ω ∂P) ≤ ENNReal.ofReal (p * C) := by
    dsimp only [R]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hp.le]
    exact mul_le_mul' le_rfl hI
  exact (reflected_lintegral_toReal_difference_bound P _ _ R (hS.pow_const _) (hF.pow_const _)
    hSt (ne_top_of_le_ne_top hSt (lintegral_mono_ae hle)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
    hcomp (hle.mono fun _ hw => hw.trans le_self_add)).trans
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal (mul_nonneg hp.le hC)))

/-- A kernel representation of the full zero mass gives the same deleted-region estimate
for either choice of degenerate insertion. -/
theorem retainedZero_deleted_moment_le (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (β α₁ α₂ α₃ r p C : ℝ) (hr : r ≤ 1) (hp : 0 < p) (hC : 0 ≤ C)
    (hα₁ : α₁ + β < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (K : ℂ → ℝ≥0∞)
    (hK : ∀ ν : Measure ℂ, ν {0} = 0 → ν {1} = 0 →
      coulombMass γ ν ![β, α₁, α₂] ![0, 0, 1] α₃ = ∫⁻ x, K x ∂ν)
    (hd : (∫⁻ ω, (∫⁻ x in Metric.ball 0 r, K x ∂M ω) *
      retainedZeroMass γ β α₁ α₂ α₃ r (M ω) ^ (-(p + 1)) ∂P) ≤ ENNReal.ofReal C) :
    |(∫⁻ ω, retainedZeroMass γ β α₁ α₂ α₃ r (M ω) ^ (-p) ∂P).toReal -
      (∫⁻ ω, coulombMass γ (M ω) ![β, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal| ≤ p * C := by
  obtain ⟨_, _, hb⟩ := retainedZeroMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM β α₁ α₂ α₃ p hp.le
  apply inverse_lintegral_split_bound P _ _ _ p C hp hC
    ((retainedZeroMass_measurable ..).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM))
    (gmc_coulombMass_aemeasurable P X hX γ hγ hγ₂ M hM ..)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb r hr)) hd
  filter_upwards [retainedZeroMass_ae_positive_finite P X hX γ hγ hγ₂ M hM
    β α₁ α₂ α₃ r hr hα₁ hα₂ hα₃, gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 1] with ω hpf h0 h1
  refine ⟨hpf.1.ne', hpf.2.ne, ?_⟩
  simp only [Function.comp_apply]
  rw [retainedZeroMass_eq_setLIntegral γ β α₁ α₂ α₃ r (M ω) h0 h1 K hK,
    hK (M ω) h0 h1, lintegral_exterior_add_ball]

end

end DOZZ.Proofs
