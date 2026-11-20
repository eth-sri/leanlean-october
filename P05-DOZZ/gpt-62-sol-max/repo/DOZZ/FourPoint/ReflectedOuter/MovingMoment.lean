/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.MassPerturbation
public import DOZZ.FourPoint.ReflectedOuter.InversePerturbation
public import DOZZ.FourPoint.Reflected.ChargeShift
public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
import Mathlib.Tactic

/-! # The moving inverse-moment error at the relative cutoff scale -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The moving error is bounded by `‖z‖/r` times a uniform inverse moment, at the literal
outer radius `r=‖z‖^(1-ξ)`. The estimate does not impose any upper bound on `ξ`. -/
theorem fusion_outer_moving_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hb : 0 ≤ γ * χ) (hb₂ : γ * χ ≤ 2)
    (hα₁ : α₁ - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ),
      0 < ‖z‖ ^ (1 - ξ) → ‖z‖ ^ (1 - ξ) ≤ 1 → ‖z‖ ≤ 1 →
      ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 →
      |(∫⁻ ω, fusionOuterMass γ (-χ) α₁ α₂ α₃ (M ω) z ξ ^ (-p) ∂P).toReal -
        (∫⁻ ω, (retainedZeroMass γ (-χ) α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) (M ω)) ^ (-p) ∂P).toReal| ≤
          C * (‖z‖ / ‖z‖ ^ (1 - ξ)) := by
  obtain ⟨Cs, hCs, hsb⟩ := retainedZeroMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM (-χ) α₁ α₂ α₃ p hp.le
  obtain ⟨_, _, htb⟩ := fusionOuterMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM (-χ) α₁ α₂ α₃ p hp.le
  let A : ℝ := p * (1 / 4 : ℝ) ^ (-(p + 1))
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A * 4 * Cs, by positivity, ?_⟩
  intro z ξ hr hr₁ hz₁ hz
  let r : ℝ := ‖z‖ ^ (1 - ξ)
  let d : ℝ := 4 * (‖z‖ / r)
  let S : Ω → ℝ≥0∞ := fun ω => retainedZeroMass γ (-χ) α₁ α₂ α₃ r (M ω)
  let T : Ω → ℝ≥0∞ := fun ω => fusionOuterMass γ (-χ) α₁ α₂ α₃ (M ω) z ξ
  have hm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM
  have hSm : AEMeasurable S P :=
    (retainedZeroMass_measurable γ (-χ) α₁ α₂ α₃ r).comp_aemeasurable hm
  have hTm : AEMeasurable T P :=
    (fusionOuterMass_measurable γ (-χ) α₁ α₂ α₃ ξ z).comp_aemeasurable hm
  have hcomp : ∀ᵐ ω ∂P, S ω ≠ 0 ∧ S ω ≠ ∞ ∧ RelativeMassBound d (S ω) (T ω) := by
    filter_upwards [retainedZeroMass_ae_positive_finite P X hX γ hγ hγ₂ M hM
      (-χ) α₁ α₂ α₃ r hr₁ (by simpa [sub_eq_add_neg] using hα₁) hα₂ hα₃,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 1] with ω hpf h0 h1
    have hsfin : S ω ≠ ⊤ := ne_top_of_le_ne_top hpf.2.ne
      ((lintegral_mono' Measure.restrict_le_self fun _ => le_rfl))
    exact ⟨hpf.1.ne', hsfin, fusionOuterMass_relative_comparison
      γ χ α₁ α₂ α₃ ξ hb hb₂ z (M ω) hr hz h0 h1⟩
  have h := relative_inverse_lintegral_bound P S T p d Cs hp (by dsimp only [d]; positivity)
    hCs.le hSm hTm (hsb r hr₁) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htb z ξ hz₁ hr₁)) hcomp
  change |(∫⁻ ω, T ω ^ (-p) ∂P).toReal - (∫⁻ ω, S ω ^ (-p) ∂P).toReal| ≤ _
  convert h using 1 <;> dsimp only [A, d] <;> ring
/-- The relative comparison at the half-charge insertion. -/
theorem reflected_outer_moving_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hα₁ : α₁ - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ),
      0 < ‖z‖ ^ (1 - ξ) → ‖z‖ ^ (1 - ξ) ≤ 1 → ‖z‖ ≤ 1 →
      ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 →
      |gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        (∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) (M ω)) ^ (-p) ∂P).toReal| ≤
          C * (‖z‖ / ‖z‖ ^ (1 - ξ)) := by
  have h := fusion_outer_moving_moment_bound P X M γ (γ / 2) α₁ α₂ α₃ p hγ hγ₂ hp
    (by positivity) (by nlinarith only [hγ, hγ₂]) hα₁ hα₂ hα₃ hX hM
  simpa only [neg_div, reflectedRetainedZeroMass, gammaHalfOuterMass, fusionOuterMass, gammaHalfOuterMoment, ENNReal.rpow_eq_pow] using h

end DOZZ.Proofs
