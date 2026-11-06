/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.CutoffGood
public import DOZZ.ShiftEquations.PoleSubtracted.IntegralHolomorphy
import Mathlib.Tactic

/-!
# Holomorphy of the cutoff family

For `n ≤ m`, `G_{m,n}(z) = E[e^{z X_m(0) - m z²/2}(B_n^{1-z/γ} - R₁^{1-z/γ})]` is holomorphic on the
half-plane `Re z > -2η - δ` ([KRV, (interpol2)]). On a closed disk in the half-plane the integrand
is dominated by the two endpoint weights of its real parts, which are integrable after the
Cameron–Martin tilt (`integrable_cutoffDomination`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The half-plane `{Re z > -2η - δ}`. -/
def cutoffHalfPlane (η δ : ℝ) : Set ℂ := {z | -2 * η - δ < z.re}

theorem isOpen_cutoffHalfPlane (η δ : ℝ) : IsOpen (cutoffHalfPlane η δ) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_cutoffHalfPlane (η δ : ℝ) : IsPreconnected (cutoffHalfPlane η δ) :=
  (convex_halfSpace_re_gt (-2 * η - δ)).isPreconnected

variable (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)

include P X hX γ hγ hγ2 M hM Xc hXc in
theorem aestronglyMeasurable_cutoffIntegrand  (η : ℝ)
    (m n : ℕ) (z : ℂ) : AEStronglyMeasurable (cutoffIntegrand Xc M γ η m n z) P := by
  have hB := aemeasurable_baseMassReal P X hX γ hγ hγ2 M hM η n
  have hL := aemeasurable_localMassReal P X hX γ hγ hγ2 M hM η
  have hXm : AEMeasurable (fun ω => Xc ω 0 m) P :=
    (measurable_circleAverage_origin hXc m).aemeasurable
  
  
  
  have h : AEMeasurable (fun ω => cutoffIntegrand Xc M γ η m n z ω) P := by
    unfold cutoffIntegrand
    fun_prop (disch := positivity)
  exact h.aestronglyMeasurable

/-- Local data of a point of the half-plane: a disk, its real range and bounds. -/
theorem cutoff_disk_bounds {γ : ℝ} (hγ : 0 < γ) {z₀ ζ : ℂ} {r : ℝ}
    (hζ : ζ ∈ closedBall z₀ r) :
    ζ.re ∈ Icc (z₀.re - r) (z₀.re + r) ∧ |ζ.im| ≤ |z₀.im| + r ∧
      ‖1 - ζ / γ‖ ≤ 1 + (‖z₀‖ + r) / γ := by
  have hd : ‖ζ - z₀‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hζ
  have hre : |ζ.re - z₀.re| ≤ r := by
    exact (Complex.abs_re_le_norm _).trans hd
  have him : |ζ.im - z₀.im| ≤ r := by
    exact (Complex.abs_im_le_norm _).trans hd
  refine ⟨⟨by linarith [neg_abs_le (ζ.re - z₀.re)], by linarith [le_abs_self (ζ.re - z₀.re)]⟩,
    ?_, ?_⟩
  · grind
  · have hζn : ‖ζ‖ ≤ ‖z₀‖ + r := by
      exact norm_le_norm_add_const_of_dist_le hζ
    calc ‖1 - ζ / γ‖ ≤ ‖(1 : ℂ)‖ + ‖ζ / γ‖ := norm_sub_le _ _
      _ = 1 + ‖ζ‖ / γ := by
          rw [norm_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
      _ ≤ 1 + (‖z₀‖ + r) / γ := by
          gcongr

include P X hX γ hγ hγ2 M hM Xc hXc in
/-- **Holomorphy of the cutoff family** on the half-plane, with integrable sections. -/
theorem differentiableOn_cutoffFamily  {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) {m n : ℕ} (hnm : n ≤ m) :
    DifferentiableOn ℂ (cutoffFamily P Xc M γ η m n) (cutoffHalfPlane η δ) ∧
      ∀ z ∈ cutoffHalfPlane η δ, Integrable (cutoffIntegrand Xc M γ η m n z) P := by
  have hgood := ae_cutoffGood P X hX γ hγ hγ2 M hM hW
  have hmeas : ∀ z ∈ cutoffHalfPlane η δ,
      AEStronglyMeasurable (cutoffIntegrand Xc M γ η m n z) P := fun z _ =>
    aestronglyMeasurable_cutoffIntegrand P X hX γ hγ hγ2 M hM Xc hXc η m n z
  have hdiff : ∀ᵐ ω ∂P, DifferentiableOn ℂ (fun z => cutoffIntegrand Xc M γ η m n z ω)
      (cutoffHalfPlane η δ) := by
    filter_upwards [hgood] with ω hω
    exact (differentiable_cutoffIntegrand Xc M γ η m n ω hω.localMassReal_pos
      (hω.localMassReal_le hγ n)).differentiableOn
  have hdom : ∀ z ∈ cutoffHalfPlane η δ, ∃ r > 0, closedBall z r ⊆ cutoffHalfPlane η δ ∧
      ∃ g : Ω → ℝ, Integrable g P ∧ ∀ᵐ ω ∂P, ∀ ζ ∈ closedBall z r,
        ‖cutoffIntegrand Xc M γ η m n ζ ω‖ ≤ g ω := by
    intro z₀ hz₀
    have hz₀' : -2 * η - δ < z₀.re := hz₀
    set r : ℝ := (z₀.re + 2 * η + δ) / 2 with hr
    have hr0 : 0 < r := by rw [hr]; linarith
    refine ⟨r, hr0, fun ζ hζ => ?_, ?_⟩
    · have := (cutoff_disk_bounds hγ hζ).1.1
      change -2 * η - δ < ζ.re
      linarith
    set a₁ : ℝ := z₀.re - r
    set a₂ : ℝ := z₀.re + r
    have ha₁ : -2 * η - δ < a₁ := by simp only [a₁, hr]; linarith
    have ha₂ : -2 * η - δ < a₂ := by simp only [a₂, hr]; linarith
    set K : ℝ := Real.exp (m * (|z₀.im| + r) ^ 2 / 2) * (1 + (‖z₀‖ + r) / γ)
    refine ⟨fun ω => K * ((baseMassReal M γ η n ω - localMassReal M γ η ω) *
        cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a₁ +
      (baseMassReal M γ η n ω - localMassReal M γ η ω) *
        cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a₂), ?_, ?_⟩
    · exact ((integrable_cutoffDomination P X hX γ hγ hγ2 M hM Xc hXc hW ha₁ hnm).add
        (integrable_cutoffDomination P X hX γ hγ hγ2 M hM Xc hXc hW ha₂ hnm)).const_mul K
    · filter_upwards [hgood] with ω hω ζ hζ
      obtain ⟨hre, him, hw⟩ := cutoff_disk_bounds hγ hζ
      refine (norm_cutoffIntegrand_le_endpoints Xc M η m n ω hω.localMassReal_pos
        (hω.localMassReal_le hγ n) hre him hw).trans (le_of_eq ?_)
      simp only [K]
      ring
  exact ⟨differentiableOn_integral_of_locally_dominated P (isOpen_cutoffHalfPlane η δ) _ hmeas
    hdiff hdom, integrable_of_locally_dominated P _ hmeas hdom⟩

end DOZZ.Proofs

end
