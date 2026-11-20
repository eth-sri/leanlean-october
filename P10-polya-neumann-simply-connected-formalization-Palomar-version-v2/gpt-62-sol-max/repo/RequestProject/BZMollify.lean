module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import RequestProject.BZMono

/-!
# Smoothing a transversal Lipschitz function (towards External theorem BZ)

Convolving a `2`-Lipschitz function `d` with a normalized bump of radius `δ` gives a smooth
`2`-Lipschitz function `ρ` with `|ρ - d| ≤ 2δ`, which is still transversal to a Lipschitz field
`X` (at the slightly smaller rate `κ - 2 L_X δ`) on the points whose `δ`-ball lies in the region
of transversality of `d` (`exists_smooth_transversal`).
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff Convolution

noncomputable section

namespace PolyaNeumann

section bump

variable (η : ContDiffBump (0 : ℂ))

lemma integrable_normed_mul {A : ℂ → ℝ} (hA : Continuous A) :
    Integrable (fun t => η.normed volume t * A t) volume :=
  (η.continuous_normed.mul hA).integrable_of_hasCompactSupport
    (η.hasCompactSupport_normed.mul_right)

lemma integral_normed_mul_le {A B : ℂ → ℝ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ t : ℂ, ‖t‖ < η.rOut → A t ≤ B t) :
    ∫ t, η.normed volume t * A t ≤ ∫ t, η.normed volume t * B t := by
  refine integral_mono (integrable_normed_mul η hA) (integrable_normed_mul η hB) fun t => ?_
  by_cases ht : ‖t‖ < η.rOut
  exact mul_le_mul_of_nonneg_left (h t ht) (η.nonneg_normed t)
  · have : η.normed volume t = 0 := by
      rw [← Function.notMem_support, η.support_normed_eq, mem_ball, dist_zero_right]
      exact ht
    simp_all

lemma integral_normed_mul_add_const {A : ℂ → ℝ} (hA : Continuous A) (c : ℝ) :
    ∫ t, η.normed volume t * (A t + c) = (∫ t, η.normed volume t * A t) + c := by
  simp_rw [mul_add]
  rw [integral_add (integrable_normed_mul η hA) (integrable_normed_mul η continuous_const),
    integral_mul_const, η.integral_normed, one_mul]

end bump

/-- Mollification of a Lipschitz transversal function. -/
theorem exists_smooth_transversal {d : ℂ → ℝ} {L : ℝ≥0} (hd : LipschitzWith L d) {X : ℂ → ℂ}
    {LX : ℝ≥0} (hX : LipschitzWith LX X) {U : Set ℂ} {τ κ : ℝ}
    (hQ : IsTransversalOn d X U τ κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℂ → ℝ, ContDiff ℝ ∞ ρ ∧ LipschitzWith L ρ ∧ (∀ x, |ρ x - d x| ≤ (L : ℝ) * δ) ∧
      IsTransversalOn ρ X {z | ∀ t : ℂ, ‖t‖ < δ → z - t ∈ U} τ (κ - L * LX * δ) := by
  set η : ContDiffBump (0 : ℂ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hηr : η.rOut = δ := rfl
  have hdc := hd.continuous
  set ρ : ℂ → ℝ := fun x => ∫ t, η.normed volume t * d (x - t)
  have hρeq : ρ = η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] d := by
    rfl
  have hcont : ∀ x : ℂ, Continuous fun t : ℂ => d (x - t) := fun x => by fun_prop
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · rw [hρeq]
    exact η.hasCompactSupport_normed.contDiff_convolution_left _ η.contDiff_normed
      (hdc.locallyIntegrable)
  · refine LipschitzWith.of_le_add_mul L fun x y => ?_
    have h := integral_normed_mul_le η (B := fun t => d (y - t) + (L : ℝ) * dist x y)
      (hcont x) ((hcont y).add continuous_const)
      (fun t _ => by
        have h₁ := hd.dist_le_mul (x - t) (y - t)
        rw [dist_sub_right, Real.dist_eq] at h₁
        linarith [le_abs_self (d (x - t) - d (y - t))])
    rwa [integral_normed_mul_add_const η (hcont y)] at h
  · intro x
    rw [← Real.dist_eq, hρeq]
    exact η.dist_normed_convolution_le hdc.aestronglyMeasurable
      (fun y hy => (hd.dist_le_mul y x).trans (by gcongr; exact le_of_lt hy))
  · intro z hz s hs0 hsτ
    have := integral_normed_mul_le η (A := fun t => d (z - t) + (κ - L * LX * δ) * s)
      (B := fun t => d (z + s * X z - t)) ((hcont z).add continuous_const) (hcont (z + s * X z))
      (fun t ht => by
        rw [hηr] at ht
        have hU := hz t ht
        have h1 := hQ (z - t) hU s hs0 hsτ
        have h2 := hd.dist_le_mul (z + s * X z - t) (z - t + s * X (z - t))
        rw [Real.dist_eq, dist_eq_norm,
          show z + s * X z - t - (z - t + s * X (z - t)) = s * (X z - X (z - t)) by ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0] at h2
        have h3 : ‖X z - X (z - t)‖ ≤ LX * δ := by
          rw [← dist_eq_norm]
          refine (hX.dist_le_mul _ _).trans ?_
          rw [dist_eq_norm, show z - (z - t) = t by ring]
          gcongr
        have h4 := (neg_abs_le _).trans' (neg_le_neg h2)
        have h5 := mul_le_mul_of_nonneg_left h3 hs0
        push_cast at h4 ⊢
        nlinarith)
    rw [integral_normed_mul_add_const η (hcont z)] at this
    simp  [ρ]
    assumption

end PolyaNeumann

end
