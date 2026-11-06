/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.SharpMoments.WeightedCutoffCompact
public import DOZZ.GMC.SharpMoments.SeibergUniform

/-! Uniform decay and zero-charge disk estimates shared by the Coulomb cutoff bounds. -/
public section
open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Admissibility makes the weighted scaling exponent positive. -/
theorem weightedCutoff_exponent_pos {γ α t : ℝ}
    (h : 0 < weightedCutoffSlack (γ, α, t)) :
    0 < γ * (Q γ - α) * t - γ ^ 2 * t ^ 2 / 2 := by
  obtain ⟨hγ, _, _, ht, hlt⟩ := (weightedCutoffSlack_pos_iff _).mp h
  have h1 : γ * t / 2 < Q γ - α := by
    have h2 := mul_lt_mul_of_pos_left (lt_min_iff.mp hlt).2 (half_pos hγ)
    have he : γ / 2 * (2 / γ * (Q γ - α)) = Q γ - α := by field_simp
    rw [he] at h2
    linarith
  convert mul_pos (mul_pos hγ ht) (sub_pos.mpr h1) using 1 <;> ring

/-- Compact admissible families have a common positive lower bound for their exponent. -/
theorem weightedCutoff_exponent_eventually
    {A : Type*} [TopologicalSpace A] {S : Set A} (hS : IsCompact S)
    (φ : A → ℝ × ℝ × ℝ) (hφ : ContinuousOn φ S)
    (h : ∀ c ∈ S, 0 < weightedCutoffSlack (φ c)) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), ∀ c ∈ S,
      κ ≤ (φ c).1 * (Q (φ c).1 - (φ c).2.1) * (φ c).2.2 -
        (φ c).1 ^ 2 * (φ c).2.2 ^ 2 / 2 := by
  have he := eventually_le_of_isCompact_of_pos (hS.image_of_continuousOn hφ)
    (f := fun q : ℝ × ℝ × ℝ => q.1 * (Q q.1 - q.2.1) * q.2.2 - q.1 ^ 2 * q.2.2 ^ 2 / 2)
    (by
      rintro q ⟨c, hc, rfl⟩
      have hn := ((weightedCutoffSlack_pos_iff _).mp (h c hc)).1.ne'
      apply ContinuousAt.continuousWithinAt
      unfold Q
      fun_prop (disch := assumption))
    (by rintro q ⟨c, hc, rfl⟩; exact weightedCutoff_exponent_pos (h c hc))
  filter_upwards [he] with κ hκ c hc
  exact hκ _ ⟨c, hc, rfl⟩

/-- The bulk threshold always lies below the zero-charge insertion threshold. -/
theorem weightedCutoffSlack_zero_pos {γ t : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (ht : 0 < t) (ht4 : t < 4 / γ ^ 2) : 0 < weightedCutoffSlack (γ, 0, t) := by
  refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ, hγ2, ?_, ht, lt_min ht4 ?_⟩
  · unfold Q; positivity
  · have h : 4 / γ ^ 2 < 2 / γ * (Q γ - 0) := by
      rw [sub_zero, Q]
      field_simp
      linarith only [pow_pos hγ 2]
    exact ht4.trans h

/-- A coarse zero-charge exponent bound on the subcritical interval. -/
theorem weightedCutoff_zero_exponent_le {γ t tm : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (ht : 0 < t) (htm : t ≤ tm) : γ * (Q γ - 0) * t - γ ^ 2 * t ^ 2 / 2 ≤ 4 * tm := by
  have hQ : γ * Q γ = 2 + γ ^ 2 / 2 := by rw [Q]; field_simp
  have hγsq := pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero
  have hQt : γ * (Q γ - 0) * t = (2 + γ ^ 2 / 2) * t := by rw [sub_zero, hQ]
  have h1 := mul_lt_mul_of_pos_right hγsq ht
  have h2 : 0 ≤ γ ^ 2 * t ^ 2 := by positivity
  linarith only [hQt, h1, h2, htm]

/-- A cutoff weighted mass with zero charge is a cutoff disk mass. -/
private theorem cutoffWeightedGmcBallMass_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (z : ℂ) (R r : ℝ) (ω : Ω) :
    cutoffWeightedGmcBallMass P Xc γ 0 z R (Real.exp (-r)) ω =
      regularizedGMC P Xc γ r ω (Metric.ball z R) := by
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  rw [cutoffWeightedGmcBallMass, hlog]
  simp

/-- Uniform cutoff disk moments follow from the zero-charge weighted estimate. -/
theorem regularizedGMC_disk_moment_uniform_compact
    {Ω A : Type*} [MeasurableSpace Ω] [TopologicalSpace A]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {S : Set A} (hS : IsCompact S) (γ τ : A → ℝ)
    (hγc : ContinuousOn γ S) (hτ : ContinuousOn τ S)
    (hadm : ∀ c ∈ S, 0 < γ c ∧ γ c < 2 ∧ 0 < τ c ∧ τ c < 4 / γ c ^ 2)
    {tm Rm : ℝ} (htm : 0 ≤ tm) (hτm : ∀ c ∈ S, τ c ≤ tm) (hRm : 1 ≤ Rm) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ S, ∀ R : ℝ, 1 ≤ R → R ≤ Rm → ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, regularizedGMC P Xc (γ c) r ω (Metric.ball 0 R) ^ τ c ∂P ≤
        ENNReal.ofReal (C * Rm ^ (4 * tm)) := by
  have hcont : ContinuousOn (fun c => (γ c, (0 : ℝ), τ c)) S :=
    hγc.prodMk (continuousOn_const.prodMk hτ)
  obtain ⟨C, hC, hCb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
    (hS.image_of_continuousOn hcont)
    (by rintro q ⟨c, hc, rfl⟩; obtain ⟨hg, hg2, ht, ht4⟩ := hadm c hc
        exact weightedCutoffSlack_zero_pos hg hg2 ht ht4)
    (closedBall 0 0) (isCompact_closedBall _ _) Rm (by linarith)
  refine ⟨C, hC, fun c hc R hR hRR r hr => ?_⟩
  obtain ⟨hg, hg2, ht, _⟩ := hadm c hc
  have hδ : Real.exp (-r) ≤ R := (Real.exp_le_one_iff.mpr (by linarith)).trans hR
  have h := hCb _ ⟨c, hc, rfl⟩ 0 (mem_closedBall_self le_rfl) (Real.exp (-r)) R
    (Real.exp_pos _) hδ hRR
  simp only [cutoffWeightedGmcBallMass_zero] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le))
  exact (Real.rpow_le_rpow_of_exponent_le hR (weightedCutoff_zero_exponent_le hg hg2 ht (hτm c hc))).trans
    (Real.rpow_le_rpow (by linarith) hRR (mul_nonneg (by norm_num) htm))

end DOZZ.Proofs
