module

public import DOZZ.GMC.WeightedCutoff.SmallBound

/-! # Uniform fine-cutoff moments on bounded disks -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem regularizedGMC_bounded_ball_moment_compact_gamma_fine
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    Γ (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    q (hq : 1 < q) (hcrit : ∀ γ ∈ Γ, q < 4 / γ ^ 2)
    B (hB : 0 < B) :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ γ ∈ Γ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
      (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball 0 B)) ^ q ∂P) ≤ D := by
  classical
  let K : Set ℂ := Metric.closedBall 0 B
  let U := {w : ℂ // w ∈ K}
  obtain ⟨S, hcover⟩ := (isCompact_closedBall (0 : ℂ) B).elim_finite_subcover
    (fun w : U => Metric.ball (w : ℂ) (1 / 8 : ℝ)) (fun _ => Metric.isOpen_ball)
    (by intro x hx; exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by norm_num)⟩)
  have hSne : S.Nonempty := by
    have hc := hcover (show (0 : ℂ) ∈ K by simp [K]; positivity)
    simp only [Set.mem_iUnion] at hc
    obtain ⟨w, hw, _⟩ := hc
    exact ⟨w, hw⟩
  obtain ⟨A, hA, hroot⟩ := regularizedGMC_openBall_root_bound_compact_gamma_small_chart
    P X hX Xc hXc Γ hΓ hΓpos q hq hcrit
  obtain ⟨M, hM, hmove⟩ := cutoffWeightedGmcBallMoment_translate_compact P X hX Xc hXc Γ hΓ
    {(0, q)} isCompact_singleton K (isCompact_closedBall (0 : ℂ) B)
  let H := ENNReal.ofReal M * A ^ q
  let D := (S.card : ℝ≥0∞) ^ q * (S.card : ℝ≥0∞) * H
  refine ⟨D, (ENNReal.mul_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top _))) (by simp)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) hA.ne)))), ?_⟩
  intro γ hγ δ hδ hδsmall
  let μ := regularizedGMC P Xc γ (Real.log (1 / δ))
  let f : U → Ω → ℝ≥0∞ := fun w ω => μ ω (Metric.ball (w : ℂ) (1 / 8))
  have heq z ω : cutoffWeightedGmcBallMass P Xc γ 0 z (1 / 8) δ ω =
      μ ω (Metric.ball z (1 / 8)) := by simp [cutoffWeightedGmcBallMass, μ]
  have hlocal w : (∫⁻ ω, (f w ω) ^ q ∂P) ≤ H := by
    have h := hmove γ hγ (0, q) (by simp) (w : ℂ) w.property (1 / 8) δ
      (by norm_num) (by norm_num) hδ hδsmall
    simp only [heq] at h
    exact h.trans (mul_le_mul_right (by exact (ENNReal.rpow_inv_le_iff (by linarith)).mp (by simpa [μ, one_div] using ((hroot γ hγ q hq.le le_rfl 0 (1 / 8) δ (by norm_num) (by norm_num) hδ hδsmall (by norm_num)).1))) _)
  have hmass ω : μ ω (Metric.ball 0 B) ≤ ∑ w ∈ S, f w ω := by
    calc
      _ ≤ μ ω (⋃ w ∈ S, Metric.ball (w : ℂ) (1 / 8)) :=
        measure_mono (Metric.ball_subset_closedBall.trans hcover)
      _ ≤ _ := measure_biUnion_finset_le _ _
  have hmeas w : AEMeasurable (fun ω => (f w ω) ^ q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
        (Metric.ball (w : ℂ) (1 / 8)) Metric.isOpen_ball.measurableSet)
  calc
    _ ≤ ∫⁻ ω, (S.card : ℝ≥0∞) ^ q * ∑ w ∈ S, (f w ω) ^ q ∂P := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.rpow_le_rpow (hmass ω) (by linarith)).trans
        (ennreal_finset_sum_rpow_le_card_rpow_sum S hSne (fun w => f w ω) q (by linarith))
    _ = (S.card : ℝ≥0∞) ^ q * ∑ w ∈ S, ∫⁻ ω, (f w ω) ^ q ∂P := by
      rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ (fun w hw => hmeas w)),
        lintegral_finsetSum' S (f := fun w ω => (f w ω) ^ q) (fun w hw => hmeas w)]
    _ ≤ (S.card : ℝ≥0∞) ^ q * ∑ _w ∈ S, H := by
      apply mul_le_mul_right
      exact Finset.sum_le_sum (fun w hw => hlocal w)
    _ = D := by simp [D]; ac_rfl

end DOZZ.Proofs
