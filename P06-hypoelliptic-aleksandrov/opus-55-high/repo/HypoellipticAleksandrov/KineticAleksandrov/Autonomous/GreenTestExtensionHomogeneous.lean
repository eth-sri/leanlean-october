module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionHomogeneousError

/-! # Actual exit representation of bounded smooth homogeneous solutions -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology

/-- The uniquely characterized actual exit measure represents every bounded homogeneous
solution with the prescribed continuous future traces. -/
theorem reconstruction_homogeneous_exit_representation
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (lower T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : lower < e.1.time) (u : Point → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
    (hop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a u p = 0)
    (hc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ M) :
    u e.1 = ∫ p, u p ∂stripExitOfRealization hH hlam hLam A H E hE T e := by
  obtain ⟨M, hM, hb⟩ := hb
  let r (n : ℕ)  := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by positivity
  have hr1 (n : ℕ) : r n ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simp
  choose F hFb hclose herr using fun n : ℕ => reconstruction_homogeneous_probe_error
    hH hlam hLam A H E hE lower T e he u hu hop hc M hM hb (n + 1) _ (hr n)
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  have hΩ := stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e
  have hlim : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop (𝓝 (∫ p, u p ∂Ω)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M + 1)
    · intro n
      exact (exitProbePhysical_continuous_compact _).1.measurable.aestronglyMeasurable
    · fun_prop
    · intro n
      exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs]
        grind)
    · filter_upwards [hΩ] with p hp
      apply Metric.tendsto_nhds.mpr
      intro eps heps
      have hnr := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds heps)
      have hnx := tendsto_natCast_atTop_atTop.eventually_ge_atTop (|p.position 0|)
      filter_upwards [hnr, hnx] with n hn hx
      exact (hclose n p hp (hx.trans (by linarith))).trans_lt hn
  let Q := reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T (sectionTwoPoint e.1)
  let b (n : ℕ) := r n + (2 * M + r n) * Real.exp (-(n + 1)) * Q
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n + 1))) atTop _ :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop _
        tendsto_natCast_atTop_atTop))
  have hb0 : Tendsto b atTop (𝓝 0) := by
    simpa only [b, mul_zero, zero_mul, add_zero] using
      hr0.add (((tendsto_const_nhds.add hr0).mul hexp).mul_const Q)
  have hpole : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop (𝓝 (u e.1)) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hb0.eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq]
    grind
  exact tendsto_nhds_unique hpole hlim

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
