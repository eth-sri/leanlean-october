module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionHomogeneousError
public import PDEFoundation.Calculus.RegularityOrder


/-! # Actual exit representation of bounded smooth homogeneous solutions -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Filter
open TheoremA
open scoped Topology

/-- The uniquely characterized actual exit measure represents every bounded homogeneous
solution with the prescribed continuous future traces. -/
theorem reconstruction_homogeneous_exit_representation
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (lower T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : lower < e.1.time) (u : Point → ℝ)
    (hu : ContDiffOn ℝ PDE.smoothOrder (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
    (hop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a u p = 0)
    (hc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ M) :
    u e.1 = ∫ p, u p ∂stripExitOfRealization hH hlam hLam A H E hE T e := by
  obtain ⟨M, hM, hb⟩ := hb
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hr1 (n : ℕ) : r n ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose F hFb hclose herr using fun n : ℕ => reconstruction_homogeneous_probe_error
    hH hlam hLam A H E hE lower T e he u hu hop hc M hM hb ((n : ℝ) + 1) (r n) (hr n)



  let Q := reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T (sectionTwoPoint e.1)
  let b (n : ℕ) := r n + (2 * M + r n) * Real.exp (-((n : ℝ) + 1)) * Q
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop))


  exact tendsto_nhds_unique (by
      apply Metric.tendsto_nhds.mpr
      intro eps heps
      filter_upwards [(show Tendsto b atTop (𝓝 0) by
          simpa only [b, mul_zero, zero_mul, add_zero] using
            hr0.add (((tendsto_const_nhds.add hr0).mul hexp).mul_const Q)).eventually (gt_mem_nhds heps)] with n hn
      rw [Real.dist_eq, abs_sub_comm]
      exact (herr n).trans_lt hn) (by
      apply tendsto_integral_of_dominated_convergence (fun _ => M + 1)
      · intro n
        exact (exitProbePhysical_continuous_compact (F n)).1.measurable.aestronglyMeasurable
      · exact integrable_const _
      · intro n
        exact Filter.Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs]
          exact (hFb n p).trans (add_le_add (le_refl M) (hr1 n)))
      · filter_upwards [(stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e)] with p hp
        apply Metric.tendsto_nhds.mpr
        intro eps heps


        filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds heps)), (tendsto_natCast_atTop_atTop.eventually_ge_atTop (|p.position 0| ))] with n hn hx
        rw [Real.dist_eq]
        exact (hclose n p hp (hx.trans (by linarith))).trans_lt hn)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
