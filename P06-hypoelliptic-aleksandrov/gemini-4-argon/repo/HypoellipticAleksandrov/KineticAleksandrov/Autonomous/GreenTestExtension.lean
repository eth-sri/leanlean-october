module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionHomogeneous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionHomogeneousError

/-! # The full actual finite-strip Green identity for the original bounded C112 class -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology

/- The original bounded C112 class has the full actual identity at every strictly interior
starting time, with no extra regularity or boundary-solution premise. -/
theorem strip_identity_C112_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (_hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  obtain ⟨u, hform, hu, hop, huc, hexit⟩ := strip_bounded_source_reconstruction
    hH hlam hLam A H E hE sMinus T phi hphi hc hb
  have hub := reconstruction_uniform_bound H E A sMinus T e he phi u hphi hb hform huc
  have hrep : u e.1 = ∫ p, u p ∂stripExitOfRealization hH hlam hLam A H E hE T e := by
    obtain ⟨M, hM, hub⟩ := hub
    let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
    have hr1 (n : ℕ) : r n ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      simp only [one_mul]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    choose F hFb hclose herr using fun n : ℕ => reconstruction_homogeneous_probe_error
      hH hlam hLam A H E hE sMinus T e he u hu hop huc M hM hub ((n : ℝ) + 1) (r n) (hr n)
    let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
    have hΩ := stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e
    have hlim : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop (𝓝 (∫ p, u p ∂Ω)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => M + 1)
      · intro n
        exact (exitProbePhysical_continuous_compact (F n)).1.measurable.aestronglyMeasurable
      · exact integrable_const _
      · intro n
        exact Filter.Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs]
          exact (hFb n p).trans (add_le_add (le_refl M) (hr1 n)))
      · filter_upwards [hΩ] with p hp
        apply Metric.tendsto_nhds.mpr
        intro eps heps
        have hnr := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds heps)
        have hnx := tendsto_natCast_atTop_atTop.eventually_ge_atTop (|p.position 0| : ℝ)
        filter_upwards [hnr, hnx] with n hn hx
        rw [Real.dist_eq]
        exact (hclose n p hp (hx.trans (by linarith))).trans_lt hn
    let Q := reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T (sectionTwoPoint e.1)
    let b (n : ℕ) := r n + (2 * M + r n) * Real.exp (-((n : ℝ) + 1)) * Q
    have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop))
    have hb0 : Tendsto b atTop (𝓝 0) := by
      simpa only [b, mul_zero, zero_mul, add_zero] using
        hr0.add (((tendsto_const_nhds.add hr0).mul hexp).mul_const Q)
    have hpole : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop (𝓝 (u e.1)) := by
      apply Metric.tendsto_nhds.mpr
      intro eps heps
      filter_upwards [hb0.eventually (gt_mem_nhds heps)] with n hn
      rw [Real.dist_eq, abs_sub_comm]
      exact (herr n).trans_lt hn
    exact tendsto_nhds_unique hpole hlim
  have hclosed : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      p ∈ stripClosedExit H T := by
    rw [ae_iff]
    exact stripExitOfRealization_compl_closedExit hH hlam hLam A H E hE T e
  have hAE : u =ᵐ[stripExitOfRealization hH hlam hLam A H E hE T e] phi := by
    filter_upwards [hclosed,
      stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e] with p hp ht
    apply hexit
    rcases hp with hp | hp
    · exact Or.inl hp
    · by_cases hpt : p.time = T
      · exact Or.inl ⟨hpt, ht.2.2⟩
      · exact Or.inr ⟨he.trans_le ht.1, lt_of_le_of_ne hp.1 hpt, hp.2⟩
  rw [integral_congr_ae hAE] at hrep
  have hh := hform e he
  rw [integral_neg] at hh
  linarith

/- The canonical autonomous families satisfy the full C112 identity at an interior pole. -/
theorem strip_identity_C112
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sMinus T : ℝ) (hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit hH hLE hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H T e :=
  strip_identity_C112_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) sMinus T hT e he phi hphi hc hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
