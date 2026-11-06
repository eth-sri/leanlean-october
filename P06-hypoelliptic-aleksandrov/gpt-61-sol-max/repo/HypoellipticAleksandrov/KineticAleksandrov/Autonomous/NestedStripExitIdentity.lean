module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripHomogeneous
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation

/-! # Actual homogeneous larger-exit potentials satisfy the smaller exit equation -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Parabolic

/-- The larger strip's genuine homogeneous exit potential restricts to the smaller equation.
The potential and all its regularity and bounds are produced internally from reconstruction. -/
theorem exists_nested_exit_potential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (f : exitProbeSubmodule) :
    ∃ u : Point → ℝ,
      ContinuousOn u (reconstructionClosedSlab H2 sMinus T) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H2 sMinus T, |u p| ≤ C) ∧
      EqOn u (exitProbePhysical f) (reconstructionExit H2 (sMinus - 1) T) ∧
      (∀ ep : StripPole H2 (T : WithTop ℝ), sMinus ≤ ep.1.time →
        u ep.1 = ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T ep) ∧
      (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T
        (nestedPoleInclusion H1 H2 hsub T e)) =
          ∫ p, u p ∂stripExit hH hLE hlam hLam A H1 T e := by
  have ht  := WithTop.coe_lt_coe.mp e.2.1
  obtain ⟨u, hu, hop, hc, ⟨C, hC, hb⟩, htrace, hrep⟩ :=
    exists_nested_homogeneous_potential hH hLE hlam hLam A H2 sMinus T (he.trans ht) f
  have hi : reconstructionStrip H1 sMinus T ⊆ reconstructionStrip H2 (sMinus - 1) T := by
    intro p hp
    exact ⟨by linarith [hp.1], hp.2.1, hsub hp.2.2⟩
  have hsmall : IsKineticC112On u (reconstructionStrip H1 sMinus T) :=
    ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
      fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
      hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
      hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩
  have hclosed : reconstructionStrip H1 sMinus T ∪ reconstructionExit H1 sMinus T ⊆
      reconstructionClosedSlab H2 sMinus T := by
    intro p hp

    refine ⟨?_, (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T hp)⟩
    rcases hp with hp | hp
    · exact hp.1.le
    · rcases hp with hp | hp
      · rw [hp.1]; exact (he.trans ht).le
      · exact hp.1.le

  have hid := strip_identity_C112 hH hLE hlam hLam A H1 sMinus T (he.trans ht)
    e he u hsmall (hc.mono hclosed) (by
        refine ⟨C, fun p hp => ⟨hb p (hclosed (Or.inl hp)), ?_⟩⟩
        rw [hop p (hi hp), abs_zero]
        exact hC)

  rw [integral_congr_ae (show (fun p => forwardScalarOperator A.a u p) =ᵐ[
      stripGreen hH hLE hlam hLam A H1 T e] fun _ => 0 by
      filter_upwards [stripGreenOfKernel_ae_mem_stripPast H1
        _ T e,
        reconstruction_green_ae_time_gt H1 _ T e]
        with p hp hpt
      apply hop
      exact hi ⟨he.trans hpt, hp⟩), integral_zero, sub_zero] at hid
  refine ⟨u, hc, ⟨C, hC, hb⟩, htrace, hrep, ?_⟩
  rw [← hrep (nestedPoleInclusion H1 H2 hsub T e) he.le]
  exact hid

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
