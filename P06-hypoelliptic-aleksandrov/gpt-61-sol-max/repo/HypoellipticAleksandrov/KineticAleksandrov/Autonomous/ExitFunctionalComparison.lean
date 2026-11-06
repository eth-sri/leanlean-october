module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalGeometry
public import PDEFoundation.Calculus.RegularityOrder


/-! # Boundary comparison for actual homogeneous Green reconstructions -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology

/-- Bounded regular tests with ordered exit values have the same order at the actual
homogeneous reconstruction value. This uses the proved pointwise reconstruction. -/
theorem reconstruction_boundary_comparison
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : Continuous phi)
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M)
    (M : ℝ) (hM : ∀ p, |phi p| ≤ M) (c : ℝ)
    (hbd : ∀ p ∈ stripClosedExit H T, phi p ≤ c) :
    phi e.1 - ∫ p, -forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e ≤ c := by
  obtain ⟨g, f, hg, hg0, hf, heq, hop⟩ :=
    exists_reconstruction_smooth_pointwise hH hlam hLam A H E hE sMinus T phi hphi hb
  let u := stripReconstructionCandidate H E.2 T phi g
  let D := sectionTwoPoint ⁻¹' reconstructionStrip H sMinus T

  have hD  := (isOpen_reconstructionStrip H sMinus T).preimage
    (continuous_sectionTwoPoint 1)
  have hU  := (isOpen_reconstructionStrip H sMinus T).preimage
    continuous_reconstructionPhysicalPoint
  have hsm : ContDiffOn ℝ PDE.smoothOrder ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' D) := hf.congr (fun x hx => heq hx)
  have hreg (p : Point) (hp : p ∈ D)  :=
    reconstruction_slice_regular_of_contDiffOn hD hsm p hp
  have huop (p : Point) (hp : p ∈ D) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        (u ∘ sectionTwoPoint) p = 0 := by
    let x := (evolutionHomeomorph 1).symm p
    have hx : x ∈ (reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T) := by
      change sectionTwoPoint (evolutionHomeomorph 1 x) ∈ reconstructionStrip H sMinus T
      rwa [Homeomorph.apply_symm_apply]
    have hh  :=
      Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => heq hy)
    have hj : ContDiffAt ℝ 2 ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x :=
      (hsm.contDiffAt ((hD.preimage (evolutionHomeomorph 1).continuous).mem_nhds hx)).of_le
        (by simp)
    have ht := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hj
    change transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
      (u ∘ reconstructionPhysicalPoint) x = _ at ht
    rw [reconstruction_transportedOperator_congr _ _ hh, hop x hx] at ht
    simpa only [x, Homeomorph.apply_symm_apply] using ht.symm
  let a := e.1.time
  have hactive : movingActiveSlab (intervalDomain H) (fun _ => 0) a T ⊆ D := by
    intro p hp
    refine ⟨he.trans_le hp.1, hp.2.1, ?_⟩
    simpa only [Interval.carrier, sectionTwoPoint, intervalDomain, mem_movingDomain_iff, sub_zero,
      PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate] using hp.2.2
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  have hcand := reconstruction_candidate_continuousOn_exit hH hlam hLam A H E hE
    sMinus T phi hphi hc.continuousOn g hg

  have hmax := growth_comparison
    (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)) continuous_const
    hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
    (le_refl 0) zero_le_one (a := a) (T := T)
    (u := fun p => u (sectionTwoPoint p) - c)
    ⟨M + C * (T - a) + |c|, fun p hp => by
      let sharedTerm_340065da62 := ((stripSourcePotential H E.2 T g (sectionTwoPoint p)))
      have hv := reconstruction_potential_abs_le_time H E.2 T g C hC hgb (sectionTwoPoint p)
      have ht  := max_le
        (sub_le_sub_left hp.1 T) (sub_nonneg.mpr (WithTop.coe_lt_coe.mp e.2.1).le)




      change phi (sectionTwoPoint p) - sharedTerm_340065da62 - c ≤ _
      change |sharedTerm_340065da62| ≤ C * max (T - p.time) 0 at hv
      linarith only [hv, (mul_le_mul_of_nonneg_left ht hC), ((le_abs_self (phi (sectionTwoPoint p))).trans (hM _)), (neg_le_abs sharedTerm_340065da62), (neg_le_abs c)]⟩
    ((hcand.comp (continuous_sectionTwoPoint 1).continuousOn (reconstruction_closedSlab_mapsTo H he)).sub continuousOn_const)
    (fun p hp => (hreg p (hactive hp)).sub (IsSliceRegularAt.const c p))
    (fun p hp => by
      change 0 ≤ viscousTransportedOperator (evolutionCoefficient A.a) (identityDrift 1) 0
        (fun q => (u ∘ sectionTwoPoint) q - (fun _ : Point => c) q) p
      rw [viscousTransportedOperator_sub (hreg p (hactive hp)) (IsSliceRegularAt.const c p),
        viscousTransportedOperator_zero, huop p (hactive hp), viscousTransportedOperator_const]
      norm_num)
    (fun p hp hpt => by
      have hv := intervalDomain_closure_bounds H (by
        simpa only [mem_closure_movingDomain_iff, sub_zero] using hp.2.2)
      have hn : sectionTwoPoint p ∉ stripPast H T := fun hh =>
        (by simpa only [sectionTwoPoint, hpt] using hh.1 : T < T).false

      change phi (sectionTwoPoint p) - stripSourcePotential H E.2 T g (sectionTwoPoint p) - c ≤ 0
      rw [(reconstruction_potential_zero_outside H E.2 T g _ hn), sub_zero]
      exact sub_nonpos.mpr (hbd _ (Or.inl ⟨hpt, hv⟩)))
    (fun p hp hpf => by

      have hv := reconstruction_interval_frontier_eq H (by
          simpa only [movingDomain, PDE.translateSet_zero] using hpf)


      change phi (sectionTwoPoint p) - stripSourcePotential H E.2 T g (sectionTwoPoint p) - c ≤ 0
      rw [(reconstruction_potential_zero_outside H E.2 T g _ (show sectionTwoPoint p ∉ stripPast H T by
          intro h
          rcases hv with hv | hv
          · exact (lt_irrefl H.lo) (hv ▸ h.2.1)
          · exact (lt_irrefl H.hi) (hv ▸ h.2.2))), sub_zero]
      exact sub_nonpos.mpr (hbd _ (Or.inr ⟨hp.2.1, hv⟩)))
  have hp : sectionTwoPoint e.1 ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T :=
    ⟨le_rfl, (WithTop.coe_lt_coe.mp e.2.1).le, subset_closure (stripPoleState H T e).2.1⟩
  have hres := sub_nonpos.mp (hmax _ hp)

  change phi e.1 - stripSourcePotential H E.2 T g e.1 ≤ c at hres
  rw [stripSourcePotential_eq_green H E.2 T g e, stripPotentialOfKernel,
    integral_congr_ae (by
        filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
          reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
        exact hg p ⟨he.trans ht, hp⟩)] at hres
  exact hres

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
