module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionSpatialTail
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionTraceApproximation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionUniformBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGap
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.TietzeExtension

/-! # Actual exit-probe approximation of a bounded smooth homogeneous solution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open Topology
open scoped CompactlySupported

/- A bounded homogeneous solution is approximated at its pole by actual compact exit
integrals, with a proved exponentially vanishing spatial-tail error. -/
theorem reconstruction_homogeneous_probe_error
    (hH : HormanderHypoellipticityStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (lower T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : lower < e.1.time) (u : Point → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
    (hop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a u p = 0)
    (hc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (M ) (hM : 0 ≤ M)
    (hb : ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ M)
    (R eps : ℝ) (heps : 0 < eps) :
    ∃ F : exitProbeSubmodule,
      (∀ p, |exitProbePhysical F p| ≤ M + eps) ∧
      (∀ p ∈ reconstructionClosedSlab H e.1.time T, |p.position 0| ≤ R →
        |exitProbePhysical F p - u p| ≤ eps) ∧
      |u e.1 - ∫ p, exitProbePhysical F p ∂stripExitOfRealization hH hlam hLam A H E hE T e| ≤
        eps + (2 * M + eps) * Real.exp (-R) *
          reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T (sectionTwoPoint e.1) := by
  have hT := WithTop.coe_lt_coe.mp e.2.1
  obtain ⟨F, hFb, hclose⟩ : ∃ F : exitProbeSubmodule,
      (∀ p, |exitProbePhysical F p| ≤ M + eps) ∧
      ∀ p ∈ reconstructionClosedSlab H e.1.time T, |p.position 0| ≤ R →
        |exitProbePhysical F p - u p| ≤ eps := by
    let a := e.1.time
    have hc := (hc.mono (reconstructionClosedSlab_subset_strip_union_exit H he))
    let D := reconstructionClosedSlab H a T
    have hD : IsClosed D := by
      change IsClosed (reconstructionClosedSlab H a T)
      rw [← closure_reconstructionStrip H a T hT]
      exact isClosed_closure
    let f : BoundedContinuousFunction D ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => u p.1) (continuousOn_iff_continuous_domRestrict.mp hc) M
      (fun p => by rw [Real.norm_eq_abs]; exact hb p.1 p.2)
    let j : D → EvolutionVec 1 := fun p => reconstructionPhysicalHomeomorph.symm p.1
    have hj : IsClosedEmbedding j := reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp
      hD.isClosedEmbedding_subtypeVal
    obtain ⟨G, hGb, hG⟩ :=
      BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_isClosedEmbedding f
        (fun p => abs_le.mp (hb p.1 p.2)) (by linarith) hj
    let pack (q : ℝ × ℝ × ℝ) : EvolutionVec 1 :=
      packPoint q.1 (fun _ => q.2.2) (fun _ => q.2.1)
    let K := pack '' (Icc a T ×ˢ (Icc (-R) R ×ˢ Icc H.lo H.hi))
    have hp : Continuous pack := by
      change Continuous (fun q : ℝ × ℝ × ℝ =>
        (evolutionProdCLE 1).symm (q.1, (fun _ => q.2.2), (fun _ => q.2.1)))
      exact (evolutionProdCLE 1).symm.continuous.comp
        (continuous_fst.prodMk ((continuous_pi fun _ => continuous_snd.snd).prodMk
          (continuous_pi fun _ => continuous_snd.fst)))
    have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image hp
    obtain ⟨chi, hchi, hcc, _, hcb, hone⟩ :=
      exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
    let g : C_c(EvolutionVec 1, ℝ) :=
      ⟨⟨fun x => chi x * G x, hchi.continuous.mul G.continuous⟩, hcc.mul_right⟩
    obtain ⟨s, hs, hclose⟩ := exists_smooth_compact_probe_close g eps heps
    let F : exitProbeSubmodule := ⟨s, hs, s.hasCompactSupport⟩
    have hg (x : EvolutionVec 1) : |g x| ≤ M := by
      change |chi x * G x| ≤ M
      rw [abs_mul, abs_of_nonneg (hcb x).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hcb x).2).trans (abs_le.mpr (hGb x))
    refine ⟨F, ?_, ?_⟩
    · intro p
      have hh := (abs_add_le (s (reconstructionPhysicalHomeomorph.symm p) -
        g (reconstructionPhysicalHomeomorph.symm p)) (g (reconstructionPhysicalHomeomorph.symm
          p))).trans
          (add_le_add (hclose _) (hg _))
      change |s (reconstructionPhysicalHomeomorph.symm p)| ≤ _
      rw [sub_add_cancel] at hh
      exact hh.trans_eq (add_comm eps M)
    · intro p hpd hpr
      have hpk : reconstructionPhysicalHomeomorph.symm p ∈ K := by
        refine ⟨(p.time, p.position 0, p.velocity 0),
          ⟨⟨hpd.1, hpd.2.1⟩, abs_le.mp hpr, hpd.2.2⟩, ?_⟩
        ext i
        fin_cases i <;> rfl
      have hGp : G (reconstructionPhysicalHomeomorph.symm p) = u p :=
        congrFun hG ⟨p, hpd⟩
      have hgp : g (reconstructionPhysicalHomeomorph.symm p) = u p := by
        change chi _ * G _ = _
        rw [hone _ hpk, one_mul, hGp]
      change |s (reconstructionPhysicalHomeomorph.symm p) - u p| ≤ _
      rw [← hgp]
      exact hclose _
  have hFc := (exitProbePhysical_continuous_compact F).1
  have hFr := exitProbePhysical_isKineticC112On F (reconstructionStrip H lower T)
    (isOpen_reconstructionStrip H lower T)
  obtain ⟨C, hC⟩ := exitProbePhysical_bounded_source A F
  have hFs : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H lower T,
      |exitProbePhysical F p| ≤ M ∧ |forwardScalarOperator A.a (exitProbePhysical F) p| ≤ M :=
    ⟨C, fun p _ => hC p⟩
  obtain ⟨v, hvform, hvs, hvop, hvc, hvexit⟩ := strip_bounded_source_reconstruction
    hH hlam hLam A H E hE lower T (exitProbePhysical F) hFr hFc.continuousOn hFs
  obtain ⟨Mv, _, hvb⟩ := reconstruction_uniform_bound H E A lower T e he
    (exitProbePhysical F) v hFr hFs hvform hvc
  let k := (2 * M + eps) * Real.exp (-R)
  let q := fun p => k * reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T p
  have hk : 0 ≤ k := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hqn (p : Point) : 0 ≤ q p := mul_nonneg hk
    (mul_nonneg (Real.exp_pos _).le (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
  have hqc : Continuous q := continuous_const.mul (reconstructionSpatialBarrier_continuous _ _)
  have hqr (p : Point) : IsSliceRegularAt q p :=
    (reconstructionSpatialBarrier_regular _ _ p).const_mul k
  have hqo (p : Point) (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) q p ≤ 0 := by
    rw [← viscousTransportedOperator_zero,
      viscousTransportedOperator_const_mul k (reconstructionSpatialBarrier_regular _ _ p),
      viscousTransportedOperator_zero]
    have hh := reconstructionSpatialBarrier_operator_le A.a H T p hp
    have hw : 0 ≤ reconstructionSpatialWeight (p.velocity 0) :=
      add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    exact mul_nonpos_of_nonneg_of_nonpos hk (hh.trans (neg_nonpos.mpr hw))
  have hbd (p : Point) (hp : p ∈ stripClosedExit H T) (ht : e.1.time ≤ p.time) :
      |u p - v p| ≤ eps + q (sectionTwoPoint p) := by
    have hslab : p ∈ reconstructionClosedSlab H e.1.time T := by
      rcases hp with hp | hp
      · exact ⟨ht, hp.1.le, hp.2⟩
      · refine ⟨ht, hp.1, ?_⟩
        rcases hp.2 with hv | hv <;> rw [hv]
        · exact ⟨le_rfl, H.ordered.le⟩
        · exact ⟨H.ordered.le, le_rfl⟩
    have hexit : p ∈ reconstructionExit H lower T := by
      rcases hp with hp | hp
      · exact Or.inl hp
      · by_cases hpt : p.time = T
        · exact Or.inl ⟨hpt, hslab.2.2⟩
        · exact Or.inr ⟨he.trans_le ht, lt_of_le_of_ne hp.1 hpt, hp.2⟩
    rw [hvexit hexit]
    by_cases hx : |p.position 0| ≤ R
    · have hh := hclose p hslab hx
      rw [abs_sub_comm] at hh
      exact hh.trans (le_add_of_nonneg_right (hqn _))
    · have hh := (abs_sub _ _).trans (add_le_add (hb p hslab) (hFb p))
      have htail := reconstructionSpatialBarrier_tail H T R (2 * M + eps)
        (by linarith) (sectionTwoPoint p) hslab.2.1 (not_le.mp hx).le
      change 2 * M + eps ≤ q (sectionTwoPoint p) at htail
      exact hh.trans ((by linarith : M + (M + eps) ≤ 2 * M + eps).trans
        (htail.trans (le_add_of_nonneg_left heps.le)))
  have hupper := reconstruction_homogeneous_gap_le_barrier hlam A H lower T e he
    u v hu hvs hop hvop hc hvc M Mv hb hvb eps q hqc hqr hqn hqo
    (fun p hp ht => (le_abs_self _).trans (hbd p hp ht))
  have hlower := reconstruction_homogeneous_gap_le_barrier hlam A H lower T e he
    v u hvs hu hvop hop hvc hc Mv M hvb hb eps q hqc hqr hqn hqo
    (fun p hp ht => by
      have hh := hbd p hp ht
      rw [abs_sub_comm] at hh
      exact (le_abs_self _).trans hh)
  have hval : v e.1 = ∫ p, exitProbePhysical F p
      ∂stripExitOfRealization hH hlam hLam A H E hE T e := by
    have hh := hvform e he
    rw [integral_neg] at hh
    have hi := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e F
    unfold exitProbeValue at hi
    linarith
  refine ⟨F, hFb, hclose, ?_⟩
  rw [← hval]
  exact abs_le.mpr ⟨by linarith, hupper⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
