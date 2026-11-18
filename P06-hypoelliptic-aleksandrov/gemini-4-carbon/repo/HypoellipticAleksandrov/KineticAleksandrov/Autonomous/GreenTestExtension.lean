module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitCone
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov SectionTwo TheoremA Evolution Topology MeasureTheory Filter Parabolic
open scoped CompactlySupported Topology


/-- The full physical closed slab at finite times. -/
def reconstructionClosedSlab (H : Interval) (a T : ℝ) : Set Point :=
  {p | a ≤ p.time ∧ p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi}

/-- The closure of a nonempty physical open strip is its literal closed slab. -/
theorem closure_reconstructionStrip (H : Interval) (a T : ℝ) (ha : a < T) :
    closure (reconstructionStrip H a T) = reconstructionClosedSlab H a T  := by
  let S : Set (ℝ × ℝ × ℝ) := Ioo a T ×ˢ (univ ×ˢ Ioo H.lo H.hi)
  have heq : reconstructionStrip H a T = (((Homeomorph.refl ℝ).prodCongr (PDE.scalarToVecOneContinuousLinearEquiv.toHomeomorph.prodCongr PDE.scalarToVecOneContinuousLinearEquiv.toHomeomorph)).trans (KineticPoint.homeomorphProd 1).symm) '' S := by
    ext p
    constructor
    · intro hp
      refine ⟨(p.time, p.position 0, p.velocity 0), ⟨⟨hp.1, hp.2.1⟩, mem_univ _, hp.2.2⟩, ?_⟩
      refine KineticPoint.ext rfl ?_ ?_
      · funext i
        fin_cases i
        rfl
      · funext i
        fin_cases i
        rfl
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1.1, hq.1.2, hq.2.2⟩
  rw [heq, ← Homeomorph.image_closure]
  dsimp only [S]
  rw [closure_prod_eq, closure_prod_eq, closure_Ioo ha.ne, closure_univ,
    closure_Ioo H.ordered.ne]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1.1, hq.1.2, hq.2.2⟩
  · intro hp
    refine ⟨(p.time, p.position 0, p.velocity 0), ⟨⟨hp.1, hp.2.1⟩, mem_univ _, hp.2.2⟩, ?_⟩
    refine KineticPoint.ext rfl ?_ ?_
    · funext i
      fin_cases i
      rfl
    · funext i
      fin_cases i
      rfl

/-- Every closed future slab lies in the regular strip together with its prescribed exit. -/
theorem reconstructionClosedSlab_subset_strip_union_exit (H : Interval)
    {lower a T : ℝ} (ha : lower < a) :
    reconstructionClosedSlab H a T ⊆ reconstructionStrip H lower T ∪ reconstructionExit H
      lower T := by
  intro p hp
  by_cases ht : p.time = T
  · exact Or.inr (Or.inl ⟨ht, hp.2.2⟩)
  · have hpt : p.time < T := lt_of_le_of_ne hp.2.1 ht
    by_cases hv : p.velocity 0 ∈ H.carrier
    · exact Or.inl ⟨ha.trans_le hp.1, hpt, hv⟩
    · have hf : p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi := by
        change ¬(H.lo < p.velocity 0 ∧ p.velocity 0 < H.hi) at hv
        rcases not_and_or.mp hv with hv | hv
        · exact Or.inl (le_antisymm (not_lt.mp hv) hp.2.2.1)
        · exact Or.inr (le_antisymm hp.2.2.2 (not_lt.mp hv))
      exact Or.inr (Or.inr ⟨ha.trans_le hp.1, hpt, hf⟩)

/-- The original interior bound extends to every closed future slab by the prescribed continuity. -/
theorem reconstruction_closed_slab_test_bound
    (H : Interval) {lower a T : ℝ} (ha : lower < a) (hT : a < T)
    (phi : Point → ℝ)
    (hc : ContinuousOn phi (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (M : ℝ) (hM : ∀ p ∈ reconstructionStrip H lower T, |phi p| ≤ M) :
    ∀ p ∈ reconstructionClosedSlab H a T, |phi p| ≤ M := by
  have hcl := closure_reconstructionStrip H a T hT
  intro p hp
  rw [← hcl] at hp
  apply le_on_closure
    (s := reconstructionStrip H a T)
    (fun p hp => hM p ⟨ha.trans hp.1, hp.2⟩)
  · rw [hcl]
    exact (hc.mono (reconstructionClosedSlab_subset_strip_union_exit H ha)).abs
  · exact continuousOn_const
  · exact hp




/-- An actual reconstruction satisfying its proved formula and trace continuity remains
uniformly bounded up to every closed future slab. -/
theorem reconstruction_uniform_bound
    (H : Interval) (E : StripEvolution H) {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (lower T : ℝ) (e : StripPole H (T : WithTop ℝ)) (he : lower < e.1.time)
    (phi u : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H lower T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H lower T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M)
    (hformula : ∀ e : StripPole H (T : WithTop ℝ), lower < e.1.time →
      u e.1 = phi e.1 - ∫ p, -forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e)
    (hc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ B := by
  obtain ⟨g, hg, _⟩ := exists_bounded_reconstruction_source A H lower T phi hphi hb
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  obtain ⟨M, hM⟩ := hb
  have heD : e.1 ∈ reconstructionStrip H lower T :=
    ⟨he, WithTop.coe_lt_coe.mp e.2.1, e.2.2⟩
  have hLT := he.trans (WithTop.coe_lt_coe.mp e.2.1)
  let B := M + C * (T - lower)
  have hB := add_nonneg ((abs_nonneg _).trans (hM e.1 heD).1) (mul_nonneg hC (sub_nonneg.mpr hLT.le))
  refine ⟨B, hB, reconstruction_closed_slab_test_bound H he
    (WithTop.coe_lt_coe.mp e.2.1) u hc B ?_⟩
  intro p hp
  let ep : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2⟩
  have hAE : g =ᵐ[stripGreenOfKernel H E.2 T ep] fun q => -forwardScalarOperator A.a phi q := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T ep,
      reconstruction_green_ae_time_gt H E.2 T ep] with q hq ht
    exact hg q ⟨hp.1.trans ht, hq⟩
  have hh := mul_le_mul_of_nonneg_left (max_le (sub_le_sub_left hp.1.le T) (sub_nonneg.mpr hLT.le)) hC
  have heq : u p = phi p - stripSourcePotential H E.2 T g p := by
    rw [hformula ep hp.1, stripSourcePotential_eq_green H E.2 T g ep, stripPotentialOfKernel]
    rw [integral_congr_ae hAE]
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add (hM p hp).1 ((reconstruction_potential_abs_le_time H E.2 T g C hC hgb p).trans hh)))


/-- The proper spatial weight dominates the exponential of absolute position. -/
theorem reconstructionSpatialWeight_exp_abs_le (x : ℝ) :
    Real.exp |x| ≤ reconstructionSpatialWeight x := by
  unfold reconstructionSpatialWeight
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos (not_le.mp hx).le]
    exact le_add_of_nonneg_left (Real.exp_pos _).le




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
    u e.1 = ∫ p, u p ∂stripExitOfRealization hH hlam hLam A H E hE T e   := by
  have exists_reconstruction_smooth_trace_probe (a : ℝ) (ha : a < T) (hc : ContinuousOn u (reconstructionClosedSlab H a T)) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p ∈ reconstructionClosedSlab H a T, |u p| ≤ M) (R : ℝ) (eps : ℝ) (heps : 0 < eps) :
      ∃ F : exitProbeSubmodule,
      (∀ p, |exitProbePhysical F p| ≤ M + eps) ∧
      ∀ p ∈ reconstructionClosedSlab H a T, |p.position 0| ≤ R →
        |exitProbePhysical F p - u p| ≤ eps := by
    let D := reconstructionClosedSlab H a T
    have hD : IsClosed D := by
      change IsClosed (reconstructionClosedSlab H a T)
      rw [← closure_reconstructionStrip H a T ha]
      exact isClosed_closure
    let f : BoundedContinuousFunction D ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => u p.1) (continuousOn_iff_continuous_domRestrict.mp hc) M
      (fun p => by rw [Real.norm_eq_abs]; exact hb p.1 p.2)
    let j : D → EvolutionVec 1 := fun p => reconstructionPhysicalHomeomorph.symm p.1
    obtain ⟨G, hGb, hG⟩ :=
      BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_isClosedEmbedding f
        (fun p => abs_le.mp (hb p.1 p.2)) (by linarith) (reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp hD.isClosedEmbedding_subtypeVal)
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
  have reconstruction_homogeneous_probe_error (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ M) (R : ℝ) (eps : ℝ) (heps : 0 < eps) :
      ∃ F : exitProbeSubmodule,
      (∀ p, |exitProbePhysical F p| ≤ M + eps) ∧
      (∀ p ∈ reconstructionClosedSlab H e.1.time T, |p.position 0| ≤ R →
        |exitProbePhysical F p - u p| ≤ eps) ∧
      |u e.1 - ∫ p, exitProbePhysical F p ∂stripExitOfRealization hH hlam hLam A H E hE T e| ≤
        eps + (2 * M + eps) * Real.exp (-R) *
          reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T (sectionTwoPoint e.1) := by
    have reconstructionSpatialBarrier_scaled_operator (C : ℝ) (hC : 0 ≤ C) (p : Point) (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        (fun q => C * reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T q) p ≤ 0 := by
      rw [← viscousTransportedOperator_zero,
        viscousTransportedOperator_const_mul C (reconstructionSpatialBarrier_regular _ _ p),
        viscousTransportedOperator_zero]
      have hh := reconstructionSpatialBarrier_operator_le A.a H T p hp
      have hw : 0 ≤ reconstructionSpatialWeight (p.velocity 0) :=
        add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      exact mul_nonpos_of_nonneg_of_nonpos hC (hh.trans (neg_nonpos.mpr hw))
    have reconstructionSpatialBarrier_tail (C : ℝ) (hC : 0 ≤ C) (p : Point) (ht : p.time ≤ T) (hx : R ≤ |p.velocity 0|) :
        C ≤ C * Real.exp (-R) * reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T p := by
      have hV : 0 ≤ max |H.lo| |H.hi| + 1 := by positivity
      have ht' :=
        Real.one_le_exp_iff.mpr (mul_nonneg hV (sub_nonneg.mpr ht))
      have hx' := (Real.exp_le_exp.mpr hx).trans
        (reconstructionSpatialWeight_exp_abs_le (p.velocity 0))
      have hq : Real.exp R ≤ reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T p := by
        unfold reconstructionSpatialBarrier
        exact (by simpa using
          mul_le_mul ht' hx' (Real.exp_pos R).le (le_trans zero_le_one ht'))
      have he : Real.exp (-R) * Real.exp R = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      simpa [mul_assoc, he] using (mul_le_mul_of_nonneg_left hq (mul_nonneg hC (Real.exp_pos (-R)).le))
    have reconstruction_homogeneous_gap_le_barrier (u : Point → ℝ) (v : Point → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
        (KineticPoint.equivProd 1 '' reconstructionStrip H lower T)) (hv : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ (KineticPoint.equivProd 1).symm)
        (KineticPoint.equivProd 1 '' reconstructionStrip H lower T)) (huop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a u p = 0) (hvop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a v p = 0) (huc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T)) (hvc : ContinuousOn v (reconstructionStrip H lower T ∪ reconstructionExit H lower T)) (Mu : ℝ) (Mv : ℝ) (hub : ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ Mu) (hvb : ∀ p ∈ reconstructionClosedSlab H e.1.time T, |v p| ≤ Mv) (q : Point → ℝ) (hqc : Continuous q) (hqr : ∀ p, IsSliceRegularAt q p) (hqn : ∀ p, 0 ≤ q p) (hqo : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T,
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) q p ≤ 0) (hbd : ∀ p ∈ stripClosedExit H T, e.1.time ≤ p.time →
        u p - v p ≤ eps + q (sectionTwoPoint p)) :
        u e.1 - v e.1 ≤ eps + q (sectionTwoPoint e.1) := by
      have reconstruction_physical_slice_regular (u : Point → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
          (KineticPoint.equivProd 1 '' reconstructionStrip H lower T)) (p : Point) (hp : sectionTwoPoint p ∈ reconstructionStrip H lower T) :
          IsSliceRegularAt (u ∘ sectionTwoPoint) p := by
        have reconstruction_physical_smooth_to_packed :
            ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ reconstructionPhysicalHomeomorph)
            (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T) := by
          let c : EvolutionVec 1 → ℝ × PDE.Vec 1 × PDE.Vec 1 := fun x =>
            ((evolutionProdCLE 1 x).1, (evolutionProdCLE 1 x).2.2, (evolutionProdCLE 1 x).2.1)
          have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
            (evolutionProdCLE 1).contDiff.fst.prodMk
              ((evolutionProdCLE 1).contDiff.snd.snd.prodMk (evolutionProdCLE 1).contDiff.snd.fst)
          have hmaps : MapsTo c (reconstructionPhysicalHomeomorph ⁻¹' reconstructionStrip H lower T)
              (KineticPoint.equivProd 1 '' reconstructionStrip H lower T) := by
            intro x hx
            exact ⟨reconstructionPhysicalHomeomorph x, hx, rfl⟩
          have hh := hu.comp hc.contDiffOn hmaps
          exact hh
        have hD := (isOpen_reconstructionStrip H lower T).preimage
          (continuous_sectionTwoPoint 1)
        exact reconstruction_slice_regular_of_contDiffOn hD
          (reconstruction_physical_smooth_to_packed) p hp
      let a := e.1.time
      have hact : ∀ p ∈ movingActiveSlab (intervalDomain H) (fun _ => 0) a T,
          sectionTwoPoint p ∈ reconstructionStrip H lower T := by
        intro p hp
        refine ⟨he.trans_le hp.1, hp.2.1, ?_⟩
        simpa [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier, sectionTwoPoint] using hp.2.2
      have hslab : ∀ p ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T,
          sectionTwoPoint p ∈ reconstructionClosedSlab H a T := by
        intro p hp
        change a ≤ p.time ∧ p.time ≤ T ∧ p.position 0 ∈ Icc H.lo H.hi
        exact ⟨hp.1, hp.2.1, intervalDomain_closure_bounds H (by
          simpa [mem_closure_movingDomain_iff] using hp.2.2)⟩
      have hur (p : Point) (hp : p ∈ movingActiveSlab (intervalDomain H) (fun _ => 0) a T) :=
        reconstruction_physical_slice_regular u hu p (hact p hp)
      have hvr (p : Point) (hp : p ∈ movingActiveSlab (intervalDomain H) (fun _ => 0) a T) :=
        reconstruction_physical_slice_regular v hv p (hact p hp)
      have huc' := huc.comp (continuous_sectionTwoPoint 1).continuousOn
        (reconstruction_closedSlab_mapsTo H he)
      have hvc' := hvc.comp (continuous_sectionTwoPoint 1).continuousOn
        (reconstruction_closedSlab_mapsTo H he)
      have hmax := growth_comparison
        (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)) continuous_const
        hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
        (le_refl 0) zero_le_one
        (u := fun p => (u (sectionTwoPoint p) - v (sectionTwoPoint p) - eps) - q p)
        ⟨Mu + Mv + |eps|, fun p hp => by
          have h1 := (le_abs_self _).trans (hub _ (hslab p hp))
          have h2 := (neg_le_abs _).trans (hvb _ (hslab p hp))
          have h3 := neg_le_abs eps
          have h4 := hqn p
          linarith⟩
        (((huc'.sub hvc').sub continuousOn_const).sub hqc.continuousOn)
        (fun p hp => ((hur p hp).sub (hvr p hp) |>.sub (IsSliceRegularAt.const eps p)).sub (hqr p))
        (fun p hp => by
          change 0 ≤ viscousTransportedOperator (evolutionCoefficient A.a) (identityDrift 1) 0
            (fun y => ((u ∘ sectionTwoPoint) y - (v ∘ sectionTwoPoint) y -
              (fun _ => eps) y) - q y) p
          rw [viscousTransportedOperator_sub
            ((hur p hp).sub (hvr p hp) |>.sub (IsSliceRegularAt.const eps p)) (hqr p),
            viscousTransportedOperator_sub ((hur p hp).sub (hvr p hp)) (IsSliceRegularAt.const eps p),
            viscousTransportedOperator_sub (hur p hp) (hvr p hp),
            viscousTransportedOperator_zero, viscousTransportedOperator_zero,
            reconstruction_scalar_operator_swap, reconstruction_scalar_operator_swap,
            huop _ (hact p hp), hvop _ (hact p hp), viscousTransportedOperator_const,
            viscousTransportedOperator_zero]
          have hh := hqo p ⟨hp.2.1, hp.2.2⟩
          linarith)
        (fun p hp hpt => by
          have hvel := intervalDomain_closure_bounds H (by
            simpa [mem_closure_movingDomain_iff] using hp.2.2)
          have hh := hbd (sectionTwoPoint p) (Or.inl ⟨hpt, hvel⟩) hp.1
          change (u (sectionTwoPoint p) - v (sectionTwoPoint p) - eps) - q p ≤ 0
          rw [sectionTwoPoint_involutive] at hh
          linarith)
        (fun p hp hpf => by
          have hvel := reconstruction_interval_frontier_eq H (by
            simpa only [movingDomain, PDE.translateSet_zero] using hpf)
          have hh := hbd (sectionTwoPoint p) (Or.inr ⟨hp.2.1, hvel⟩) hp.1
          rw [sectionTwoPoint_involutive] at hh
          linarith)
      have hp : sectionTwoPoint e.1 ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T :=
        ⟨le_rfl, (WithTop.coe_lt_coe.mp e.2.1).le, subset_closure (stripPoleState H T e).2.1⟩
      have hh := hmax _ hp
      rw [sectionTwoPoint_involutive] at hh
      linarith
    obtain ⟨F, hFb, hclose⟩ := exists_reconstruction_smooth_trace_probe e.1.time (WithTop.coe_lt_coe.mp e.2.1)
      (hc.mono (reconstructionClosedSlab_subset_strip_union_exit H he)) M hM hb R eps heps
    have hFr := exitProbePhysical_isKineticC112On F (reconstructionStrip H lower T)
      (isOpen_reconstructionStrip H lower T)
    obtain ⟨C, hC⟩ := exitProbePhysical_bounded_source A F
    have hFs : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H lower T,
        |exitProbePhysical F p| ≤ M ∧ |forwardScalarOperator A.a (exitProbePhysical F) p| ≤ M :=
      ⟨C, fun p _ => hC p⟩
    obtain ⟨v, hvform, hvs, hvop, hvc, hvexit⟩ := strip_bounded_source_reconstruction
      hH hlam hLam A H E hE lower T (exitProbePhysical F) hFr ((exitProbePhysical_continuous_compact F).1).continuousOn hFs
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
        transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) q p ≤ 0 :=
      reconstructionSpatialBarrier_scaled_operator k hk p hp
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
        have htail := reconstructionSpatialBarrier_tail (2 * M + eps)
          (by linarith) (sectionTwoPoint p) hslab.2.1 (not_le.mp hx).le
        change 2 * M + eps ≤ q (sectionTwoPoint p) at htail
        exact hh.trans ((by linarith : M + (M + eps) ≤ 2 * M + eps).trans
          (htail.trans (le_add_of_nonneg_left heps.le)))
    have hlower := reconstruction_homogeneous_gap_le_barrier
      v u hvs hu hvop hop hvc hc Mv M hvb hb q hqc hqr hqn hqo
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
    exact abs_le.mpr ⟨by linarith, (reconstruction_homogeneous_gap_le_barrier u v hu hvs hop hvop hc hvc M Mv hb hvb q hqc hqr hqn hqo (fun p hp ht => (le_abs_self _).trans (hbd p hp ht)))⟩
  obtain ⟨M, hM, hb⟩ := hb
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hr1 (n : ℕ) : r n ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose F hFb hclose herr using fun n : ℕ => reconstruction_homogeneous_probe_error M hM hb ((n : ℝ) + 1) (r n) (hr n)
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
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop))
  have hb0 : Tendsto b atTop (𝓝 0) := by
    simpa [b] using
      hr0.add (((tendsto_const_nhds.add hr0).mul hexp).mul_const Q)
  have hpole : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop (𝓝 (u e.1)) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hb0.eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq, abs_sub_comm]
    exact (herr n).trans_lt hn
  exact tendsto_nhds_unique hpole hlim



/-- The canonical autonomous families satisfy the full C112 identity at an interior pole. -/
theorem strip_identity_C112
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sMinus T : ℝ) (hT : sMinus < T)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hc : ContinuousOn phi (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExit hH hLE hlam hLam A H T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H T e  := by
  have strip_identity_C112_of_realization (E : StripEvolution H) (hE : IsStripEvolution A H E) (_hT : sMinus < T) (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
      phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
    obtain ⟨u, hform, hu, hop, huc, hexit⟩ := strip_bounded_source_reconstruction
      hH hlam hLam A H E hE sMinus T phi hphi hc hb
    have hub := reconstruction_uniform_bound H E A sMinus T e he phi u hphi hb hform huc
    have hrep := reconstruction_homogeneous_exit_representation hH hlam hLam A H E hE
      sMinus T e he u hu hop huc hub
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
  exact strip_identity_C112_of_realization _
    (stripEvolution_spec hH hLE hlam hLam A H) hT hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

