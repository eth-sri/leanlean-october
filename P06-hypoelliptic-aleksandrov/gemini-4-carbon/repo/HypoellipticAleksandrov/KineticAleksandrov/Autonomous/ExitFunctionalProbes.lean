module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstruction
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalProbe
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Topology.TietzeExtension

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov SectionTwo TheoremA Evolution MeasureTheory Filter Parabolic
open scoped Topology CompactlySupported

/-- The closed exit carrier contains the whole past lateral faces and the terminal face.
The actual measure's future-time support is a separate theorem. -/
def stripClosedExit (H : Interval) (T : ℝ) : Set Point :=
  {p | p.time = T ∧ p.velocity 0 ∈ Icc H.lo H.hi} ∪
    {p | p.time ≤ T ∧ (p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi)}

/-- The full exit carrier is closed in physical kinetic spacetime. -/
theorem isClosed_stripClosedExit (H : Interval) (T : ℝ) : IsClosed (stripClosedExit H T) :=
  ((isClosed_eq continuous_time continuous_const).inter
    (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_velocity))).union
    ((isClosed_le continuous_time continuous_const).inter
      ((isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const).union
        (isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const)))

/-- Swapping a native closed slab gives interior or prescribed exit points on any lower strip. -/
theorem reconstruction_closedSlab_mapsTo (H : Interval) {sMinus a T : ℝ}
    (ha : sMinus < a) :
    MapsTo sectionTwoPoint (movingClosedSlab (intervalDomain H) (fun _ => 0) a T)
      (reconstructionStrip H sMinus T ∪ reconstructionExit H sMinus T) := by
  intro p hp
  have hv := intervalDomain_closure_bounds H (by
    simpa [mem_closure_movingDomain_iff] using hp.2.2)
  by_cases ht : p.time = T
  · exact Or.inr (Or.inl ⟨ht, hv⟩)
  · have htl : sMinus < p.time := ha.trans_le hp.1
    have htu := lt_of_le_of_ne hp.2.1 ht
    by_cases hl : p.position 0 = H.lo
    · exact Or.inr (Or.inr ⟨htl, htu, Or.inl hl⟩)
    · by_cases hh : p.position 0 = H.hi
      · exact Or.inr (Or.inr ⟨htl, htu, Or.inr hh⟩)
      · exact Or.inl ⟨htl, htu, lt_of_le_of_ne hv.1 (Ne.symm hl), lt_of_le_of_ne hv.2 hh⟩

/-- The native interval frontier consists of exactly the two scalar endpoints. -/
theorem reconstruction_interval_frontier_eq (H : Interval) {v : PDE.Vec 1}
    (hv : v ∈ frontier (intervalDomain H)) : v 0 = H.lo ∨ v 0 = H.hi := by
  have hb := intervalDomain_closure_bounds H (frontier_subset_closure hv)
  change v ∈ closure (intervalDomain H) ∧ v ∉ interior (intervalDomain H) at hv
  have hn := hv.2
  rw [(isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)).interior_eq] at hn
  by_cases hl : v 0 = H.lo
  · exact Or.inl hl
  · right
    by_contra hh
    apply hn
    apply PDE.mem_oneDimensionalAxisBox_iff.mpr
    exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hl), lt_of_le_of_ne hb.2 hh⟩


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
  let U := reconstructionPhysicalPoint ⁻¹' reconstructionStrip H sMinus T
  have hD := (isOpen_reconstructionStrip H sMinus T).preimage
    (continuous_sectionTwoPoint 1)
  have hsm := hf.congr (fun x hx => heq hx)
  have hreg (p : Point) (hp : p ∈ D) : IsSliceRegularAt (u ∘ sectionTwoPoint) p :=
    reconstruction_slice_regular_of_contDiffOn hD hsm p hp
  have huop (p : Point) (hp : p ∈ D) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        (u ∘ sectionTwoPoint) p = 0 := by
    let x := (evolutionHomeomorph 1).symm p
    have hx : x ∈ U := by
      change sectionTwoPoint (evolutionHomeomorph 1 x) ∈ reconstructionStrip H sMinus T
      rwa [Homeomorph.apply_symm_apply]
    have hh :=
      Filter.mem_of_superset (((isOpen_reconstructionStrip H sMinus T).preimage continuous_reconstructionPhysicalPoint).mem_nhds hx) (fun y hy => heq hy)
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
    simpa [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier, sectionTwoPoint]
        using hp.2.2
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  have hcslab :=
    (reconstruction_candidate_continuousOn_exit hH hlam hLam A H E hE sMinus T phi hphi hc.continuousOn g hg).comp (continuous_sectionTwoPoint 1).continuousOn (reconstruction_closedSlab_mapsTo H he)
  have hmax := growth_comparison
    (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)) continuous_const
    hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
    (le_refl 0) zero_le_one

    ⟨M + C * (T - a) + |c|, fun p hp => by
      have hv := reconstruction_potential_abs_le_time H E.2 T g C hC hgb (sectionTwoPoint p)
      have ht := max_le
        (sub_le_sub_left hp.1 T) (sub_nonneg.mpr (WithTop.coe_lt_coe.mp e.2.1).le)
      have hb' := mul_le_mul_of_nonneg_left ht hC
      have hφ := (le_abs_self (phi (sectionTwoPoint p))).trans (hM _)
      change phi (sectionTwoPoint p) - stripSourcePotential H E.2 T g (sectionTwoPoint p) - c ≤ _
      change |stripSourcePotential H E.2 T g (sectionTwoPoint p)| ≤ C * max (T - p.time) 0 at hv
      linarith only [hv, hb', hφ, (neg_le_abs (stripSourcePotential H E.2 T g (sectionTwoPoint p))), (neg_le_abs c)]⟩
    (hcslab.sub continuousOn_const)
    (fun p hp => (hreg p (hactive hp)).sub (IsSliceRegularAt.const c p))
    (fun p hp => by
      change 0 ≤ viscousTransportedOperator (evolutionCoefficient A.a) (identityDrift 1) 0
        (fun q => (u ∘ sectionTwoPoint) q - (fun _ => c) q) p
      rw [viscousTransportedOperator_sub (hreg p (hactive hp)) (IsSliceRegularAt.const c p),
        viscousTransportedOperator_zero, huop p (hactive hp), viscousTransportedOperator_const]
      norm_num)
    (fun p hp hpt => by
      have hv := intervalDomain_closure_bounds H (by
        simpa [mem_closure_movingDomain_iff] using hp.2.2)
      have hn : sectionTwoPoint p ∉ stripPast H T := fun hh =>
        (by simpa only [sectionTwoPoint, hpt] using hh.1 : T < T).false
      have hz := reconstruction_potential_zero_outside H E.2 T g (sectionTwoPoint p) hn
      change phi (sectionTwoPoint p) - stripSourcePotential H E.2 T g (sectionTwoPoint p) - c ≤ 0
      rw [hz, sub_zero]
      exact sub_nonpos.mpr (hbd _ (Or.inl ⟨hpt, hv⟩)))
    (fun p hp hpf => by
      have hf : p.position ∈ frontier (intervalDomain H) := by
        simpa only [movingDomain, PDE.translateSet_zero] using hpf
      have hv := reconstruction_interval_frontier_eq H hf
      have hn : sectionTwoPoint p ∉ stripPast H T := by
        intro h
        rcases hv with hv | hv
        · exact (lt_irrefl H.lo) (hv ▸ h.2.1)
        · exact (lt_irrefl H.hi) (hv ▸ h.2.2)
      change phi (sectionTwoPoint p) - stripSourcePotential H E.2 T g (sectionTwoPoint p) - c ≤ 0
      rw [(reconstruction_potential_zero_outside H E.2 T g (sectionTwoPoint p) hn), sub_zero]
      exact sub_nonpos.mpr (hbd _ (Or.inr ⟨hp.2.1, hv⟩)))
  have hp : sectionTwoPoint e.1 ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T :=
    ⟨le_rfl, (WithTop.coe_lt_coe.mp e.2.1).le, subset_closure (stripPoleState H T e).2.1⟩
  have hres := sub_nonpos.mp (hmax _ hp)
  have hgAE : g =ᵐ[stripGreenOfKernel H E.2 T e] fun p => -forwardScalarOperator A.a phi p := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
      reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
    exact hg p ⟨he.trans ht, hp⟩
  change phi e.1 - stripSourcePotential H E.2 T g e.1 ≤ c at hres
  rw [stripSourcePotential_eq_green H E.2 T g e, stripPotentialOfKernel,
    integral_congr_ae hgAE] at hres
  exact hres


/-- The physical coordinate homeomorphism associated to the native Euclidean packing. -/
def reconstructionPhysicalHomeomorph : EvolutionVec 1 ≃ₜ Point :=
  (evolutionHomeomorph 1).trans (sectionTwoHomeomorph 1)

/-- The inverse map packs physical velocity before physical position. -/
@[simp] theorem reconstructionPhysicalHomeomorph_symm_apply (p : Point) :
    reconstructionPhysicalHomeomorph.symm p = packPoint p.time p.velocity p.position := rfl

/-- Ambient smooth compact scalar functions form the exit probe vector space. -/
def exitProbeSubmodule : Submodule ℝ (EvolutionVec 1 → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun _c _f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

/-- The physical test supplied by an ambient exit probe. -/
def exitProbePhysical (f : exitProbeSubmodule) : Point → ℝ :=
  f.1 ∘ reconstructionPhysicalHomeomorph.symm

/-- A physical probe is globally continuous and compactly supported. -/
theorem exitProbePhysical_continuous_compact (f : exitProbeSubmodule) :
    Continuous (exitProbePhysical f) ∧ HasCompactSupport (exitProbePhysical f) :=
  ⟨f.2.1.continuous.comp reconstructionPhysicalHomeomorph.symm.continuous,
    f.2.2.comp_homeomorph reconstructionPhysicalHomeomorph.symm⟩


/-- Smooth ambient probes supply genuine global physical C112 tests. -/
theorem exitProbePhysical_isKineticC112On (f : exitProbeSubmodule) (D : Set Point)
    (hD : IsOpen D) : IsKineticC112On (exitProbePhysical f) D  := by
  have probe_native_smooth :
      ContDiff ℝ (⊤ : ℕ∞) (exitProbePhysical f ∘ evolutionHomeomorph 1) := by
    have heq : exitProbePhysical f ∘ evolutionHomeomorph 1 =
        (f.1 ∘ (evolutionProdCLE 1).symm) ∘
          (fun q => (q.1, q.2.2, q.2.1)) ∘ evolutionProdCLE 1 := by
      funext x
      simp [exitProbePhysical, reconstructionPhysicalHomeomorph_symm_apply, time_evolutionHomeomorph, velocity_evolutionHomeomorph, position_evolutionHomeomorph, evolutionProdCLE_apply, evolutionProdCLE_symm_apply]
    rw [heq]
    exact f.2.1.comp ((evolutionProdCLE 1).symm.contDiff.comp ((contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)).comp (evolutionProdCLE 1).contDiff))
  exact isKineticC112On_of_contDiffOn hD (probe_native_smooth).contDiffOn



/-- The actual packed kinetic operator of a smooth compact probe is smooth and compact. -/
theorem exitProbe_operator_smooth_compact {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (f : exitProbeSubmodule) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1) ∧
    HasCompactSupport (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1)   := by
  have probe_operator_formula :
      transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1 =
      fun x => fderiv ℝ f.1 x basisT +
        A.a (transportedCoord 1 x 0) (diffusedCoord 1 x 0) *
          fderiv ℝ (fun y => fderiv ℝ f.1 y (basisV 0)) x (basisV 0) +
        diffusedCoord 1 x 0 * fderiv ℝ f.1 x (basisZ 0) := by
    funext x
    simp [transportedOperator, Fin.sum_univ_one, evolutionCoefficient, identityDrift]
  have probe_derivative_smooth {f : EvolutionVec 1 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : EvolutionVec 1) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x v) :=
    (hf.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hh := probe_derivative_smooth (probe_derivative_smooth f.2.1 (basisV 0)) (basisV 0)
  have hvc : HasCompactSupport (fun x => fderiv ℝ f.1 x (basisV 0)) :=
    f.2.2.fderiv_apply ℝ _
  rw [probe_operator_formula]
  constructor
  · simpa using! ((probe_derivative_smooth f.2.1 basisT).add ((A.smooth.comp (((contDiff_apply ℝ ℝ 0).comp (transportedCoord 1).contDiff).prodMk ((contDiff_apply ℝ ℝ 0).comp (diffusedCoord 1).contDiff))).mul hh)).add
      (((contDiff_apply ℝ ℝ 0).comp (diffusedCoord 1).contDiff).mul (probe_derivative_smooth f.2.1 (basisZ 0)))
  · exact ((f.2.2.fderiv_apply ℝ basisT).add (hvc.fderiv_apply ℝ (basisV 0)).mul_left).add
      (f.2.2.fderiv_apply ℝ (basisZ 0)).mul_left

/-- The scalar physical operator is exactly the packed probe operator under the fixed map. -/
theorem exitProbePhysical_operator {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) (p : Point) :
    forwardScalarOperator A.a (exitProbePhysical f) p =
      transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1
        (reconstructionPhysicalHomeomorph.symm p) := by
  let x := reconstructionPhysicalHomeomorph.symm p
  have heq : (exitProbePhysical f ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1 = f.1 := by
    funext y
    exact congrArg f.1 (reconstructionPhysicalHomeomorph.symm_apply_apply y)
  have hs : ContDiffAt ℝ 2 ((exitProbePhysical f ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x := by
    rw [heq]
    exact (f.2.1.of_le (by simp)).contDiffAt
  have hop := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hs
  rw [heq, reconstruction_scalar_operator_swap] at hop
  have hx : sectionTwoPoint (evolutionHomeomorph 1 x) = p :=
    reconstructionPhysicalHomeomorph.apply_symm_apply p
  rw [hx] at hop
  exact hop.symm

/-- A compact probe and its actual kinetic operator satisfy the bounded source hypotheses. -/
theorem exitProbePhysical_bounded_source {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) :
    ∃ M : ℝ, ∀ p, |exitProbePhysical f p| ≤ M ∧
      |forwardScalarOperator A.a (exitProbePhysical f) p| ≤ M := by
  obtain ⟨B, hB⟩ := f.2.2.exists_bound_of_continuous f.2.1.continuous
  obtain ⟨C, hC⟩ := (exitProbe_operator_smooth_compact A f).2.exists_bound_of_continuous
    (exitProbe_operator_smooth_compact A f).1.continuous
  refine ⟨max B C, fun p => ⟨(hB _).trans (le_max_left _ _), ?_⟩⟩
  rw [exitProbePhysical_operator A f p]
  exact (hC _).trans (le_max_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

