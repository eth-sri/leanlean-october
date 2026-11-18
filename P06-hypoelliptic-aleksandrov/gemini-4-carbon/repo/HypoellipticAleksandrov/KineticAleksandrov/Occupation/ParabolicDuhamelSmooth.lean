module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSliceLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
section

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)


/-- The slice integrand is continuous on the closed cylinder, and equals the classical
solution there, which is smooth in the open cylinder and has the stated trace data. -/
theorem slice_regularity {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (r : ℝ) :
    ∃ V : TimeVelocity d → ℝ,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ sliceClosedCylinder Ω γ r, |V p| ≤ C) ∧
      ContinuousOn V (sliceClosedCylinder Ω γ r) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) V (sliceOpenCylinder Ω γ r) ∧
      (∀ p ∈ sliceOpenCylinder Ω γ r,
        scalarParabolicOperator B (fun _ _ => 0) V p = 0) ∧
      (∀ v ∈ closure (movingDomain Ω γ r), V (r, v) = g (r, v)) ∧
      ∀ p ∈ sliceClosedCylinder Ω γ r,
        parabolicDuhamelIntegrand K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g p r
          = V p  := by
  have integrand_eq_slice_solution (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (g : TimeVelocity d → ℝ) (r : ℝ) (V : TimeVelocity d → ℝ) (hlat : ∀ p ∈ ParabolicProbe.scalarLateralFrontier Ω γ r, V p = 0) (hV : ∀ (s : ℝ) (hsr : s ≤ r) (y : EvolutionPosition Ω γ s),
      V (s, y.1) = parabolicSourceIntegral K hΩ g s r hsr y) (p : TimeVelocity d) (hp : p ∈ sliceClosedCylinder Ω γ r) :
      parabolicDuhamelIntegrand K hΩ g p r = V p := by
    by_cases hmem : p.2 ∈ movingDomain Ω γ p.1
    · rw [parabolicDuhamelIntegrand_of_valid K hΩ g p r ⟨hp.1, hmem⟩]
      exact (hV p.1 hp.1 ⟨p.2, hmem⟩).symm
    · rw [parabolicDuhamelIntegrand_of_not_valid K hΩ g p r (fun h => hmem h.2)]
      have hfr : p.2 ∈ frontier (movingDomain Ω γ p.1) := by
        rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩa p.1).frontier_eq]
        exact ⟨hp.2, hmem⟩
      exact (hlat p ⟨hp.1, hfr⟩).symm
  obtain ⟨V, ⟨hbd, hcont, hsm, heq, hterm, hlat⟩, hVs⟩ :=
    exists_slice_solution K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) hP g hgs hgc T
      hgU r
  refine ⟨V, hbd, hcont, hsm, heq, fun v hv => ?_,
    integrand_eq_slice_solution hΩa _ g r V hlat hVs⟩
  exact hterm (r, v) ⟨rfl, hv⟩

/-- A compactly supported source vanishes at all times outside a bounded interval. -/
theorem exists_time_range (g : TimeVelocity d → ℝ) (hgc : HasCompactSupport g) :
    ∃ a b : ℝ, ∀ r, r ∉ Icc a b → ∀ v, g (r, v) = 0 := by
  have hK := hgc.image continuous_fst
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨a, ha⟩ := hK.bddBelow
  refine ⟨a, b, fun r hr v => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hr ⟨ha ⟨_, hmem, rfl⟩, hb ⟨_, hmem, rfl⟩⟩

/-- **Continuity of the Duhamel potential** on the closed region
`{s ≤ T, v ∈ closure Ω_s}`, by dominated convergence in the source time. -/
theorem continuousWithinAt_duhamelPotential {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T)
    (p₀ : TimeVelocity d) (hp₀ : p₀ ∈ duhamelClosedFiber Ω γ T) :
    ContinuousWithinAt
      (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
      (duhamelClosedFiber Ω γ T) p₀ := by
  have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  obtain ⟨a, b, hab⟩ := exists_time_range g hgc
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  have hgm := hgs.continuous.measurable
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgm.comp (measurable_const.prodMk measurable_id)
  let F : TimeVelocity d → ℝ → ℝ := fun p r =>
    (Ioc p.1 T).indicator (parabolicDuhamelIntegrand K hΩ g p) r
  have hW : parabolicDuhamelPotential K hΩ T g = fun p => ∫ r, F p r :=
    funext fun p => (integral_indicator measurableSet_Ioc).symm
  have hFm : ∀ p, Measurable (F p) := fun p =>
    ((measurable_parabolicDuhamelIntegrand K hΩ hγ g hgm).comp (measurable_const.prodMk measurable_id)).indicator measurableSet_Ioc
  have hF0 : ∀ p r, r ∉ Icc a b → F p r = 0 := by
    intro p r hr
    by_cases h : r ∈ Ioc p.1 T
    · exact (indicator_of_mem h _).trans
        (parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg p r (hab r hr))
    · exact indicator_of_notMem h _
  have hbd : ∀ p r, ‖F p r‖ ≤ (Icc a b).indicator (fun _ => C) r := by
    intro p r
    by_cases hr : r ∈ Icc a b
    · rw [indicator_of_mem hr, Real.norm_eq_abs]
      by_cases h : r ∈ Ioc p.1 T
      · change |(Ioc p.1 T).indicator (parabolicDuhamelIntegrand K hΩ g p) r| ≤ C
        rw [indicator_of_mem h,
          abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
        exact parabolicDuhamelIntegrand_le K hΩ g hg hgn C hgb p r
      · change |(Ioc p.1 T).indicator (parabolicDuhamelIntegrand K hΩ g p) r| ≤ C
        rw [indicator_of_notMem h, abs_zero]
        exact (hgn (0, 0)).trans (hgb _)
    · rw [indicator_of_notMem hr, hF0 p r hr, norm_zero]
  have hint : Integrable ((Icc a b).indicator (fun _ => C)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ({p₀.1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton _)
  have hcont : ∀ᵐ r ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun p => F p r) (duhamelClosedFiber Ω γ T) p₀ := by
    filter_upwards [hne] with r hr
    rcases lt_trichotomy r p₀.1 with h | h | h
    · have hopen : {p : TimeVelocity d | r < p.1} ∈ 𝓝 p₀ :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds h
      have hev : (fun p => F p r) =ᶠ[𝓝[duhamelClosedFiber Ω γ T] p₀] fun _ => 0 := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with p hp
        exact indicator_of_notMem (fun hh => absurd hh.1 (not_lt.2 hp.le)) _
      have h0 : F p₀ r = 0 := indicator_of_notMem (fun hh => absurd hh.1 (not_lt.2 h.le)) _
      exact continuousWithinAt_const.congr_of_eventuallyEq hev h0
    · exact absurd h (by simpa using hr)
    · by_cases hrT : r ≤ T
      · obtain ⟨V, -, hVc, -, -, -, hVeq⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
        have hp₀r : p₀ ∈ sliceClosedCylinder Ω γ r := ⟨h.le, hp₀.2⟩
        have hnh : sliceClosedCylinder Ω γ r ∈ 𝓝[duhamelClosedFiber Ω γ T] p₀ :=
          mem_nhdsWithin.2 ⟨{p | p.1 < r}, isOpen_lt continuous_fst continuous_const, h,
            fun p hp => ⟨hp.1.le, hp.2.2⟩⟩
        have hc2 := ((hVc.congr (fun p hp => hVeq p hp)) p₀ hp₀r).mono_of_mem_nhdsWithin hnh
        have hev : (fun p => F p r) =ᶠ[𝓝[duhamelClosedFiber Ω γ T] p₀]
            fun p => parabolicDuhamelIntegrand K hΩ g p r := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds h)] with p hp
          exact indicator_of_mem (show r ∈ Ioc p.1 T from ⟨hp, hrT⟩) _
        exact hc2.congr_of_eventuallyEq hev (indicator_of_mem (show r ∈ Ioc p₀.1 T from ⟨h, hrT⟩) _)
      · have hz : ∀ p, F p r = 0 := fun p =>
          indicator_of_notMem (fun hh => hrT hh.2) _
        simp only [hz]
        exact continuousWithinAt_const
  rw [hW]
  exact continuousWithinAt_of_dominated
    (Eventually.of_forall fun p => (hFm p).aestronglyMeasurable)
    (Eventually.of_forall fun p => Eventually.of_forall fun r => hbd p r) hint hcont

/-- Continuity of the Duhamel potential on the closed region. -/
theorem continuousOn_duhamelPotential {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) :
    ContinuousOn
      (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
      (duhamelClosedFiber Ω γ T) :=
  fun p₀ hp₀ => continuousWithinAt_duhamelPotential K hΩa hγ hP g hgn hgs hgc T hgU p₀ hp₀

end

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology MatrixOrder

variable {n : ℕ}

/-- Hörmander regularity for a distributional solution of `Lop u = g` with smooth `g`
(packed coordinates), with Hörmander's theorem as the explicit hypothesis `hH`. -/
theorem exists_smooth_representative_transported_source
    (hH : HormanderHypoellipticityStatement) {lam Lam m : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hm : 0 < m) (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    {U : Set (EvolutionVec n)} (hU : IsOpen U) {u g : EvolutionVec n → ℝ}
    (hu : IsWeakTransportedSolution B b U u g) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ∃ f : EvolutionVec n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_transportedFields hlam hB_smooth hB_ell hb_smooth hm hb_coercive U
  exact hH hU _ _ _ _ hX hspan contDiffOn_const (hasWeakHormanderEquation_transportedFields hlam hB_smooth hB_ell hb_smooth hu hg)

section Potential

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- The parabolic operator of a smooth function with continuous coefficient is continuous. -/
theorem continuousOn_scalarParabolicOperator_of_contDiffOn {B' : CoefficientField d}
    (hBc : ∀ i j, Continuous (fun p : TimeVelocity d => B' p.1 p.2 i j))
    {D : Set (TimeVelocity d)} (hD : IsOpen D) {w : TimeVelocity d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D) :
    ContinuousOn (scalarParabolicOperator B' (fun _ _ => 0) w) D := by
  have hu :=
    isScalarC12On_of_isOpen_contDiffOn_two hD (hw.of_le (by norm_num))
  have hfun : scalarParabolicOperator B' (fun _ _ => 0) w = fun p =>
      scalarTimeDerivative w p + ∑ i, ∑ j, B' p.1 p.2 i j * scalarSpatialHessian w p i j := by
    funext p
    simp [scalarParabolicOperator_apply, matrixContraction, PDE.vecDot]
  rw [hfun]
  refine hu.continuousOn_scalarTimeDerivative.add (continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => (hBc i j).continuousOn.mul ?_)
  exact (show Continuous (fun A : PDE.Mat d => A i j) from
    (continuous_apply j).comp (continuous_apply i)).comp_continuousOn
      hu.continuousOn_scalarSpatialHessian

/-- The lift `(σ, v) ↦ (σ, v, 0)` is smooth. -/
theorem contDiff_zeroLift : ContDiff ℝ (⊤ : ℕ∞) (fun p : TimeVelocity d =>
    packPoint p.1 p.2 (0 : PDE.Vec d) : TimeVelocity d → EvolutionVec d) := by
  have : (fun p : TimeVelocity d => packPoint p.1 p.2 0) =
      (evolutionProdCLE d).symm ∘ (fun p : TimeVelocity d => (p.1, (p.2, 0))) := by
    funext p; rfl
  rw [this]
  exact (evolutionProdCLE d).symm.contDiff.comp
    (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

/-- **Smoothness and the source equation.**  Under Hörmander's theorem (`hH`), the Duhamel
potential is smooth in `U₀` and satisfies `∂_σ W + B : D_v² W = -g` there. -/
theorem duhamel_smooth_equation (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ) {lam Lam : ℝ}
    {B : CoefficientField d} (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) :
    ContDiffOn ℝ (⊤ : ℕ∞)
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
        (duhamelFiber Ω γ T) ∧
      ∀ p ∈ duhamelFiber Ω γ T,
        scalarParabolicOperator B (fun _ _ => 0)
          (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
          p = -g p  := by
  have duhamel_weak_identity {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ) (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K) (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B)) {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b) (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' duhamelFiber Ω γ T) :
      (∫ x, parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g
        (evolutionToTimeVelocity d x) *
        transportedAdjoint (zIndependentCoefficient B) b ψ x) =
      -∫ x, g (evolutionToTimeVelocity d x) * ψ x := by
    have slice_terminal_limit {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ) (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
        (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K) (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (C : ℝ) (hub : ∀ p r, |parabolicDuhamelIntegrand K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g p r| ≤ C) {ψ : EvolutionVec d → ℝ} (hψ : Continuous ψ) (hψs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' duhamelFiber Ω γ T) (r : ℝ) (w : PDE.Vec d × PDE.Vec d) :
        Tendsto (fun t : ℝ => parabolicDuhamelIntegrand K
          (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g (t, w.1) r * ψ (packQ d (t, w)))
        (𝓝[<] r) (𝓝 (g (r, w.1) * ψ (packQ d (r, w)))) := by
      have slice_leftLimit {B : CoefficientField d} (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ) (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
          (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K) (g : TimeVelocity d → ℝ) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (r : ℝ) (v : PDE.Vec d) (hv : (r, v) ∈ duhamelFiber Ω γ T) :
          Tendsto (fun t : ℝ => parabolicDuhamelIntegrand K
            (measurableSet_of_isAdmissibleEvolutionDomain hΩa) g (t, v) r) (𝓝[<] r)
          (𝓝 (g (r, v))) := by
        obtain ⟨V, -, hVc, -, -, hterm, hVeq⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
        have hU := isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
        have hcl : (r, v) ∈ sliceClosedCylinder Ω γ r := ⟨le_rfl, subset_closure hv.2⟩
        have hev : ∀ᶠ t in 𝓝[<] r, (t, v) ∈ sliceClosedCylinder Ω γ r := by
          have hn :=
            (continuous_id.prodMk continuous_const).continuousAt.eventually (hU.mem_nhds hv)
          filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht2
          exact ⟨le_of_lt ht2, subset_closure ht.2⟩
        have hmap : Tendsto (fun t : ℝ => (t, v)) (𝓝[<] r) (𝓝[sliceClosedCylinder Ω γ r] (r, v)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, hev⟩
          exact ((continuous_id.prodMk continuous_const).tendsto r).mono_left nhdsWithin_le_nhds
        have h1 := (hVc _ hcl).tendsto.comp hmap
        rw [hterm v (hcl.2)] at h1
        refine h1.congr' ?_
        filter_upwards [hev] with t ht
        exact (hVeq (t, v) ht).symm
      have hψt : Tendsto (fun t : ℝ => ψ (packQ d (t, w))) (𝓝[<] r) (𝓝 (ψ (packQ d (r, w)))) :=
        ((hψ.comp (continuous_packQ.comp (continuous_id.prodMk continuous_const))).tendsto r).mono_left
          nhdsWithin_le_nhds
      by_cases h0 : ψ (packQ d (r, w)) = 0
      · rw [h0, mul_zero]
        have hb : Tendsto (fun t : ℝ => C * |ψ (packQ d (t, w))|) (𝓝[<] r) (𝓝 0) := by
          have := (hψt.abs).const_mul C
          simpa [h0] using this
        refine squeeze_zero_norm (fun t => ?_) hb
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hub _ _) (abs_nonneg _)
      · have hsupp : packQ d (r, w) ∈ tsupport ψ := subset_closure h0
        have hv : (r, w.1) ∈ duhamelFiber Ω γ T := by
          simpa only [mem_preimage, evolutionToTimeVelocity_packQ] using (hψs hsupp)
        exact (slice_leftLimit hΩa hγ hP g hgs hgc T hgU r w.1 hv).mul hψt
    have potential_eq_integral_Ioi {hΩ : MeasurableSet Ω} (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (p : TimeVelocity d) :
        parabolicDuhamelPotential K hΩ T g p =
        ∫ r in Ioi p.1, parabolicDuhamelIntegrand K hΩ g p r := by
      have integrand_eq_zero_of_ge {hΩ : MeasurableSet Ω} {r : ℝ} (hr : T ≤ r) :
          parabolicDuhamelIntegrand K hΩ g p r = 0 := by
        refine parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg p r (fun v => ?_)
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact absurd (hgU h).1 (not_lt.2 hr)
      unfold parabolicDuhamelPotential
      symm
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Ioc_subset_Ioi_self (fun r hr => ?_)
      exact integrand_eq_zero_of_ge (not_lt.1 fun h => hr.2 ⟨hr.1, h.le⟩)
    have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
    obtain ⟨a, b₀, hab⟩ := exists_time_range g hgc
    obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
    have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
    have hC0 := (hgn (0, 0)).trans (hgb _)
    have hgm := hgs.continuous.measurable
    have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
      hgm.comp (measurable_const.prodMk measurable_id)
    have hmeas := measurable_parabolicDuhamelIntegrand K hΩ hγ g hgm
    have hub : ∀ p r, |parabolicDuhamelIntegrand K hΩ g p r| ≤ C := fun p r => by
      rw [abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
      exact parabolicDuhamelIntegrand_le K hΩ g hg hgn C hgb p r
    let Λ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q =>
      transportedAdjoint (zIndependentCoefficient B) b ψ (packQ d q)
    let Ψ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => ψ (packQ d q)
    have hΛc : Continuous Λ :=
      (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
    have hΛs : HasCompactSupport Λ :=
      hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
    have hΨc : Continuous Ψ := hψ.continuous.comp continuous_packQ
    have hΨs : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
    have per : ∀ r : ℝ, (∫ q : ℝ × (PDE.Vec d × PDE.Vec d),
        {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
          (fun q => parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r * Λ q) q) +
        ∫ w : PDE.Vec d × PDE.Vec d, g (r, w.1) * Ψ (r, w) = 0 := by
      intro r
      obtain ⟨V, -, -, hVsm, hVeq, -, hVint⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
      exact slice_weak_identity (u := fun p => parabolicDuhamelIntegrand K hΩ g p r) hB hb (isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ r)
        hVsm hVeq (fun p hp => hVint p ⟨hp.1.le, subset_closure hp.2⟩)
        (hmeas.comp (measurable_id.prodMk measurable_const)) C hC0 (fun p => hub p r) hψ hc r
        (fun x hx hxr => ⟨hxr, (hψs hx).2⟩)
        (fun w => g (r, w.1) * ψ (packQ d (r, w)))
        (slice_terminal_limit hΩa hγ hP g hgs hgc T hgU C hub hψ.continuous hψs r)
    -- Fubini in the source time `r` and the packed coordinates `q`.
    let F1 : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) → ℝ := fun z =>
      {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1}.indicator
        (fun z => parabolicDuhamelIntegrand K hΩ g (z.2.1, z.2.2.1) z.1 * Λ z.2) z
    have hS : MeasurableSet {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} :=
      measurableSet_lt (measurable_snd.fst) measurable_fst
    have hGm :=
      (hmeas.comp (((measurable_snd.fst).prodMk (measurable_snd.snd.fst)).prodMk
        measurable_fst)).mul (hΛc.measurable.comp measurable_snd)
    have hF1m : Measurable F1 := hGm.indicator hS
    have hbnd : Integrable (fun z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) =>
        (Icc a b₀).indicator (fun _ => C) z.1 * ‖Λ z.2‖)
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))) :=
      Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (by simp))) (hΛc.integrable_of_hasCompactSupport hΛs).norm
    have hF1int : Integrable F1
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))) := by
      refine hbnd.mono' hF1m.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      have hnn : 0 ≤ (Icc a b₀).indicator (fun _ => C) z.1 * ‖Λ z.2‖ :=
        mul_nonneg (indicator_nonneg (fun _ _ => hC0) _) (norm_nonneg _)
      by_cases hz : z.2.1 < z.1
      · have hF : F1 z = parabolicDuhamelIntegrand K hΩ g (z.2.1, z.2.2.1) z.1 * Λ z.2 :=
          indicator_of_mem (show z ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
        rw [hF, norm_mul, Real.norm_eq_abs]
        by_cases hr : z.1 ∈ Icc a b₀
        · rw [indicator_of_mem hr]
          exact mul_le_mul_of_nonneg_right (hub _ _) (norm_nonneg _)
        · rw [parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg _ _ (hab _ hr)]
          simpa using hnn
      · have hF : F1 z = 0 :=
          indicator_of_notMem
            (show z ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
        rw [hF, norm_zero]
        exact hnn
    let F2 : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => g (q.1, q.2.1) * Ψ q
    have hF2c : Continuous F2 :=
      (hgs.continuous.comp (continuous_fst.prodMk (continuous_snd.fst))).mul hΨc
    have hF2int : Integrable F2
        ((volume : Measure ℝ).prod (volume : Measure (PDE.Vec d × PDE.Vec d))) :=
      hF2c.integrable_of_hasCompactSupport hΨs.mul_left
    have hAint : Integrable (fun r => ∫ q, F1 (r, q)) :=
      hF1int.integral_prod_left
    have hMint : Integrable (fun r => ∫ w, F2 (r, w)) :=
      hF2int.integral_prod_left
    have hsum : (∫ r, ∫ q, F1 (r, q)) + ∫ r, ∫ w, F2 (r, w) = 0 := by
      rw [← integral_add hAint hMint]
      have : (fun r => (∫ q, F1 (r, q)) + ∫ w, F2 (r, w)) = fun _ => 0 := funext per
      rw [this, integral_zero]
    have hA : (∫ r, ∫ q, F1 (r, q)) =
        ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
          parabolicDuhamelPotential K hΩ T g (q.1, q.2.1) := by
      rw [← integral_prod F1 hF1int, integral_prod_symm F1 hF1int]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      have hfun : (fun r => F1 (r, q)) = (Ioi q.1).indicator
          (fun r => Λ q * parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r) := by
        funext r
        by_cases hr : q.1 < r
        · rw [indicator_of_mem (show r ∈ Ioi q.1 from hr)]
          exact (indicator_of_mem (show (r, q) ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
            z.2.1 < z.1} from hr) _).trans (mul_comm _ _)
        · rw [indicator_of_notMem (show r ∉ Ioi q.1 from hr)]
          exact indicator_of_notMem (show (r, q) ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
            z.2.1 < z.1} from hr) _
      have hq : ∫ r, F1 (r, q) = Λ q * ∫ r in Ioi q.1,
          parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r := by
        change ∫ r, (fun r => F1 (r, q)) r = _
        rw [hfun, integral_indicator measurableSet_Ioi, integral_const_mul]
      show (∫ r, F1 (r, q)) = Λ q * parabolicDuhamelPotential K hΩ T g (q.1, q.2.1)
      rw [hq, potential_eq_integral_Ioi hg (q.1, q.2.1)]
    have hM : (∫ r, ∫ w, F2 (r, w)) = ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), F2 q :=
      (integral_prod F2 hF2int).symm
    rw [hA, hM] at hsum
    have e1 : (∫ x, parabolicDuhamelPotential K hΩ T g (evolutionToTimeVelocity d x) *
        transportedAdjoint (zIndependentCoefficient B) b ψ x) =
        ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
          parabolicDuhamelPotential K hΩ T g (q.1, q.2.1) := by
      rw [integral_evolution_eq_prod]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only [evolutionToTimeVelocity_packQ, Λ]
      ring
    have e2 : (∫ x, g (evolutionToTimeVelocity d x) * ψ x) = ∫ q, F2 q := by
      rw [integral_evolution_eq_prod]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only [evolutionToTimeVelocity_packQ, F2, Ψ]
    rw [e1, e2]
    linarith
  have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  set W := parabolicDuhamelPotential K hΩ T g with hW
  obtain ⟨hsm, hsymm, hell⟩ := SectionTwo.sectionTwoCoefficient_fullBounds lam Lam B hB
  have hlam : 0 < lam := hB.1
  have hb : IsSmoothDrift (SectionTwo.identityDrift d) := SectionTwo.identityDrift_smooth d
  set Qp := evolutionToTimeVelocity d with hQp
  have hU₀ : IsOpen (duhamelFiber Ω γ T) :=
    isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
  have hU : IsOpen (Qp ⁻¹' duhamelFiber Ω γ T) := hU₀.preimage Qp.continuous
  have hWc : ContinuousOn W (duhamelFiber Ω γ T) :=
    (continuousOn_duhamelPotential K hΩa hγ hP g hgn hgs hgc T hgU).mono
      (duhamelFiber_subset_closedFiber T)
  have hWQ : ContinuousOn (fun x => W (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) :=
    hWc.comp Qp.continuous.continuousOn (fun x hx => hx)
  -- the weak equation on the packed set
  have hweak : IsWeakTransportedSolution (zIndependentCoefficient B) (SectionTwo.identityDrift d)
      (Qp ⁻¹' duhamelFiber Ω γ T) (fun x => W (Qp x)) (fun x => -g (Qp x)) := by
    refine ⟨hWQ.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [neg_mul, integral_neg]
      exact duhamel_weak_identity hΩa hγ hP hsm hb g hgn hgs hgc T hgU hψ hc hs
    · intro x hx
      have : x ∉ tsupport ψ := fun h => hx (hs h)
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    · intro x hx
      have : x ∉ tsupport ψ := fun h => hx (hs h)
      rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ this, mul_zero]
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => -g (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) :=
    ((hgs.comp Qp.contDiff).neg).contDiffOn
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hlam hsm hell hb
    one_pos ((SectionTwo.identityDrift_bounds d).2) hU hweak hg'
  have heq : EqOn (fun x => W (Qp x)) f (Qp ⁻¹' duhamelFiber Ω γ T) :=
    Measure.eqOn_open_of_ae_eq hae hU hWQ hf.continuousOn
  -- smoothness of `W`
  have hι : ∀ p : TimeVelocity d, Qp (packPoint p.1 p.2 0) = p := fun p => by
    simp [hQp]
  have hmaps : MapsTo (fun p : TimeVelocity d => packPoint p.1 p.2 0)
      (duhamelFiber Ω γ T) (Qp ⁻¹' duhamelFiber Ω γ T) := fun p hp => by
    simpa [hι] using hp
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) W (duhamelFiber Ω γ T) := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ fun p : TimeVelocity d =>
        packPoint p.1 p.2 0) (duhamelFiber Ω γ T) :=
      hf.comp contDiff_zeroLift.contDiffOn hmaps
    refine h1.congr fun p hp => ?_
    have := heq (hmaps hp)
    simpa [hι] using this
  refine ⟨hsmooth, ?_⟩
  -- the classical equation
  have hBc : ∀ i j, Continuous (fun p : TimeVelocity d => B p.1 p.2 i j) := fun i j =>
    (hsm i j).continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk
      (continuous_const : Continuous fun _ : TimeVelocity d => (0 : PDE.Vec d))))
  have hopQ : ContinuousOn (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x))
      (Qp ⁻¹' duhamelFiber Ω γ T) := (continuousOn_scalarParabolicOperator_of_contDiffOn hBc hU₀ hsmooth).comp Qp.continuous.continuousOn (fun x hx => hx)
  have hgQ : Continuous (fun x => g (Qp x)) := hgs.continuous.comp Qp.continuous
  have hzero : ∀ x ∈ Qp ⁻¹' duhamelFiber Ω γ T,
      scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x) = 0 := by
    have hcont : ContinuousOn (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) +
        g (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) := hopQ.add hgQ.continuousOn
    have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hcont.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
        have h1 := integral_transportedAdjoint_zIndep hsm hb hU₀ hsmooth hψ hc hs
        have h2 := hweak.2 ψ hψ hc hs
        have iA := integrable_evolution_mul_test hopQ hψ.continuous hc hs
        have iG := integrable_evolution_mul_test hgQ.continuousOn hψ.continuous hc hs
        have hAeq : (∫ x in Qp ⁻¹' duhamelFiber Ω γ T,
            scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x) =
            ∫ x, scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
        have hGeq : (∫ x in Qp ⁻¹' duhamelFiber Ω γ T, -g (Qp x) * ψ x) =
            -∫ x, g (Qp x) * ψ x := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero])]
          simp only [neg_mul, integral_neg]
        rw [hAeq] at h1
        have h3 : (∫ x, scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x) +
            ∫ x, g (Qp x) * ψ x = 0 := by
          have := h1.symm.trans h2
          rw [hGeq] at this
          linarith
        have : (fun x => ψ x • (scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x))) =
            fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x + g (Qp x) * ψ x := by
          funext x; simp; ring
        rw [this, integral_add iA iG, h3])
    have hae1 : (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x))
        =ᵐ[volume.restrict (Qp ⁻¹' duhamelFiber Ω γ T)] fun _ => (0 : ℝ) :=
      (ae_restrict_iff' hU.measurableSet).2 hae0
    exact Measure.eqOn_open_of_ae_eq hae1 hU hcont continuousOn_const
  intro p hp
  have := hzero (packPoint p.1 p.2 (0 : PDE.Vec d)) (hmaps hp)
  rw [hι] at this
  linarith

end Potential

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

