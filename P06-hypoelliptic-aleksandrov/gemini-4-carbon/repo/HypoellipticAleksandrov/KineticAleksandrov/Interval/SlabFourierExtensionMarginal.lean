module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockRetentionLift
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CorridorSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CommonSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhase
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.OppositePaths
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierOccupation
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Decay HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.Scaling
open scoped ProbabilityTheory

/-- A ball fits whenever both endpoint distances exceed its radius. -/
theorem interval_ball_subset_of_distance {a c R : ℝ} (hR : 0 < R) (v : PDE.Vec 1)
    (hd : R < min (v 0 - a) (c - v 0)) :
    PDE.euclideanBall v R ⊆ PDE.oneDimensionalAxisBox a c := by
  intro w hw
  rw [PDE.mem_oneDimensionalAxisBox_iff]
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR,
    vecEuclideanNorm_vec_one] at hw
  have hh := abs_lt.mp hw
  simp only [PDE.vecOneCoordinate]
  simp at hh
  constructor <;> linarith only [hh.1, hh.2, ((lt_min_iff.mp hd).1), ((lt_min_iff.mp hd).2)]

/-- The length-independent boundary branch of the unit block. -/
theorem interval_boundary_block
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K)
    (σ : ℝ) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
    (hb : min (v 0 - a) (c - v 0) ≤ blockOuter Lb)
    (ξ : PDE.Vec 1) (hL : σ ≤ σ + blockTime m Lb)
    (ν : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection K (movingQuery σ (σ + blockTime m Lb) hL v 0 hv) ξ ν) :
    TV ν ≤ intervalHeat lam (blockTime m Lb) (blockOuter Lb) := by
  have ht : 0 < blockTime m Lb := by
    unfold blockTime
    have h := blockL0_pos hs.2.2.1
    positivity
  have hkill := interval_killing hH hLE hac B b hs hJ S K hr
    σ (σ + blockTime m Lb) (lt_add_of_pos_right σ ht) v hv
  have htv := interval_fourier_tv_le_mass hJ K B ((interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1) σ (σ + blockTime m Lb) hL
    v 0 ξ hv ν hν
  have hnorm : σ + blockTime m Lb - σ = blockTime m Lb := by ring
  rw [hnorm] at hkill
  exact htv.trans (hkill.trans (intervalHeat_mono_distance hs.1.1 ht hb))



/-- The affine preimage of an interval, with no fallback outside that domain. -/
theorem scaledDomain_interval (a c : ℝ) (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r =
      PDE.oneDimensionalAxisBox ((a - v₀ 0) / r.1) ((c - v₀ 0) / r.1) := by
  ext Y
  simp [scaledDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate]
  rw [div_lt_iff₀ r.2, lt_div_iff₀ r.2]
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- Rescaled endpoints remain strictly ordered. -/
theorem scaled_interval_endpoints {a c : ℝ} (hac : a < c)
    (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    (a - v₀ 0) / r.1 < (c - v₀ 0) / r.1 :=
  (div_lt_div_iff_of_pos_right r.2).2 (sub_lt_sub_right hac _)

/-- Admissibility of the rescaled interval. -/
theorem scaled_interval_admissible {a c : ℝ} (hac : a < c)
    (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    IsAdmissibleEvolutionDomain (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) := by
  rw [scaledDomain_interval]
  exact interval_admissible (scaled_interval_endpoints hac v₀ r)

/-- Source setting and all constants are preserved under interval scaling. -/
theorem scaled_interval_setting (lam Lam m Lb a c σ₀ : ℝ) (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    SourceSetting lam Lam m Lb (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      (scaledCoefficient B σ₀ v₀ r) (scaledDrift b v₀ r) := by
  rw [scaledDomain_interval]
  exact sourceSetting_interval (scaled_interval_endpoints hac v₀ r) _ _
    (scaledCoefficient_sectionTwo lam Lam B hs.1 σ₀ v₀ r)
    (scaledDrift_smooth b v₀ r hs.2.1) hs.2.2.1 hs.2.2.2.1
    (scaledDrift_transportBounds b v₀ r hs.2.2.2.2.1)

/-- The source kinetic affine map carries the rescaled stationary interval to the original. -/
theorem mapsDomain_interval (a c σ₀ : ℝ) (v₀ z₀ : PDE.Vec 1)
    (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    (KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r).MapsDomain
      (PDE.oneDimensionalAxisBox a c) stationary
      (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) stationary := by
  intro τ
  ext Y
  simp [movingDomain, stationary, PDE.mem_translateSet_iff_sub_mem, scaledDomain]
  rfl

/-- The rescaled interval realization is the affine pushforward of the original realization. -/
theorem realizes_ofRadius_interval (a c σ₀ : ℝ) (hac : a < c)
    (v₀ z₀ : PDE.Vec 1) (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r})
    {B : CoefficientField 1}
    {S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary}
    {K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary}
    (hreal : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary
      (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac))
      (zIndependentCoefficient B) b S K) :
    let hmap := mapsDomain_interval a c σ₀ v₀ z₀ b r
    let hJr := measurableSet_of_isAdmissibleEvolutionDomain
      (scaled_interval_admissible hac v₀ r)
    RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary hJr (zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r))
      (scaledDrift b v₀ r)
      (fiberOperator (KineticAffineScaling.pushKernel hmap K) hJr)
      (KineticAffineScaling.pushKernel hmap K) := by
  have h := KineticAffineScaling.realizes_pushKernel
    (mapsDomain_interval a c σ₀ v₀ z₀ b r)
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac)) continuous_const
    (measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible hac v₀ r)) hreal
  rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift] at h
  exact h

/-- Fourier affine image and exact total-variation equality on the rescaled interval. -/
theorem realizes_ofRadius_interval_fourier_tv (a c σ₀ : ℝ) (hac : a < c)
    (v₀ z₀ : PDE.Vec 1) (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r})
    {B : CoefficientField 1}
    {S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary}
    {K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary}
    (hreal : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary
      (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac))
      (zIndependentCoefficient B) b S K)
    {S' : TerminalOperatorFamily (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary}
    {K' : MovingFiberKernel (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) stationary}
    (hreal' : RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary (measurableSet_of_isAdmissibleEvolutionDomain
        (scaled_interval_admissible hac v₀ r))
      (zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r)) (scaledDrift b v₀ r) S' K')
    (q' : EvolutionQuery (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) stationary)
    (ξ : PDE.Vec 1) (ν ν' : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection K (KineticAffineScaling.queryMap
      (mapsDomain_interval a c σ₀ v₀ z₀ b r) q') ξ ν)
    (hν' : IsFourierProjection K' q' (r.1 ^ 3 • ξ) ν') :
    (∀ E : Set (PDE.Vec 1), MeasurableSet E →
      ν E = Complex.exp (-Complex.I *
        ((r.1 ^ 2 * (q'.1.2.1 - q'.1.1) * PDE.vecDot ξ (b v₀) : ℝ) : ℂ)) *
        ν' ((fun Y : PDE.Vec 1 => v₀ + r.1 • Y) ⁻¹' E)) ∧
      totalVariationNorm ν = totalVariationNorm ν' := by
  have hreal'' : RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary (measurableSet_of_isAdmissibleEvolutionDomain
        (scaled_interval_admissible hac v₀ r))
      ((KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r).coefficient (zIndependentCoefficient B))
      ((KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r).drift b) S' K' := by
    rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift]
    exact hreal'
  exact KineticAffineScaling.realizes_fourier_tv _ (interval_admissible hac)
    (zeroCurve_piecewiseC1 1) (scaled_interval_admissible hac v₀ r)
    hreal hreal'' q' ξ ν ν' hν hν'



section
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Decay Filter HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.Occupation HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal

/-- The ambient velocity marginal is exactly the derived scalar parabolic measure. -/
theorem interval_firstMarginal_eq_parabolic {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    K.firstMarginal (movingQuery σ τ hστ v z hv) =
      P K hJ (scalarQuery σ τ hστ v hv) := by
  obtain ⟨Q, hfirst, _⟩ := hp (fun _ _ _ _ => rfl)
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hJ σ τ hστ
    (evolutionStateOfPosition (PDE.oneDimensionalAxisBox a c) stationary σ ⟨v, hv⟩ z)
  rw [← hfirst σ τ hστ ⟨v, hv⟩ z] at hmap
  exact hmap.symm

section

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

open HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {a c : ℝ}
variable (σ T : ℝ) (hT : 0 < T)

include hT in
/-- Finite positive elapsed horizons carry finite Lebesgue measure. -/
theorem intervalElapsedVolume_finite : IsFiniteMeasure (elapsedVolume (ENNReal.ofReal T)) :=
  ⟨by rw [elapsedVolume_univ T hT]; exact ENNReal.ofReal_lt_top⟩

/-- Pull back the first marginal along the literal finite-horizon occupation queries. -/
def intervalOccupationKernel (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary) :
    ProbabilityTheory.Kernel ((PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T))
      (PDE.Vec 1) :=
  K.firstMarginal.comap (fun q => movingQuery σ (σ + q.2.1) (le_add_of_nonneg_right q.2.2.1.le)
    q.1.1 0
    (by simpa only [movingDomain_stationary] using q.1.2)) (by
    apply Measurable.subtype_mk
    change Measurable (fun q : (PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T) =>
      (σ, (σ + q.2.1, (q.1.1, 0))))
    fun_prop)

/-- The pulled-back velocity kernel is finite. -/
instance intervalOccupationKernel_finite (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) :
    ProbabilityTheory.IsFiniteKernel (intervalOccupationKernel σ T K) := by
  unfold intervalOccupationKernel MovingFiberKernel.firstMarginal
  infer_instance

/-- The finite-horizon occupation measure, with time and velocity in source order. -/
def intervalOccupationMeasure (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
  (ρ : Measure (PDE.oneDimensionalAxisBox a c)) :
    Measure (TimeVelocity 1) :=
  ((ρ.prod (elapsedVolume (ENNReal.ofReal T))).compProd (intervalOccupationKernel σ T K)).map
    (fun q => (q.1.2.1, q.2))

include hT in
/-- The projected occupation measure is finite for finite initial measures. -/
theorem intervalOccupationMeasure_finite (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] : IsFiniteMeasure (intervalOccupationMeasure σ T K ρ) := by
  have := intervalElapsedVolume_finite T hT
  unfold intervalOccupationMeasure
  infer_instance

include hT in
/-- Positive elapsed time puts the entire occupation measure in the open finite slab. -/
theorem intervalOccupationMeasure_compl_slab (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a
  c) stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c)) :
    intervalOccupationMeasure σ T K ρ (Ioo (0 : ℝ) T ×ˢ univ)ᶜ = 0 := by
  rw [intervalOccupationMeasure, Measure.map_apply (by fun_prop)
    ((measurableSet_Ioo.prod MeasurableSet.univ).compl)]
  have he : (fun q : ((PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T)) × PDE.Vec
    1 =>
      (q.1.2.1, q.2)) ⁻¹'
      (Ioo 0 T ×ˢ univ)ᶜ = ∅ := by
    ext q
    simp
    exact ⟨q.1.2.2.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mp q.1.2.2.2)⟩
  rw [he, measure_empty]

include hT in
/-- Projected occupation integration is the full iterated first-marginal characterization. -/
theorem integral_intervalOccupationMeasure (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] (φ : TimeVelocity 1 → ℝ) (hφ : Measurable φ)
    (hφb : ∃ M : ℝ, ∀ q, |φ q| ≤ M) :
    (∫ q, φ q ∂intervalOccupationMeasure σ T K ρ) =
      ∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal T),
        ∫ w, φ (τ.1, w) ∂K.firstMarginal
          (movingQuery σ (σ + τ.1) (le_add_of_nonneg_right τ.2.1.le) v.1 0
            (by simpa only [movingDomain_stationary] using v.2))
        ∂elapsedVolume (ENNReal.ofReal T) ∂ρ := by
  have := intervalElapsedVolume_finite T hT
  obtain ⟨M, hM⟩ := hφb
  let ψ : ((PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T)) × PDE.Vec 1 → ℝ :=
    fun q => φ (q.1.2.1, q.2)
  have hψ : Measurable ψ := hφ.comp (by fun_prop)
  have hi : Integrable ψ ((ρ.prod (elapsedVolume (ENNReal.ofReal T))).compProd
      (intervalOccupationKernel σ T K)) :=
    (integrable_const M).mono' hψ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa using hM _)
  rw [intervalOccupationMeasure, integral_map (by fun_prop) hφ.aestronglyMeasurable]
  change (∫ q, ψ q ∂_) = _
  rw [Measure.integral_compProd hi]
  exact (integral_prod _ hi.integral_compProd).trans (by
    simp only [ProbabilityTheory.Kernel.prodMkLeft_apply, intervalOccupationKernel,
      ProbabilityTheory.Kernel.comap_apply, ψ])

/-- Set evaluation of the projected occupation measure is the iterated kernel action. -/
theorem intervalOccupationMeasure_apply
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ]
    (A : Set (TimeVelocity 1)) (hA : MeasurableSet A) :
    intervalOccupationMeasure σ T K ρ A =
      ∫⁻ v, ∫⁻ t : ElapsedTime (ENNReal.ofReal T),
        intervalOccupationKernel σ T K (v, t) {w | (t.1, w) ∈ A}
          ∂elapsedVolume (ENNReal.ofReal T) ∂ρ := by
  rw [intervalOccupationMeasure, Measure.map_apply (by fun_prop) hA,
    Measure.compProd_apply (hA.preimage (by fun_prop))]
  exact lintegral_prod _
    ((ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
      (κ := intervalOccupationKernel σ T K) (hA.preimage (by fun_prop))).aemeasurable)

include hT in
/-- The occupation measure is concentrated in the open time-interval product. -/
theorem intervalOccupationMeasure_compl_region
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ] :
    intervalOccupationMeasure σ T K ρ
      (Ioo (0 : ℝ) T ×ˢ PDE.oneDimensionalAxisBox a c)ᶜ = 0 := by
  rw [intervalOccupationMeasure_apply σ T K ρ _ (measurableSet_Ioo.prod hJ).compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  refine Filter.Eventually.of_forall fun v => ?_
  apply lintegral_eq_zero_of_ae_eq_zero
  refine Filter.Eventually.of_forall fun t => ?_
  have he : {w : PDE.Vec 1 | (t.1, w) ∈
      (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)ᶜ} =
        (PDE.oneDimensionalAxisBox a c)ᶜ := by
    ext w
    simp [t.2.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mp t.2.2)]
  dsimp only
  rw [he]
  let q : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary := movingQuery σ (σ + t.1)
    (le_add_of_nonneg_right t.2.1.le) v.1 0
    (by simpa using v.2)
  change K.firstMarginal q _ = 0
  have hpre : MeasurableSet {p : EvolutionAmbientState 1 |
      p.1 ∈ (PDE.oneDimensionalAxisBox a c)ᶜ} := hJ.compl.preimage measurable_fst
  rw [K.firstMarginal_apply q _ hJ.compl, ← K.terminal_support q,
    Measure.restrict_apply hpre]
  have he' : {p : EvolutionAmbientState 1 | p.1 ∈
      (PDE.oneDimensionalAxisBox a c)ᶜ} ∩
      evolutionStateSet (PDE.oneDimensionalAxisBox a c) stationary q.1.2.1 = ∅ := by
    ext p
    simp [evolutionStateSet, movingDomain_stationary, not_and_self, mem_empty_iff_false]
  rw [he', measure_empty]

end

/-- A finite measure dominated by a real density has a smaller real density. -/
theorem exists_real_density_of_le_withDensity {X : Type*} [MeasurableSpace X]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν]
    (f : X → ℝ) (_hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hle : ν ≤ m.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g m ∧
      (∀ᵐ x ∂m, g x ≤ f x) ∧
      (∀ φ : X → ℝ, (∫ x, φ x * g x ∂m) = ∫ x, φ x ∂ν) := by
  have hac := hle.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hrle : ∀ᵐ x ∂m, ν.rnDeriv m x ≤ ENNReal.ofReal (f x) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀
      (Measure.measurable_rnDeriv ν m).aemeasurable
    intro E hE _
    have h := Measure.le_iff.1 hle E hE
    rw [← Measure.withDensity_rnDeriv_eq ν m hac, withDensity_apply _ hE,
      withDensity_apply _ hE] at h
    exact h
  refine ⟨(fun x => (ν.rnDeriv m x).toReal), (Measure.measurable_rnDeriv ν m).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · simpa using
      Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := m) (measure_ne_top ν univ)
  · filter_upwards [hrle] with x hx
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
      (ENNReal.toReal_ofReal (hf0 x))
  · intro φ
    simpa only [mul_comm] using integral_toReal_rnDeriv_mul hac


/-- Nonnegative smooth interior tests have smaller interval transition integral. -/
theorem interval_scalar_test_le_whole {a c lam Lam σ τ : ℝ}
    (hac : a < c) (hστ : σ < τ) (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (Kw : MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hpw : HasParabolicMarginalBundle (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) MeasurableSet.univ
      (zIndependentCoefficient B) Kw)
    (φ : PDE.Vec 1 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφJ : tsupport φ ⊆ PDE.oneDimensionalAxisBox a c)
    (hφ0 : ∀ v, 0 ≤ φ v) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (∫ w, φ w ∂P K hJ (scalarQuery σ τ hστ.le v hv)) ≤
      ∫ w, φ w ∂Kw.firstMarginal (wholeSpaceQuery σ τ hστ.le v 0) := by
  obtain ⟨M, hM⟩ := hφs.continuous.bounded_above_of_compact_support hφc
  let F : BoundedBorel (PDE.Vec 1) :=
    ⟨φ, hφs.continuous.measurable, ⟨max M 0, le_max_right _ _, fun w =>
      (show |φ w| ≤ M from by simpa using hM w).trans
        (le_max_left _ _)⟩⟩
  obtain ⟨Q, _, _, _, _, _, hrepr, _, _, _, hsolve⟩ := hp (fun _ _ _ _ => rfl)
  obtain ⟨Qw, hfirstw, _, hposw, _, _, hreprw, _, _, _, hsolvew⟩ :=
    hpw (fun _ _ _ _ => rfl)
  obtain ⟨V, hV, heval, _⟩ := hsolve τ F
    ⟨hφs, hφc, by simpa only [movingDomain_stationary] using hφJ⟩
  obtain ⟨U, hU, hevalw, _⟩ := hsolvew τ F
    ⟨hφs, hφc, fun _ _ => by simp [movingDomain_wholeSpace]⟩
  have hUn : ∀ p : TimeVelocity 1, p.1 ≤ τ → 0 ≤ U p := by
    intro p ht
    rw [hevalw p.1 ht ⟨p.2, by simp [movingDomain_wholeSpace]⟩]
    exact hposw p.1 τ ht (terminalPositionDatum F) (fun w => hφ0 w.1) _
  have hcmp := interval_terminal_comparison hac hστ hB.1 B hB F V U hV
    (hU.2.1.mono fun p hp => ⟨hp.1.2, by
      simp [movingDomain_wholeSpace, closure_univ]⟩)
    (fun p hp => (hU.2.2.1 p ⟨hp.1.2, by
      simp [movingDomain_wholeSpace]⟩).contDiffAt
      (by
        simpa [ParabolicProbe.scalarPastOpenCylinder, movingDomain_wholeSpace, preimage, Iio] using
          (isOpen_Iio.preimage continuous_fst).mem_nhds hp.1.2)
      |>.of_le (by norm_num))
    (fun p hp => (hU.2.2.2.1 p ⟨hp.1.2, by
      simp [movingDomain_wholeSpace]⟩).le)
    (fun w _ => (hU.2.2.2.2.1 (τ, w) ⟨rfl, by
      simp [movingDomain_wholeSpace, closure_univ]⟩).ge)
    (fun p hp => hUn p hp.1.2) v (subset_closure (by
      simpa only [movingDomain_stationary] using hv))
  rw [heval σ hστ.le ⟨v, hv⟩, hrepr] at hcmp
  rw [hevalw σ hστ.le ⟨v, by simp [movingDomain_wholeSpace]⟩, hreprw] at hcmp
  change (∫ w, φ w ∂Measure.map Subtype.val
    (parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩)) ≤ _
  rw [(integral_map (μ := parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩) measurable_subtype_coe.aemeasurable hφs.continuous.measurable.aestronglyMeasurable)]
  have hmap := Kw.map_fiberFirstMarginal_eq_firstMarginal MeasurableSet.univ σ τ
    hστ.le (evolutionStateOfPosition (wholeSpace 1) (fun _ => 0) σ
      ⟨v, by simp [movingDomain_wholeSpace]⟩ 0)
  have hfirstw' := hfirstw σ τ hστ.le
    ⟨v, by simp [movingDomain_wholeSpace]⟩ 0
  rw [← hfirstw'] at hmap
  change (∫ w, φ w.1 ∂parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩) ≤
    ∫ w, φ w ∂Kw.firstMarginal
      (evolutionQueryOfState (wholeSpace 1) (fun _ => 0) σ τ hστ.le
        (evolutionStateOfPosition (wholeSpace 1) (fun _ => 0) σ
          ⟨v, by simp [movingDomain_wholeSpace]⟩ 0))
  rw [← hmap, (integral_map (μ := parabolicMarginalKernel Kw MeasurableSet.univ σ τ hστ.le ⟨v, by simp [movingDomain_wholeSpace]⟩) measurable_subtype_coe.aemeasurable hφs.continuous.measurable.aestronglyMeasurable)]
  exact hcmp


/-- The scalar interval transition is dominated by the whole-space scalar transition. -/
theorem interval_parabolic_le_whole {a c lam Lam σ τ : ℝ}
    (hac : a < c) (hστ : σ < τ) (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (Kw : MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hpw : HasParabolicMarginalBundle (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) MeasurableSet.univ
      (zIndependentCoefficient B) Kw)
    (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    P K hJ (scalarQuery σ τ hστ.le v hv) ≤
      Kw.firstMarginal (wholeSpaceQuery σ τ hστ.le v 0) := by
  let ν := P K hJ (scalarQuery σ τ hστ.le v hv)
  have : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [← interval_firstMarginal_eq_parabolic hJ K B hp σ τ hστ.le v 0 hv]
    unfold MovingFiberKernel.firstMarginal
    infer_instance
  have : IsFiniteMeasure (Kw.firstMarginal (wholeSpaceQuery σ τ hστ.le v 0)) := by
    refine ⟨?_⟩
    rw [Kw.firstMarginal_apply _ _ MeasurableSet.univ]
    simp

  have hcompl : ν (PDE.oneDimensionalAxisBox a c)ᶜ = 0 := by
    change (Measure.map Subtype.val
      (parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩)) _ = 0
    rw [Measure.map_apply measurable_subtype_coe hJ.compl]
    have he : (Subtype.val : EvolutionPosition (PDE.oneDimensionalAxisBox a c)
        stationary τ → PDE.Vec 1) ⁻¹' (PDE.oneDimensionalAxisBox a c)ᶜ = ∅ := by
      ext w
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      simpa only [movingDomain_stationary] using w.2
    rw [he, measure_empty]
  exact HypoellipticAleksandrov.KineticAleksandrov.measure_le_of_smooth_integral_le
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac)) (Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hcompl))
    (fun φ hφs hφc hφJ hφ0 => interval_scalar_test_le_whole hac hστ B hB
      hJ K hp Kw hpw φ hφs hφc hφJ hφ0 v hv)


/-- Domination on an interior time slab transfers a whole-space occupation density. -/
theorem intervalOccupationMeasure_le_density {a c lam Lam : ℝ}
    (hac : a < c) (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (Kw : MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hpw : HasParabolicMarginalBundle (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
      MeasurableSet.univ (zIndependentCoefficient B) Kw)
    (σ T : ℝ) (hT : 0 < T) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] (g : TimeVelocity 1 → ℝ)
    (hg : SlabOccupationDensity Kw σ T (ρ.map Subtype.val) g)
    (hgi : Integrable g (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ))) :
    intervalOccupationMeasure σ T K ρ ≤
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)).withDensity
        (fun p => ENNReal.ofReal (g p)) := by
  let R : Set (TimeVelocity 1) := Ioo 0 T ×ˢ univ
  have hR : MeasurableSet R := measurableSet_Ioo.prod MeasurableSet.univ
  have hs : (intervalOccupationMeasure σ T K ρ).restrict R =
      intervalOccupationMeasure σ T K ρ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact intervalOccupationMeasure_compl_slab σ T hT K ρ)
  have hsub : ∀ A : Set (TimeVelocity 1), MeasurableSet A → A ⊆ R →
      intervalOccupationMeasure σ T K ρ A ≤
        ∫⁻ p in A, ENNReal.ofReal (g p) := by
    intro A hA hAR
    have hm : Measurable (fun v =>
        ∫⁻ t in Ioo 0 T, occupationKernel Kw σ t v {w | (t, w) ∈ A}) :=
      ((measurable_occupationKernel_section Kw σ hA).comp measurable_swap).lintegral_prod_right'
    rw [occupation_set_identity Kw σ T hT (ρ.map Subtype.val) g hg hgi hA hAR,
      lintegral_map hm measurable_subtype_coe]
    rw [intervalOccupationMeasure_apply σ T K ρ A hA]
    apply lintegral_mono
    intro v
    dsimp only
    rw [← lintegral_elapsed_finite T hT]
    apply lintegral_mono
    intro t
    have hst : σ < σ + t.1 := lt_add_of_pos_right _ t.2.1
    have hv : v.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ := by
      simpa only [movingDomain_stationary] using v.2
    change K.firstMarginal (movingQuery σ (σ + t.1) hst.le v.1 0 hv) _ ≤ _
    rw [(interval_firstMarginal_eq_parabolic hJ K B hp σ (σ + t.1) hst.le v.1 0 hv)]
    dsimp only
    rw [occupationKernel_of_nonneg Kw σ t.1 t.2.1.le]
    exact Measure.le_iff'.1 (interval_parabolic_le_whole hac hst B hB hJ K hp Kw hpw v.1 hv) _
  apply Measure.le_iff.2
  intro A hA
  rw [← hs, Measure.restrict_apply hA, withDensity_apply _ hA]
  calc
    _ ≤ ∫⁻ p in A ∩ R, ENNReal.ofReal (g p) :=
      hsub _ (hA.inter hR) inter_subset_right
    _ = _ := by rw [Measure.restrict_restrict hA]


/-- Interval occupation has a common density with constants independent of interval length. -/
theorem interval_occupation
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ, (∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → 0 ≤ C γ) ∧
    ∀ (m Lb : ℝ), 0 < m → m ≤ Lb →
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    ∀ (σ T : ℝ), 0 < T →
    ∀ (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ],
    ∃ g : TimeVelocity 1 → ℝ, Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      (∀ φ : BoundedBorel (TimeVelocity 1),
        (∫ p, φ p * g p ∂volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) =
        ∫ v, ∫ t : ElapsedTime (ENNReal.ofReal T), ∫ w, φ (t.1, w)
          ∂P K hJ (scalarQuery σ (σ + t.1) (le_add_of_nonneg_right t.2.1.le) v.1
            (by simpa only [movingDomain_stationary] using v.2))
          ∂elapsedVolume (ENNReal.ofReal T) ∂ρ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 →
        MemLp g (ENNReal.ofReal γ)
          (volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) ∧
        eLpNorm g (ENNReal.ofReal γ)
          (volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) ≤
          ENNReal.ofReal (C γ) * ρ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2)) := by
  obtain ⟨C, hC, hocc⟩ := occupation hH (d := 1) (by norm_num)
    lam Lam hlam hlamLam
  refine ⟨C, fun γ hγ1 hγ2 => hC γ hγ1 (by norm_num; exact hγ2), ?_⟩
  intro m Lb _hm _hmLb a c hac B b hs hJ S K hr σ T hT ρ _
  have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
  have hsetting : SourceSetting lam Lam 1 1 (univ : Set (PDE.Vec 1)) B (identityDrift 1) :=
    ⟨hs.1, identityDrift_smooth 1, zero_lt_one, le_rfl, identityDrift_bounds 1,
      Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  obtain ⟨Sw, Kw, hrw, _, hpw, _⟩ :=
    exists_unitBlock_evolution (exists_terminalEvolution_of_classical hLE hH)
      (by norm_num) lam Lam 1 1 univ B (identityDrift 1) hsetting
      (wholeSpace 1) (fun _ => 0) (wholeSpace_admissible 1) (zeroCurve_piecewiseC1 1)
  obtain ⟨gw, hgw, hgwLp⟩ := hocc B hs.1 Sw Kw hrw hpw (ρ.map Subtype.val) σ T hT
  have hdom := intervalOccupationMeasure_le_density hac B hs.1 hJ K hp Kw hpw
    σ T hT ρ gw ((isOccupationDensity_iff_slabOccupationDensity Kw σ T (ρ.map Subtype.val) gw).mp hgw) (memLp_one_iff_integrable.1 (by simpa using (hgwLp 1 le_rfl (by norm_num)).1))
  let U := Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c
  have hU : MeasurableSet U := measurableSet_Ioo.prod hJ
  have hνU : (intervalOccupationMeasure σ T K ρ).restrict U =
      intervalOccupationMeasure σ T K ρ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact intervalOccupationMeasure_compl_region σ T hT hJ K ρ)
  have hdomU : intervalOccupationMeasure σ T K ρ ≤
      (volume.restrict U).withDensity (fun p => ENNReal.ofReal (gw p)) := by
    have h := Measure.restrict_mono_measure hdom U
    rw [hνU, restrict_withDensity hU, Measure.restrict_restrict_of_subset
      (show U ⊆ Ioo 0 T ×ˢ univ from prod_mono Subset.rfl (subset_univ _))] at h
    exact h
  have := intervalOccupationMeasure_finite σ T hT K ρ
  obtain ⟨g, hgm, hg0, _hgi, hgle, hpair⟩ := exists_real_density_of_le_withDensity
    (volume.restrict U) (intervalOccupationMeasure σ T K ρ) gw hgw.1 hgw.2.1 hdomU
  refine ⟨g, hgm, hg0, ?_, ?_⟩
  · intro φ
    rw [hpair φ]
    obtain ⟨M, _, hM⟩ := φ.exists_bound
    rw [integral_intervalOccupationMeasure σ T hT K ρ φ φ.measurable ⟨M, hM⟩]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun v => ?_
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun t => ?_
    dsimp only
    rw [interval_firstMarginal_eq_parabolic hJ K B hp σ (σ + t.1)
      (le_add_of_nonneg_right t.2.1.le) v.1 0]
  · intro γ hγ1 hγ2
    have hw := hgwLp γ hγ1 (by norm_num; exact hγ2)
    have hmeasure : volume.restrict U ≤ volume.restrict (Ioo 0 T ×ˢ univ) :=
      Measure.restrict_mono_set _ (prod_mono Subset.rfl (subset_univ _))
    have hnorm : ∀ᵐ p ∂volume.restrict U, ‖g p‖ ≤ ‖gw p‖ := by
      filter_upwards [hgle] with p hp
      simpa only [Real.norm_of_nonneg (hg0 p), Real.norm_of_nonneg (hgw.2.1 p)] using hp
    have hgLp := (hw.1.mono_measure hmeasure).mono hgm.aestronglyMeasurable hnorm
    refine ⟨hgLp, ?_⟩
    have hle : eLpNorm g (ENNReal.ofReal γ) (volume.restrict U) ≤
        eLpNorm gw (ENNReal.ofReal γ) (volume.restrict (Ioo 0 T ×ˢ univ)) :=
      (eLpNorm_mono_ae hgm.aestronglyMeasurable hnorm).trans
        (eLpNorm_mono_measure gw hmeasure)
    have hbound : eLpNorm gw (ENNReal.ofReal γ)
        (volume.restrict (Ioo 0 T ×ˢ univ)) ≤
        ENNReal.ofReal (C γ * (ρ univ).toReal * T ^ (3 / (2 * γ) - 1 / 2)) := by
      apply (ENNReal.toReal_le_toReal hw.1.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
      have hpos : 0 ≤ C γ * (ρ univ).toReal * T ^ (3 / (2 * γ) - 1 / 2) := by
        exact mul_nonneg (mul_nonneg (hC γ hγ1 (by norm_num; exact hγ2))
          ENNReal.toReal_nonneg) (Real.rpow_nonneg hT.le _)
      rw [ENNReal.toReal_ofReal hpos]
      have hm : (ρ.map Subtype.val) univ = ρ univ :=
        Measure.map_apply measurable_subtype_coe MeasurableSet.univ |>.trans (by
          rw [preimage_univ])
      simpa only [occupationLpNorm, occupationBeta, Nat.cast_one, hm,
        show (1 : ℝ) + 2 = 3 from by norm_num] using hw.2
    apply hle.trans
    convert hbound using 1
    rw [ENNReal.ofReal_mul (mul_nonneg (hC γ hγ1 (by norm_num; exact hγ2))
      ENNReal.toReal_nonneg), ENNReal.ofReal_mul (hC γ hγ1 (by norm_num; exact hγ2)),
      ENNReal.ofReal_toReal (measure_ne_top ρ univ)]

end

/-- Real bounds for the two factors imply a real product bound for composition. -/
theorem interval_composition_real_bound {a c F G : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hhead : TV (intervalFourierKernel K σ r hσr ξ v) ≤ F)
    (htail : ∀ w : PDE.oneDimensionalAxisBox a c,
      TV (intervalFourierKernel K r τ hrτ ξ w) ≤ G) :
    TV (intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤ F * G := by
  have hfinite : ∀ s t hst w,
      totalVariationNorm (intervalFourierKernel K s t hst ξ w) ≠ ⊤ :=
    fun s t hst w => ne_of_lt
      ((intervalFourierKernel_totalVariation_le_one K s t hst ξ w).trans_lt
        ENNReal.one_lt_top)
  have hhead' : totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) ≤
      ENNReal.ofReal F := by
    rw [← ENNReal.ofReal_toReal (hfinite σ r hσr v)]
    exact ENNReal.ofReal_le_ofReal hhead
  have htail' : (⨆ w : PDE.oneDimensionalAxisBox a c,
      totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w)) ≤ ENNReal.ofReal G := by
    apply iSup_le
    intro w
    rw [← ENNReal.ofReal_toReal (hfinite r τ hrτ w)]
    exact ENNReal.ofReal_le_ofReal (htail w)
  have h := (intervalFourierKernel_totalVariation_composition K hJ hcomp hcov
    σ r τ hσr hrτ ξ v).trans (mul_le_mul' hhead' htail')
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hF,
    ENNReal.toReal_ofReal hG] using ht

/-- The case-I decay estimate, conditional only on Hörmander's theorem and Lieberman's Theorem 5.14.
-/
theorem interval_fourier_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (v ξ : PDE.Vec 1)
      (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
      (ν : ComplexMeasure (PDE.Vec 1)),
      IsFourierProjection K (movingQuery σ τ hστ v 0 hv) ξ ν →
      TV ν ≤ C * Real.exp (-k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)))  := by
  have interval_frequency_decay :
      ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
      (v : PDE.oneDimensionalAxisBox a c),
      TV (intervalFourierKernel K σ τ hστ ξ v) ≤
        C * Real.exp (-k * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
    have interval_frequency_blocks :
        ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
        ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
        SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
        ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
        (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
        (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
        RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
          (zIndependentCoefficient B) b S K →
        ∀ (ξ : PDE.Vec 1), ξ ≠ 0 → ∀ (σ : ℝ) (v : PDE.oneDimensionalAxisBox a c),
        ∀ (ht : σ ≤ σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))),
        TV (intervalFourierKernel K σ
          (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v) ≤ 1 - δ := open HypoellipticAleksandrov.KineticAleksandrov.Scaling in by
      have unit_frequency_block_interval :
          ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
          ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
          SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
          ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
          (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
          (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
          RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
            (zIndependentCoefficient B) b S K →
          ∀ (ξ : PDE.Vec 1), PDE.vecNormSq ξ = 1 →
          ∀ (σ : ℝ) (v : PDE.Vec 1)
          (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
          (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec 1)),
          IsFourierProjection K (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ := by
        have interval_interior_block :
            ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
            ∀ (a c : ℝ) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
            SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
            ∀ (hD : MeasurableSet (PDE.oneDimensionalAxisBox a c))
            (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
            (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
            RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hD
              (zIndependentCoefficient B) b S K →
            IsDomainMonotoneEvolution (PDE.oneDimensionalAxisBox a c) stationary
              (zIndependentCoefficient B) b K →
            HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hD
              (zIndependentCoefficient B) K →
            ∀ (ξ : PDE.Vec 1), PDE.vecNormSq ξ = 1 →
            ∀ (σ : ℝ) (v : PDE.Vec 1)
            (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ),
            PDE.euclideanBall v (blockOuter Lb) ⊆ PDE.oneDimensionalAxisBox a c →
            ∀ (hL : σ ≤ σ + blockTime m Lb) (ν : ComplexMeasure (PDE.Vec 1)),
            IsFourierProjection K (movingQuery σ (σ + blockTime m Lb) hL v 0 hv) ξ ν →
            TV ν ≤ 1 - δ := by
          let hEvol := exists_terminalEvolution_of_classical hLE hH
          have hd : 1 ≤ 1 := by norm_num
          have hLb : 0 < Lb := hm.trans_le hmLb
          obtain ⟨Cstar, hC, hcorr⟩ := corridors_retained_dominated 1 hd lam Lam hlam hlamLam
          obtain ⟨h, q0, hh, hq0, hcommon⟩ :=
            continued_common_minorant_trimming 1 hd lam Lam hlam hlamLam
          let δ0 := (3 / 4) * blockMass Cstar m Lb * h * q0
          have hδ0 : 0 < δ0 := by
            exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 4)
              (Real.exp_pos _)) hh) hq0
          let δ := min δ0 (1 / 2)
          have hδ : 0 < δ := lt_min hδ0 (by norm_num)
          have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
          refine ⟨δ, hδ, hδ1, ?_⟩
          intro a c B b hsetting hD S K hreal hmono hpar ξ hξ σ v hv hfit hL ν hν
          let J := PDE.oneDimensionalAxisBox a c
          let ρ := blockRho Lb
          let η := blockEta m Lb
          let s := σ + blockL0 m
          let T := σ + blockTime m Lb
          let Ω := PDE.euclideanBall v (4 * ρ)
          have hρ : 0 < ρ := blockRho_pos hLb
          have hη : 0 < η := blockEta_pos hm hLb
          have hηρ : η < ρ := blockEta_lt_rho hLb
          have hστ : σ ≤ s := le_add_of_nonneg_right (blockL0_pos hm).le
          have hsT : s ≤ T := by
            dsimp only [s, T, blockTime]
            nlinarith only [sq_nonneg ρ]
          have hsmallfit : Ω ⊆ J :=
            (PDE.euclideanBall_mono (by positivity : 0 ≤ 4 * ρ)
              (by dsimp [blockOuter]; linarith : 4 * ρ ≤ blockOuter Lb)).trans hfit
          have hvJ : v ∈ J := by simpa only [movingDomain_stationary] using hv
          obtain ⟨α, -, -, hpaths⟩ := exists_opposite_paths m Lb σ hm hmLb
            J b hsetting.2.1 hsetting.2.2.2.2.1 ξ v hξ hfit
          let γ1 : ℝ → PDE.Vec 1 := fun _ => v
          let γ2 : ℝ → PDE.Vec 1 := fun r =>
            v + (α * tent (blockL0 m) (max 0 (min (blockL0 m) (r - σ)))) • ξ
          obtain ⟨hγ1, hγ2, hstart1, hstart2, hend1, hend2,
            hspeed1, hspeed2, htube, hphase⟩ := hpaths
          change γ1 σ = v at hstart1
          change γ2 σ = v at hstart2
          have hadm : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec 1) η) :=
            Or.inr (Or.inl ⟨0, η, hη, rfl⟩)
          have hΩadm : IsAdmissibleEvolutionDomain Ω :=
            Or.inr (Or.inl ⟨v, 4 * ρ, mul_pos (by norm_num) hρ, rfl⟩)
          obtain ⟨S1, K1, hreal1, -, hpar1, -⟩ :=
            exists_unitBlock_evolution hEvol hd lam Lam m Lb J B b hsetting _ γ1 hadm hγ1
          obtain ⟨S2, K2, hreal2, -, hpar2, -⟩ :=
            exists_unitBlock_evolution hEvol hd lam Lam m Lb J B b hsetting _ γ2 hadm hγ2
          obtain ⟨S0, K0, hreal0, hmono0, hpar0, -⟩ :=
            exists_unitBlock_evolution hEvol hd lam Lam m Lb J B b hsetting Ω stationary
              hΩadm (zeroCurve_piecewiseC1 1)
          have hv1 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ1 σ := by
            rw [mem_movingDomain_euclideanBall_iff, hstart1]
            simp [PDE.vecNormSq, PDE.vecDot]
            exact sq_pos_of_pos hη
          have hv2 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ2 σ := by
            rw [mem_movingDomain_euclideanBall_iff, hstart2]
            simp [PDE.vecNormSq, PDE.vecDot]
            exact sq_pos_of_pos hη
          let q1 := movingQuery σ s hστ v 0 hv1
          let q2 := movingQuery σ s hστ v 0 hv2
          let qD := movingQuery σ s hστ v 0 hv
          let qT := movingQuery σ T hL v 0 hv
          obtain ⟨-, -, -, -, hsupp1, hsupp2, hmass1, hmass2, hdom⟩ :=
            hcorr m Lb σ J B b hsetting S K hD hreal hmono γ1 γ2 v 0
              hγ1 hγ2 hstart1 hstart2 hend1 hend2 hspeed1 hspeed2
              (fun r => (htube r).1) (fun r => (htube r).2)
              S1 K1 S2 K2 hreal1 hreal2 hpar1 hpar2 q1 q2 qD rfl rfl rfl
          let μ1 := K1.master q1
          let μ2 := K2.master q2
          have hfμ1 : IsFiniteMeasure μ1 := ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
          have hfμ2 : IsFiniteMeasure μ2 := ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
          let N1 := ENNReal.ofReal (blockMass Cstar m Lb / (2 * μ1.real univ)) • μ1
          let N2 := ENNReal.ofReal (blockMass Cstar m Lb / (2 * μ2.real univ)) • μ2
          have hfN1 : IsFiniteMeasure N1 := by
            refine ⟨?_⟩
            rw [Measure.smul_apply, smul_eq_mul]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ1 univ)
          have hfN2 : IsFiniteMeasure N2 := by
            refine ⟨?_⟩
            rw [Measure.smul_apply, smul_eq_mul]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ2 univ)
          have hN1supp : N1 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
            rw [Measure.smul_apply, hsupp1, smul_zero]
          have hN2supp : N2 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
            rw [Measure.smul_apply, hsupp2, smul_zero]
          let R1 := N1.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState 1)
          let R2 := N2.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState 1)
          have hη4ρ : η ≤ 4 * ρ := by linarith only [hηρ, hρ]
          obtain ⟨hR1, hmR1, hsupport1⟩ := retained_ball_comap_properties v η (4 * ρ) s
            hη.le hη4ρ N1 hN1supp
          obtain ⟨hR2, hmR2, hsupport2⟩ := retained_ball_comap_properties v η (4 * ρ) s
            hη.le hη4ρ N2 hN2supp
          have hfR1 : IsFiniteMeasure R1 := inferInstance
          have hfR2 : IsFiniteMeasure R2 := inferInstance
          let E1 := continuedMeasure K0 hsT R1
          let E2 := continuedMeasure K0 hsT R2
          have hE1 : ∀ A, MeasurableSet A → E1 A =
              ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1 :=
            fun A hA => continuedMeasure_apply K0 hsT R1 hA
          have hE2 : ∀ A, MeasurableSet A → E2 A =
              ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2 :=
            fun A hA => continuedMeasure_apply K0 hsT R2 hA
          let M := K.master qT
          have hfM : IsFiniteMeasure M := ⟨(K.mass_le_one qT).trans_lt ENNReal.one_lt_top⟩
          have hcontinued : E1 + E2 ≤ M := by
            apply continued_measures_dominated J Ω hD (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet
              B b S K S0 K0 hreal hreal0 hmono hΩadm hsmallfit σ s T hστ hsT qD qT
              ⟨rfl, rfl⟩ rfl R1 R2 _ E1 E2 hE1 hE2
            rw [hR1, hR2]
            exact hdom
          have hs : s = T - 4 * ρ ^ 2 := by dsimp only [s, T, blockTime]; ring
          have ha : 0 < blockMass Cstar m Lb / 2 := div_pos (Real.exp_pos _) (by norm_num)
          have hvΩ : v ∈ movingDomain Ω stationary (T - ρ ^ 2) := by
            rw [movingDomain_stationary]
            change PDE.vecNormSq (v - v) < (4 * ρ) ^ 2
            simpa [PDE.vecNormSq, PDE.vecDot] using sq_pos_of_pos (mul_pos (by norm_num) hρ)
          let qlate := scalarQuery (T - ρ ^ 2) T (sub_le_self _ (sq_nonneg ρ)) v hvΩ
          obtain ⟨-, -, hfloor, F1, F2, hF1, hF2, hFsum, hmap1, hmap2⟩ :=
            hcommon m Lb J B b hsetting v ρ T hvJ hρ hsmallfit
              S0 K0 hreal0 hpar0 hmono0 s (blockMass Cstar m Lb / 2) η hs hsT ha hη hηρ
              R1 R2 hfR1 hfR2 (hmR1.trans hmass1) (hmR2.trans hmass2) hsupport1 hsupport2
              E1 E2 M hfM hE1 hE2 hcontinued qlate rfl
          let Θ := ENNReal.ofReal (blockMass Cstar m Lb / 2 * h) •
            P K0 (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet qlate
          have hfE1 : IsFiniteMeasure E1 := inferInstance
          have hfE2 : IsFiniteMeasure E2 := inferInstance
          have hfF1 : IsFiniteMeasure F1 := isFiniteMeasure_of_le _ hF1
          have hfF2 : IsFiniteMeasure F2 := isFiniteMeasure_of_le _ hF2
          obtain ⟨hΦ, -, -, hf1, hf2⟩ := block_continued_phase_error hd lam Lam m Lb Cstar σ
            J B b hsetting hC ξ v 0 hξ hfit γ1 γ2 hγ1 hγ2 hstart1 hstart2 hend1 hend2
            (fun r => (htube r).1) (fun r => (htube r).2) hphase
            S1 K1 S2 K2 S0 K0 hreal1 hreal2 hreal0 hpar1 hpar2 hpar0 q1 q2 rfl rfl
            R1 R2 hR1 hR2 hsT E1 E2 F1 F2 hE1 hE2 hF1 hF2
          have hMone : M.real univ ≤ 1 := by
            simpa only [measureReal_def, ENNReal.toReal_one] using
              ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one qT)
          have hmass : blockMass Cstar m Lb * h * q0 / 2 ≤ Θ.real univ := by
            convert hfloor using 1
            ring
          have hphaseν : IsPhaseProjection (phaseCoordinate ξ 0) M ν := by
            intro A hA
            exact hν A hA
          have hcancel := (block_interior_cancellation ξ 0 M F1 F2 Θ (blockMass Cstar m Lb)
            h q0 _ _ hMone hFsum hmap1 hmap2 hmass hΦ hf1 hf2 ν hphaseν).2
          exact hcancel.trans (sub_le_sub_left (min_le_left δ0 (1 / 2)) 1)
        obtain ⟨δ₁, hδ₁, hδ₁one, hi⟩ := interval_interior_block
        have ht : 0 < blockTime m Lb := by
          unfold blockTime
          have h := blockL0_pos hm
          positivity
        have hR : 0 < blockOuter Lb := by
          unfold blockOuter
          have h := blockRho_pos (hm.trans_le hmLb)
          positivity
        let δ₂ := 1 - intervalHeat lam (blockTime m Lb) (blockOuter Lb)
        have hδ₂ : 0 < δ₂ := sub_pos.mpr (intervalErf_lt_one (by
          exact div_nonneg hR.le (by positivity)))
        let δ := min δ₁ (min δ₂ (1 / 2))
        refine ⟨blockTime m Lb, δ, ht, lt_min hδ₁ (lt_min hδ₂ (by norm_num)),
          (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num)), ?_⟩
        intro a c hac B b hs hJ S K hr ξ hξ σ v hv hL ν hν
        obtain ⟨hmono, hpar, _hcov⟩ := interval_evolution_clauses hH hLE hac B b hs hJ S K hr
        by_cases hfit : PDE.euclideanBall v (blockOuter Lb) ⊆ PDE.oneDimensionalAxisBox a c
        · exact (hi a c B b hs hJ S K hr hmono hpar ξ hξ σ v hv hfit hL ν hν).trans
            (sub_le_sub_left (min_le_left _ _) 1)
        · have hb : min (v 0 - a) (c - v 0) ≤ blockOuter Lb := by
            by_contra hn
            exact hfit (interval_ball_subset_of_distance hR v (lt_of_not_ge hn))
          have hbound := interval_boundary_block hH hLE hac B b hs hJ S K hr
            σ v hv hb ξ hL ν hν
          have hδle : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
          dsimp only [δ₂] at hδle
          linarith
      obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ := unit_frequency_block_interval
      refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
      intro a c hac B b hs hJ S K hr ξ hξ σ v ht
      obtain ⟨hrpos, hr2, hrunit⟩ := frequency_radius_identities hξ
      let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ)), hrpos⟩
      let D := scaledDomain (PDE.oneDimensionalAxisBox a c) v.1 r
      let hmap := mapsDomain_interval a c σ v.1 0 b r
      let hDr := measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible hac v.1 r)
      let K' := KineticAffineScaling.pushKernel hmap K
      let S' := fiberOperator K' hDr
      have hr' := realizes_ofRadius_interval a c σ hac v.1 0 b r hr
      have hs' := scaled_interval_setting lam Lam m Lb a c σ hac B b hs v.1 r
      have hv' : 0 ∈ movingDomain D stationary 0 := by
        rw [movingDomain_stationary]
        change v.1 + r.1 • 0 ∈ PDE.oneDimensionalAxisBox a c
        simpa using v.2
      let q' := movingQuery 0 L hL.le 0 0 hv'
      let ν' := fourierProjection K' q' (r.1 ^ 3 • ξ)
      have hν' := fourierProjection_spec K' q' (r.1 ^ 3 • ξ)
      have hunit' := hunit ((a - v.1 0) / r.1) ((c - v.1 0) / r.1)
        (scaled_interval_endpoints hac v.1 r) (scaledCoefficient B σ v.1 r) (scaledDrift b v.1 r)
      rw [← scaledDomain_interval a c v.1 r] at hunit'
      have hνunit : IsFourierProjection K' (movingQuery 0 (0 + L)
          (by simpa using hL.le) 0 0 hv') (r.1 ^ 3 • ξ) ν' := by
        simpa using hν'
      have hbound := hunit' hs' hDr S' K' hr' (r.1 ^ 3 • ξ) hrunit
        0 0 hv' (by simpa using hL.le) ν' hνunit
      let ν := intervalFourierKernel K σ
        (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v
      have hquery : KineticAffineScaling.queryMap hmap q' =
          movingQuery σ (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht v.1 0
            (by simpa only [movingDomain_stationary] using v.2) := by
        apply Subtype.ext
        change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
          v.1 + r.1 • 0, 0 +
            (r.1 ^ 2 * 0) • b v.1 + r.1 ^ 3 • 0) = _
        change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
          v.1 + r.1 • 0, 0 +
            (r.1 ^ 2 * 0) • b v.1 + r.1 ^ 3 • 0) =
          (σ, σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)), v.1, 0)
        simp
        have hr2' : r.1 ^ 2 = PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)) := hr2
        rw [hr2', mul_comm L]
      have hν : IsFourierProjection K (KineticAffineScaling.queryMap hmap q') ξ ν := by
        rw [hquery]
        exact intervalFourierKernel_spec K _ _ ht ξ v
      have htv := (realizes_ofRadius_interval_fourier_tv a c σ hac v.1 0 b r hr hr'
        q' ξ ν ν' hν hν').2
      change (totalVariationNorm ν).toReal ≤ 1 - δ
      rw [htv]
      exact hbound
    obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ := interval_frequency_blocks
    have hq : 0 < 1 - δ := sub_pos.mpr hδ1
    obtain ⟨hC, hk⟩ := decay_constants hδ hδ1 hL
    refine ⟨(1 - δ)⁻¹, -Real.log (1 - δ) / L, zero_lt_one.trans_le hC, hk, ?_⟩
    intro a c hac B b hs hJ S K hr σ τ hστ ξ v
    by_cases hξ : ξ = 0
    · subst ξ
      have htv := intervalFourierKernel_totalVariation_le_one K σ τ hστ 0 v
      have hr := ENNReal.toReal_mono ENNReal.one_ne_top htv
      simp only [ENNReal.toReal_one] at hr
      simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Real.sqrt_zero, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), Real.exp_zero] using hr.trans hC
    · have hN := frequency_norm_pos hξ
      let N := PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
      have hNp : 0 < N := Real.rpow_pos_of_pos hN _
      let T := L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))
      have hTdef : T = L / N := by
        dsimp [T, N]
        rw [Real.rpow_neg hN.le]
        rfl
      have hT : 0 < T := by rw [hTdef]; exact div_pos hL hNp
      have hc := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
      have hb := interval_exponential_of_blocks K hJ hr.2.2.2 hc hT hq
        (by linarith only [hδ] : 1 - δ ≤ 1) ξ
        (fun s w => hsteps a c hac B b hs hJ S K hr ξ hξ s w
          (le_add_of_nonneg_right hT.le)) σ τ hστ v
      have he : -(-Real.log (1 - δ) / T) * (τ - σ) =
          -(-Real.log (1 - δ) / L) * (τ - σ) * N := by
        rw [hTdef]
        field_simp
      rw [he] at hb
      exact hb
  obtain ⟨C₁, k₁, hC₁, hk₁, hfreq⟩ := interval_frequency_decay
  obtain ⟨C₂, k₂, hC₂, hk₂, hkill⟩ := interval_fourier_killing_decay
    hH hLE lam Lam m Lb length hlam hlength
  let k := min k₁ k₂ / 2
  have hk : 0 < k := div_pos (lt_min hk₁ hk₂) (by norm_num)
  refine ⟨C₁ * C₂, k, mul_pos hC₁ hC₂, hk, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ τ hστ v ξ hv ν hν
  let w : PDE.oneDimensionalAxisBox a c :=
    ⟨v, by simpa only [movingDomain_stationary] using hv⟩
  have heq : ν = intervalFourierKernel K σ τ hστ ξ w := by
    apply VectorMeasure.ext
    intro E hE
    exact (hν E hE).trans ((intervalFourierKernel_spec K σ τ hστ ξ w E hE).symm)
  rw [heq]
  let r := (σ + τ) / 2
  have hσr : σ ≤ r := by dsimp [r]; linarith only [hστ]
  have hrτ : r ≤ τ := by dsimp [r]; linarith only [hστ]
  have hc := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
  have hb := interval_composition_real_bound K hJ hr.2.2.2 hc σ r τ hσr hrτ ξ w
    (mul_pos hC₁ (Real.exp_pos _)).le (mul_pos hC₂ (Real.exp_pos _)).le
    (hfreq a c hac B b hs hJ S K hr σ r hσr ξ w)
    (fun w' => hkill a c hac B b hs hJ S K hr hlen r τ hrτ ξ w')
  have hexp : -k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) +
      -k₂ * (τ - r) ≤ -k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
    have hN : 0 ≤ PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) := Real.rpow_nonneg
      (by unfold PDE.vecEuclideanNorm; exact Real.sqrt_nonneg _) _
    have htime : 0 ≤ τ - σ := sub_nonneg.mpr hστ
    have h1 := mul_le_mul_of_nonneg_right (min_le_left k₁ k₂)
      (mul_nonneg htime hN)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right k₁ k₂) htime
    dsimp only [r, k]
    nlinarith only [h1, h2]
  have hmul :
      (C₁ * Real.exp (-k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) *
        (C₂ * Real.exp (-k₂ * (τ - r))) =
      (C₁ * C₂) * Real.exp (-k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) +
        -k₂ * (τ - r)) := by rw [Real.exp_add]; ring
  rw [hmul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (mul_pos hC₁ hC₂).le)


/-- The whole-space carrier used by the adapter is measurable. -/
theorem intervalWholeSpace_measurable : MeasurableSet (wholeSpace 1) := MeasurableSet.univ

/-- Include a literal interval query in the stationary whole-space query carrier. -/
def intervalQueryInclusion {a c : ℝ} :
    EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary →
      EvolutionQuery (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) :=
  fun q => ⟨q.1, q.2.1, by rw [movingDomain_wholeSpace]; trivial, q.2.2.2⟩

/-- Inclusion of interval queries is a measurable embedding. -/
theorem intervalQueryInclusion_measurableEmbedding {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) :
    MeasurableEmbedding (intervalQueryInclusion (a := a) (c := c)) := by
  have hq : MeasurableSet {q : RawEvolutionQuery 1 |
      q.1 ≤ q.2.1 ∧ q.2.2.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c)
        stationary q.1 ∧ q.2.2.2 ∈ (univ : Set (PDE.Vec 1))} := by
    simp only [movingDomain_stationary, mem_univ, and_true]
    exact (measurableSet_le
      (show Measurable (fun q => q.1) from by fun_prop)
      (show Measurable (fun q => q.2.1) from by fun_prop)).inter
      (hJ.preimage (show Measurable (fun q : RawEvolutionQuery 1 => q.2.2.1) from
        by fun_prop))
  have he := MeasurableEmbedding.subtype_coe hq
  refine ⟨?_, ?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    exact congrArg (fun r : EvolutionQuery (wholeSpace 1)
      (fun _ => 0) => r.1) hpq
  · apply Measurable.subtype_mk
    exact measurable_subtype_coe
  · intro A hA
    have him : MeasurableSet (Subtype.val '' A) := he.measurableSet_image.2 hA
    have heq : intervalQueryInclusion '' A =
        (Subtype.val : EvolutionQuery (wholeSpace 1) (fun _ => 0) →
          RawEvolutionQuery 1) ⁻¹' (Subtype.val '' A) := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, he⟩
        exact ⟨p, hp, Subtype.ext he⟩
    rw [heq]
    exact him.preimage measurable_subtype_coe

/-- Zero-extended master kernel, with the same ambient terminal state measure. -/
def intervalExtensionMaster {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary) :
    ProbabilityTheory.Kernel
      (EvolutionQuery (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))) (EvolutionAmbientState 1) where
  toFun := Function.extend intervalQueryInclusion K.master (fun _ => 0)
  measurable' := (intervalQueryInclusion_measurableEmbedding hJ).measurable_extend
    K.master.measurable measurable_const

/-- The zero extension agrees exactly with the interval master at interior queries. -/
theorem intervalExtensionMaster_inside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (q : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary) :
    intervalExtensionMaster hJ K (intervalQueryInclusion q) = K.master q := by
  change Function.extend intervalQueryInclusion K.master (fun _ => 0)
    (intervalQueryInclusion q) = K.master q
  exact (intervalQueryInclusion_measurableEmbedding hJ).injective.extend_apply _ _ q

/-- The adapted kernel has whole-space carriers and zero transitions outside the interval. -/
def intervalExtension {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary) :
    MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) where
  master := intervalExtensionMaster hJ K
  terminal_support := by
    intro q
    simp only [evolutionStateSet, movingDomain_wholeSpace, univ_prod_univ,
      Measure.restrict_univ]
  mass_le_one := by
    intro q
    by_cases hq : ∃ p : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary,
      intervalQueryInclusion p = q
    · obtain ⟨p, rfl⟩ := hq
      rw [intervalExtensionMaster_inside]
      exact K.mass_le_one p
    · change (Function.extend intervalQueryInclusion K.master (fun _ => 0) q) univ ≤ 1
      rw [Function.extend_apply' _ _ _ hq]
      exact zero_le


/-- Include an interval state in the whole-space fiber at the same time. -/
def intervalStateInclusion {a c : ℝ} (σ : ℝ) :
    EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ →
      EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ :=
  fun p => ⟨p.1, by rw [evolutionStateSet, movingDomain_wholeSpace]; trivial⟩

/-- The fixed-time state inclusion is measurable. -/
theorem measurable_intervalStateInclusion {a c : ℝ} (σ : ℝ) :
    Measurable (intervalStateInclusion (a := a) (c := c) σ) :=
  measurable_subtype_coe.subtype_mk

/-- Exterior queries have zero master measure under the extension. -/
theorem intervalExtensionMaster_outside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (q : EvolutionQuery (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hq : q.1.2.2.1 ∉ PDE.oneDimensionalAxisBox a c) :
    intervalExtensionMaster hJ K q = 0 := by
  change Function.extend intervalQueryInclusion K.master (fun _ => 0) q = 0
  apply Function.extend_apply'
  rintro ⟨p, hp⟩
  have he : p.1 = q.1 := congrArg Subtype.val hp
  apply hq
  rw [← he]
  simpa only [movingDomain_stationary] using p.2.2.1

/-- Interior extended fibers are literal pushforwards of the original interval fibers. -/
theorem intervalExtension_fiber_inside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable σ τ hστ
      (intervalStateInclusion σ p) =
      (K.fiberKernel hJ σ τ hστ p).map (intervalStateInclusion τ) := by
  apply (MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet intervalWholeSpace_measurable τ)).map_injective
  rw [(intervalExtension hJ K).map_fiberKernel_eq_master intervalWholeSpace_measurable,
    Measure.map_map measurable_subtype_coe (measurable_intervalStateInclusion τ)]
  change intervalExtensionMaster hJ K
    (intervalQueryInclusion (evolutionQueryOfState (PDE.oneDimensionalAxisBox a c)
      stationary σ τ hστ p)) =
    (K.fiberKernel hJ σ τ hστ p).map Subtype.val
  rw [intervalExtensionMaster_inside, K.map_fiberKernel_eq_master]

/-- Starting outside the interval gives the zero fixed-time fiber. -/
theorem intervalExtension_fiber_outside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (p : EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ)
    (hp : p.1.1 ∉ PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable σ τ hστ p = 0 := by
  rw [MovingFiberKernel.fiberKernel_apply]
  change Measure.comap Subtype.val (intervalExtensionMaster hJ K
    (evolutionQueryOfState (wholeSpace 1) (fun _ => 0) σ τ hστ p)) = 0
  rw [intervalExtensionMaster_outside hJ K _ hp, Measure.comap_zero]


/-- Zero extension preserves the composition law of the interval kernel. -/
theorem intervalExtension_composition {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hcomp : K.HasComposition hJ) :
    (intervalExtension hJ K).HasComposition intervalWholeSpace_measurable := by
  intro σ r τ hσr hrτ
  apply ProbabilityTheory.Kernel.ext
  intro p
  apply Measure.ext
  intro A hA
  by_cases hp : p.1.1 ∈ PDE.oneDimensionalAxisBox a c
  · let pj : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
      ⟨p.1, by simpa only [evolutionStateSet, mem_prod, movingDomain_stationary,
        mem_univ, and_true] using hp⟩
    have he : intervalStateInclusion σ pj = p := Subtype.ext rfl
    rw [← he, intervalExtension_fiber_inside,
      Measure.map_apply (measurable_intervalStateInclusion τ) hA,
      hcomp σ r τ hσr hrτ,
      ProbabilityTheory.Kernel.comp_apply' _ _ _
        (hA.preimage (measurable_intervalStateInclusion τ)),
      ProbabilityTheory.Kernel.comp_apply' _ _ _ hA,
      intervalExtension_fiber_inside,
      lintegral_map
        (((intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable r τ
          hrτ).measurable_coe hA)
        (measurable_intervalStateInclusion r)]
    apply lintegral_congr_ae
    refine Filter.Eventually.of_forall fun w => ?_
    dsimp only
    rw [intervalExtension_fiber_inside,
      Measure.map_apply (measurable_intervalStateInclusion τ) hA]
  · rw [intervalExtension_fiber_outside hJ K σ τ (hσr.trans hrτ) p hp,
      ProbabilityTheory.Kernel.comp_apply' _ _ _ hA,
      intervalExtension_fiber_outside hJ K σ r hσr p hp]
    simp only [Measure.coe_zero, Pi.zero_apply, lintegral_zero_measure]


/-- Inclusion of interval states commutes with position translation. -/
theorem intervalStateInclusion_shift {a c : ℝ} (σ : ℝ) (z : PDE.Vec 1)
    (p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ) :
    evolutionStateShift (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ z
      (intervalStateInclusion σ p) =
      intervalStateInclusion σ
        (evolutionStateShift (PDE.oneDimensionalAxisBox a c) stationary σ z p) := rfl

/-- Literal zero extension preserves position-translation covariance. -/
theorem intervalExtension_covariance {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hc : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c)
      stationary hJ K) :
    IsTranslationCovariantEvolution (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
      intervalWholeSpace_measurable (intervalExtension hJ K) := by
  intro σ τ hστ z p
  by_cases hp : p.1.1 ∈ PDE.oneDimensionalAxisBox a c
  · let pj : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
      ⟨p.1, by simpa only [evolutionStateSet, mem_prod, movingDomain_stationary,
        mem_univ, and_true] using hp⟩
    have he : intervalStateInclusion σ pj = p := Subtype.ext rfl
    rw [← he, intervalStateInclusion_shift, intervalExtension_fiber_inside,
      intervalExtension_fiber_inside,
      Measure.map_map (measurable_evolutionStateShift _ _ τ z)
        (measurable_intervalStateInclusion τ),
      ← hc σ τ hστ z pj,
      Measure.map_map (measurable_intervalStateInclusion τ)
        (measurable_evolutionStateShift _ _ τ z)]
    rfl
  · have hs : (evolutionStateShift (wholeSpace 1) (fun _ => 0) σ z p).1.1
        ∉ PDE.oneDimensionalAxisBox a c := hp
    rw [intervalExtension_fiber_outside hJ K σ τ hστ p hp,
      intervalExtension_fiber_outside hJ K σ τ hστ _ hs, Measure.map_zero]


/-- Whole-space scalar queries inside the interval recover the original first marginal. -/
theorem intervalExtension_first_inside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).firstMarginal (wholeSpaceQuery σ τ hστ v.1 0) =
      K.firstMarginal (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2)) := by
  unfold MovingFiberKernel.firstMarginal
  rw [ProbabilityTheory.Kernel.fst_apply, ProbabilityTheory.Kernel.fst_apply]
  congr 1
  change intervalExtensionMaster hJ K (intervalQueryInclusion
    (movingQuery σ τ hστ v.1 0
      (by simpa only [movingDomain_stationary] using v.2))) = _
  exact intervalExtensionMaster_inside hJ K _

/-- Whole-space first marginals vanish when the starting velocity is exterior. -/
theorem intervalExtension_first_outside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.Vec 1)
    (hv : v ∉ PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).firstMarginal (wholeSpaceQuery σ τ hστ v 0) = 0 := by
  unfold MovingFiberKernel.firstMarginal
  rw [ProbabilityTheory.Kernel.fst_apply]
  change Measure.map Prod.fst (intervalExtensionMaster hJ K
    (wholeSpaceQuery σ τ hστ v 0)) = 0
  rw [intervalExtensionMaster_outside hJ K _ hv, Measure.map_zero]

/-- Pulling an ambient finite measure back to the actual interval cannot increase mass. -/
theorem intervalInitial_comap_mass_le {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (ρ : Measure (PDE.Vec 1)) :
    (Measure.comap (Subtype.val : PDE.oneDimensionalAxisBox a c → PDE.Vec 1) ρ) univ ≤
      ρ univ := by
  rw [(MeasurableEmbedding.subtype_coe hJ).comap_apply ρ univ]
  exact measure_mono (subset_univ _)

end HypoellipticAleksandrov.KineticAleksandrov.Interval

