module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap

/-!
# Reverse-time source as a Bochner curve

This module packages the negative reverse-time source as a literal Bochner
`L²` curve.  Its private construction clamps time into the closed source
cylinder, so the supplied local smoothness hypothesis is never used outside
its stated domain.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Infrastructure for the clamped reverse-time source curve. -/
def reverseTimeSourceClamp
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) : ℝ → Set.Icc 0 (r₁ - r₀) :=
  Set.projIcc 0 (r₁ - r₀) (le_of_lt (sub_pos.mpr h₀₁))

variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)

private theorem reverseTimeSourceClamp_mem
     (τ : ℝ) : type_of% ((reverseTimeSourceClamp r₀ r₁ h₀₁ τ).2) :=
  (reverseTimeSourceClamp r₀ r₁ h₀₁ τ).2

private theorem continuous_reverseTimeSourceClamp
     :
    Continuous fun τ  => (reverseTimeSourceClamp r₀ r₁ h₀₁ τ : ℝ) := continuous_subtype_val.comp continuous_projIcc

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (F : PDE.TimeScalarField d)

private theorem continuousOn_reverseTimeSourceUncurried


    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn
      (Function.uncurry fun τ y =>
        F (r₁ - (reverseTimeSourceClamp r₀ r₁ h₀₁ τ : ℝ)) y)
      (Set.univ ×ˢ closure Ω) := by

  rcases hFSmooth with ⟨V, hVOpen, hCylinder, hV⟩
  have hMapContinuous : Continuous (((fun z : ℝ × PDE.Vec d => (r₁ - (reverseTimeSourceClamp r₀ r₁ h₀₁ z.1 : ℝ), z.2)))) :=
    (continuous_const.sub
      ((continuous_reverseTimeSourceClamp r₀ r₁ h₀₁).comp continuous_fst)).prodMk
      continuous_snd

  exact (hV.continuousOn.mono hCylinder).comp hMapContinuous.continuousOn (by
      intro z hz
      rw [mem_scalarParabolicClosedCylinder_iff]
      constructor
      · linarith [(reverseTimeSourceClamp_mem r₀ r₁ h₀₁ z.1).2]
      constructor
      · linarith [(reverseTimeSourceClamp_mem r₀ r₁ h₀₁ z.1).1]
      · exact hz.2)

/-- Infrastructure for the clamped reverse-time source curve. -/
def reverseTimeSourceContinuousCurve

     : ℝ → C(closure Ω, ℝ) :=
  fun τ => ContinuousMap.mkD
    ((closure Ω).restrict (F (r₁ - (reverseTimeSourceClamp r₀ r₁ h₀₁ τ : ℝ))))
    0

private theorem continuous_reverseTimeSourceContinuousCurve

    [CompactSpace (closure Ω)]
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (F : PDE.TimeScalarField d)
  (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (reverseTimeSourceContinuousCurve (Ω := Ω) r₀ r₁ h₀₁ F) := ContinuousMap.continuous_mkD_restrict_of_uncurry
    _ _ (continuousOn_reverseTimeSourceUncurried r₀ r₁ h₀₁ F hFSmooth)

variable (f : C(closure Ω, ℝ))

/-- Infrastructure for the clamped reverse-time source curve. -/
def continuousOnClosureRaw

     : PDE.ScalarField d :=
  by
    classical
    exact fun y => if hy : y ∈ closure Ω then f ⟨y, hy⟩ else 0

private theorem continuousOn_continuousOnClosureRaw

     :
    ContinuousOn (continuousOnClosureRaw f) Ω := by
  rw [continuousOn_iff_continuous_restrict]

  refine (f.continuous.comp (Continuous.subtype_mk continuous_subtype_val fun y => subset_closure y.2)).congr ?_
  intro y
  simp [continuousOnClosureRaw, subset_closure y.2]

private theorem aestronglyMeasurable_continuousOnClosureRaw

    (hΩ : IsOpen Ω) (f : C(closure Ω, ℝ)) :
    AEStronglyMeasurable (continuousOnClosureRaw f) (PDE.volumeOn Ω) :=
  (continuousOn_continuousOnClosureRaw f).aestronglyMeasurable hΩ.measurableSet

/-- A bound used to construct the clamped source operator. -/
theorem memLp_continuousOnClosureRaw

    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (f : C(closure Ω, ℝ)) :
    MemLp (continuousOnClosureRaw f) (2 ) (PDE.volumeOn Ω) := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  letI : CompactSpace (closure Ω) :=
    isCompact_iff_compactSpace.mp hΩbounded.isCompact_closure
  refine MemLp.of_bound (aestronglyMeasurable_continuousOnClosureRaw hΩ f) ‖f‖ ?_
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
  rw [continuousOnClosureRaw, dif_pos (subset_closure hy)]
  exact f.norm_coe_le_norm ⟨y, subset_closure hy⟩

/-- Infrastructure for the clamped reverse-time source curve. -/
def continuousOnClosureToScalarLpLinear

    [CompactSpace (closure Ω)]
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) :
    C(closure Ω, ℝ) →ₗ[ℝ] PDE.ScalarLp Ω (2 ) where
  toFun f :=
    (memLp_continuousOnClosureRaw hΩ hΩbounded f).toLp
      (continuousOnClosureRaw f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      (memLp_continuousOnClosureRaw hΩ hΩbounded (f + g)).coeFn_toLp,
      (memLp_continuousOnClosureRaw hΩ hΩbounded f).coeFn_toLp,
      (memLp_continuousOnClosureRaw hΩ hΩbounded g).coeFn_toLp,
      Lp.coeFn_add
        ((memLp_continuousOnClosureRaw hΩ hΩbounded f).toLp
          (continuousOnClosureRaw f))
        ((memLp_continuousOnClosureRaw hΩ hΩbounded g).toLp
          (continuousOnClosureRaw g))]
      with y hfg hf hg hsum
    calc
      (memLp_continuousOnClosureRaw hΩ hΩbounded (f + g)).toLp
          _ y =
          continuousOnClosureRaw (f + g) y := hfg
      _ = continuousOnClosureRaw f y + continuousOnClosureRaw g y := by
        by_cases hy : y ∈ closure Ω <;>
          simp [continuousOnClosureRaw, hy]
      _ = ((memLp_continuousOnClosureRaw hΩ hΩbounded f).toLp
            (continuousOnClosureRaw f) +
          (memLp_continuousOnClosureRaw hΩ hΩbounded g).toLp
            (continuousOnClosureRaw g)) y := by
        rw [hsum]
        simp only [Pi.add_apply, hf, hg]
      _ = _ := rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      (memLp_continuousOnClosureRaw hΩ hΩbounded (c • f)).coeFn_toLp,
      (memLp_continuousOnClosureRaw hΩ hΩbounded f).coeFn_toLp,
      Lp.coeFn_smul c
        ((memLp_continuousOnClosureRaw hΩ hΩbounded f).toLp
          (continuousOnClosureRaw f))]
      with y hcf hf hsmul
    calc
      (memLp_continuousOnClosureRaw hΩ hΩbounded (c • f)).toLp
          _ y =
          continuousOnClosureRaw (c • f) y := hcf
      _ = c • continuousOnClosureRaw f y := by
        simp_all [continuousOnClosureRaw]
      _ = (c • (memLp_continuousOnClosureRaw hΩ hΩbounded f).toLp
          (continuousOnClosureRaw f)) y := by
        rw [hsmul]
        simp only [Pi.smul_apply, hf]
      _ = _ := rfl

/-- A bound used to construct the clamped source operator. -/
theorem norm_continuousOnClosureToScalarLpLinear_apply_le

    [CompactSpace (closure Ω)]
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (f : C(closure Ω, ℝ)) :
    ‖continuousOnClosureToScalarLpLinear hΩ hΩbounded f‖ ≤
      (measureUnivNNReal (PDE.volumeOn Ω)) ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ‖f‖ := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  apply Lp.norm_le_of_ae_bound (norm_nonneg _)
  filter_upwards [
    (memLp_continuousOnClosureRaw hΩ hΩbounded f).coeFn_toLp,
    ae_restrict_mem hΩ.measurableSet] with y hf hy
  change ‖(memLp_continuousOnClosureRaw hΩ hΩbounded f).toLp
      _ y‖ ≤ ‖f‖
  rw [hf, continuousOnClosureRaw, dif_pos (subset_closure hy)]
  exact f.norm_coe_le_norm ⟨y, subset_closure hy⟩

/-- Infrastructure for the clamped reverse-time source curve. -/
def continuousOnClosureToScalarLp

    [CompactSpace (closure Ω)]
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) :
    C(closure Ω, ℝ) →L[ℝ] PDE.ScalarLp Ω (2 ) :=
  LinearMap.mkContinuous _
    _ (norm_continuousOnClosureToScalarLpLinear_apply_le hΩ hΩbounded)

private theorem coeFn_continuousOnClosureToScalarLp

    [CompactSpace (closure Ω)]
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (f : C(closure Ω, ℝ)) :
    continuousOnClosureToScalarLp hΩ hΩbounded f =ᵐ[PDE.volumeOn Ω]
      continuousOnClosureRaw f :=
  (memLp_continuousOnClosureRaw hΩ hΩbounded f).coeFn_toLp

variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (F : PDE.TimeScalarField d)

/-- The clamped scalar source curve in spatial L². -/
def reverseTimeSourceScalarRaw

     :
    ℝ → PDE.ScalarLp Ω (2 ) :=
  letI : CompactSpace (closure Ω) :=
    isCompact_iff_compactSpace.mp hΩbounded.isCompact_closure
  fun τ => continuousOnClosureToScalarLp hΩ hΩbounded
    (reverseTimeSourceContinuousCurve r₀ r₁ h₀₁ F τ)

variable (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

include hFSmooth in
private theorem aestronglyMeasurable_reverseTimeSourceScalarRaw


     :
    AEStronglyMeasurable
      (reverseTimeSourceScalarRaw r₀ r₁ h₀₁ hΩ hΩbounded F)
      (reverseTimeVolume (r₁ - r₀)) := by
  letI : CompactSpace (closure Ω) :=
    isCompact_iff_compactSpace.mp hΩbounded.isCompact_closure
  exact (continuousOnClosureToScalarLp hΩ hΩbounded).continuous.comp_aestronglyMeasurable
    (continuous_reverseTimeSourceContinuousCurve r₀ r₁ h₀₁ F
      hFSmooth).aestronglyMeasurable

private theorem reverseTimeSourceScalarRaw_eq_sourceSlice



    (τ : ℝ) :
    reverseTimeSourceScalarRaw r₀ r₁ h₀₁ hΩ hΩbounded F τ =
      reverseTimeSourceSlice r₁ _ F
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
          r₀ r₁ hΩ hΩbounded F hFSmooth
          _
          (reverseTimeSourceClamp_mem r₀ r₁ h₀₁ τ)) := by
  letI : CompactSpace (closure Ω) :=
    isCompact_iff_compactSpace.mp hΩbounded.isCompact_closure
  apply Lp.ext
  let hSliceMem := reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
    r₀ r₁ hΩ hΩbounded F hFSmooth
    _
    (reverseTimeSourceClamp_mem r₀ r₁ h₀₁ τ)
  filter_upwards [
    coeFn_continuousOnClosureToScalarLp hΩ hΩbounded
      (reverseTimeSourceContinuousCurve r₀ r₁ h₀₁ F τ),
    hSliceMem.coeFn_toLp,
    ae_restrict_mem hΩ.measurableSet] with y hRaw hSlice hy
  change (continuousOnClosureToScalarLp hΩ hΩbounded
    (reverseTimeSourceContinuousCurve r₀ r₁ h₀₁ F τ)) y =
      hSliceMem.toLp ((F (r₁ - (reverseTimeSourceClamp r₀ r₁ h₀₁ τ : ℝ)))) y
  rw [hRaw, hSlice, continuousOnClosureRaw, dif_pos (subset_closure hy)]
  have hContinuousSlice  :=
    (continuousOn_reverseTimeSourceUncurried r₀ r₁ h₀₁ F hFSmooth).uncurry_left τ
      (Set.mem_univ τ)
  exact ContinuousMap.mkD_apply_of_continuousOn hContinuousSlice

/-- A clamped representative of the negative reverse-time source.  Outside
`[0, r₁ - r₀]` it uses endpoint data only, rather than the ambient source. -/
def reverseTimeNegativeSourceRaw


    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ℝ → H10HilbertGraphDual hΩ :=
  fun τ => reverseTimeSourceFunctional hΩ
    (reverseTimeSourceScalarRaw r₀ r₁ h₀₁ hΩ hΩbounded F τ)

variable (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

private theorem aestronglyMeasurable_reverseTimeNegativeSourceRaw


     :
    AEStronglyMeasurable
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
      (reverseTimeVolume (r₁ - r₀)) :=
  by
    change AEStronglyMeasurable
      (fun τ => -(scalarLpToH10HilbertGraphDual hΩ)
        (reverseTimeSourceScalarRaw r₀ r₁ h₀₁ hΩ hΩbounded F τ)) _
    simpa only [ContinuousLinearMap.neg_apply] using
      ((-scalarLpToH10HilbertGraphDual hΩ).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_reverseTimeSourceScalarRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth))

/-- The clamped negative source is square-integrable for the literal reverse-time measure. -/
theorem memLp_reverseTimeNegativeSourceRaw


     :
    MemLp (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
      (2 ) (reverseTimeVolume (r₁ - r₀)) := by
  letI : IsFiniteMeasure (reverseTimeVolume (r₁ - r₀)) := by
    dsimp only [reverseTimeVolume, reverseTimeOpenInterval]
    infer_instance
  obtain ⟨M, _, hM⟩ :=
    exists_reverseTimeSourceSlice_L2_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded F hFSmooth
  refine MemLp.of_bound
    (aestronglyMeasurable_reverseTimeNegativeSourceRaw
      r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
    (‖valueCLM hΩ‖ * M) ?_
  filter_upwards with τ
  rw [reverseTimeNegativeSourceRaw,
    reverseTimeSourceScalarRaw_eq_sourceSlice r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ]
  refine (norm_reverseTimeSourceFunctional_le hΩ _).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact hM _
    (reverseTimeSourceClamp_mem r₀ r₁ h₀₁ τ) _

/-- The negative reverse-time source packaged as a Bochner `L²` curve. -/
def reverseTimeNegativeSource


     :
    ReverseTimeL2VStar hΩ (r₁ - r₀) :=
  (memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).toLp
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)

/-- On the literal open reverse-time interval, the Bochner source has the
negative fixed-time source functional as its representative. -/
theorem ae_reverseTimeNegativeSource_apply


     :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ∀ hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
        reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ =
          reverseTimeSourceFunctional hΩ
            (reverseTimeSourceSlice r₁ τ F
              (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
                r₀ r₁ hΩ hΩbounded F hFSmooth τ
                ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)) := by
  filter_upwards [
    (memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp]
    with τ hToLp hτ
  change (memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).toLp
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) τ = _
  rw [hToLp, reverseTimeNegativeSourceRaw,
    reverseTimeSourceScalarRaw_eq_sourceSlice r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ]

  simp only [reverseTimeSourceClamp,
    Set.projIcc_of_mem (le_of_lt (sub_pos.mpr h₀₁)) (⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)]

/-- The clamped negative reverse-time source is continuous as a dual-valued
curve. -/
theorem continuous_reverseTimeNegativeSourceRaw


     :
    Continuous
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) := by
  letI : CompactSpace (closure Ω) :=
    isCompact_iff_compactSpace.mp hΩbounded.isCompact_closure
  change Continuous (fun τ => -(scalarLpToH10HilbertGraphDual hΩ)
    ((continuousOnClosureToScalarLp hΩ hΩbounded)
      (reverseTimeSourceContinuousCurve r₀ r₁ h₀₁ F τ)))
  simpa only [Function.comp_def, ContinuousLinearMap.neg_apply] using
    ((-scalarLpToH10HilbertGraphDual hΩ).continuous.comp
      ((continuousOnClosureToScalarLp hΩ hΩbounded).continuous.comp
        (continuous_reverseTimeSourceContinuousCurve r₀ r₁ h₀₁ F hFSmooth)))

/-- On the true closed reverse-time interval, the clamped source is the
literal negative source functional of the corresponding source slice. -/
theorem reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc



    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ =
      reverseTimeSourceFunctional hΩ
        (reverseTimeSourceSlice r₁ τ F
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
            r₀ r₁ hΩ hΩbounded F hFSmooth τ hτ)) := by
  rw [reverseTimeNegativeSourceRaw,
    reverseTimeSourceScalarRaw_eq_sourceSlice r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ]
  simp only [reverseTimeSourceClamp,
    Set.projIcc_of_mem (le_of_lt (sub_pos.mpr h₀₁)) hτ]

end HypoellipticAleksandrov.Parabolic.Dirichlet
