module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionMarginal
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierBound
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Green.LogIntegration
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Green.Gluing
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierEmbedding
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardCone
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Green HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped ENNReal NNReal ProbabilityTheory
section
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Decay HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal ProbabilityTheory



/-- Interior Fourier measures of the carrier adapter are exactly the interval Fourier measures. -/
theorem intervalExtension_fourier_inside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) :
    fourierKernel (intervalExtension hJ K) σ τ hστ ξ v.1 =
      intervalFourierKernel K σ τ hστ ξ v := by
  have he : (intervalExtension hJ K).master (wholeSpaceQuery σ τ hστ v.1 0) =
      K.master (movingQuery σ τ hστ v.1 0
        (by simpa using v.2)) := by
    change intervalExtensionMaster hJ K (intervalQueryInclusion
      (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2))) = _
    exact intervalExtensionMaster_inside hJ K _
  apply VectorMeasure.ext
  intro E hE
  rw [fourierKernel_spec _ _ _ _ _ _ E hE,
    intervalFourierKernel_spec _ _ _ _ _ _ E hE, he]
  rfl

/-- Exterior Fourier measures of the carrier adapter vanish. -/
theorem intervalExtension_fourier_outside {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1)
    (hv : v ∉ PDE.oneDimensionalAxisBox a c) :
    fourierKernel (intervalExtension hJ K) σ τ hστ ξ v = 0 := by
  have he : (intervalExtension hJ K).master (wholeSpaceQuery σ τ hστ v 0) = 0 :=
    intervalExtensionMaster_outside hJ K _ hv
  apply VectorMeasure.ext
  intro E hE
  rw [fourierKernel_spec _ _ _ _ _ _ E hE, he]
  simp



/-- Phase-weighted evolution has variation dominated by the positive pushed marginal. -/
theorem interval_evolved_variation_domination
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (κ : ProbabilityTheory.Kernel X Y)
    (ph : Y → ℂ) (π : Y → Z) (_hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) :
    (evolvedMeasure μ κ ph π).variation ≤ ((μ ⊗ₘ κ).snd).map π := by
  let Λ := (μ ⊗ₘ κ).snd
  by_cases hi : Integrable ph Λ
  · unfold evolvedMeasure
    refine VectorMeasure.variation_map_le.trans ?_
    rw [Measure.variation_withDensityᵥ hi]
    have he : (fun y => ‖ph y‖ₑ) = (fun _ : Y => 1) := by
      funext y
      simp [← ofReal_norm, hph1 y]
    rw [he]
    change Measure.map π (Λ.withDensity 1) ≤ _
    rw [withDensity_one]
  · have hz : Λ.withDensityᵥ ph = 0 := by
      rw [Measure.withDensityᵥ, dite_eq_right hi]
    unfold evolvedMeasure
    change ((Λ.withDensityᵥ ph).map π).variation ≤ _
    rw [hz, VectorMeasure.map_zero, VectorMeasure.variation_zero]
    exact Measure.zero_le _

/-- The dominated phase-weighted evolution has finite variation for finite source and kernel. -/
theorem interval_evolved_variation_finite
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [IsFiniteMeasure μ] (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsFiniteKernel κ] (ph : Y → ℂ) (π : Y → Z)
    (hph : Measurable ph) (hph1 : ∀ y, ‖ph y‖ = 1) :
    IsFiniteMeasure (evolvedMeasure μ κ ph π).variation :=
  isFiniteMeasure_of_le _ (interval_evolved_variation_domination μ κ ph π hph hph1)


variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))



end

/-- Shared slab reconstruction inputs with the half-time killing factor retained. -/
theorem killed_slab_fourier_of_bounds {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hcdec : 0 < cdec)
    (hdec : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d),
      totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤
        ENNReal.ofReal (Cdec * Real.exp (-cdec * (τ - σ) *
          (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) :
    ∃ g : SlabBase d → ℝ≥0∞, Measurable g ∧
      (slabMeasure d T Γ).fst = (slabBase d T).withDensity g ∧
      (∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        eLpNorm g (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ)) ∧
      ∃ f : PDE.Vec d → SlabBase d → ℂ, Measurable (Function.uncurry f) ∧
      (∀ ξ, Integrable (f ξ) (slabBase d T) ∧
        ∀ E : Set (SlabBase d), MeasurableSet E →
          ∫ y in E, f ξ y ∂slabBase d T =
            ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
              Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        (∀ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ) * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))) ∧
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2)) *
            ENNReal.ofReal (Real.exp (-((cdec / 2) * T)))   := by
  have killed_slab_fourier_density_bound (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) σ₀)) [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ) {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T)) (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) (hhalf : (halfMeasure K σ₀ T hT.le μ ξ).variation univ ≤
      μ univ * ENNReal.ofReal (Cdec * Real.exp
        (-(cdec * (T / 2) * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))) :
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * 2 ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) := by
    intro γ hγ1 hγ2
    have hρfin : IsFiniteMeasure (halfMeasure K σ₀ T hT.le μ ξ).variation :=
      interval_evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
    obtain ⟨gξ, hgξ, hnorm⟩ := hocc.2 (halfMeasure K σ₀ T hT.le μ ξ).variation (σ₀ + T / 2)
      (3 * T / 2) (by positivity)
    have hint : Integrable gξ
        (volume.restrict (Ioo 0 (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))) := by
      have := (hnorm 1 le_rfl (one_le_slabGamma0 hd)).1
      rw [ENNReal.ofReal_one] at this
      exact memLp_one_iff_integrable.1 this
    obtain ⟨hmem, hbd⟩ := hnorm γ hγ1 hγ2
    have hC0 := hocc.1 γ hγ1 hγ2
    have hβ := slabBeta_nonneg hd hγ1 hγ2
    -- step 1: domination
    have h1 : eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
        eLpNorm (fun y => ENNReal.ofReal (gξ (slabShift d (T / 2) y))) (ENNReal.ofReal γ)
          (slabBase d T) := by
      refine eLpNorm_mono_enorm_ae (f := k)
        (g := fun y => ENNReal.ofReal (gξ (slabShift d (T / 2) y))) hk.aestronglyMeasurable ?_
      filter_upwards [(slab_fourier_ae_bound K hcov hcomp σ₀ μ Γ hΓ hT ξ gξ hgξ hint k hk hkE)] with y hy
      rwa [enorm_eq_self]
    -- step 2: the occupation bound
    set Cn : ℝ := Cocc γ * ((halfMeasure K σ₀ T hT.le μ ξ).variation univ).toReal *
      (3 * T / 2) ^ slabBeta d γ with hCn
    have hbd' : eLpNorm gξ (ENNReal.ofReal γ)
        (volume.restrict (Ioo 0 (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))) ≤
          ENNReal.ofReal Cn := by
      rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal hbd
    have h2 := eLpNorm_slabShift_le gξ hgξ.1 hgξ.2.1 (T / 2) T (3 * T / 2) γ Cn hT.le
      (by linarith) (by linarith) hbd'
    -- step 3: arithmetic
    set E : ℝ := Real.exp (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hmass := hhalf
    have hrho : ((halfMeasure K σ₀ T hT.le μ ξ).variation univ).toReal ≤
        (μ univ).toReal * (Cdec * E) := by
      have hexp : Real.exp (-(cdec * (T / 2) * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) = E :=
        by
        rw [hE]; congr 1; ring
      rw [hexp] at hmass
      have hfin : μ univ * ENNReal.ofReal (Cdec * E) ≠ ⊤ :=
        ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
      have := ENNReal.toReal_mono hfin hmass
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hfinal : ENNReal.ofReal Cn ≤
        ENNReal.ofReal (Cocc γ * Cdec * 2 ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) * ENNReal.ofReal E := by
      refine (ENNReal.ofReal_le_ofReal (fourier_bound_arith _ _ _ _ _ _ _ hC0 hCdec.le ENNReal.toReal_nonneg hE0 hT hβ hrho)).trans (le_of_eq ?_)
      have h2pos : 0 ≤ Cocc γ * Cdec * 2 ^ slabBeta d γ :=
        mul_nonneg (mul_nonneg hC0 hCdec.le) (Real.rpow_nonneg (by norm_num) _)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul h2pos, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact h1.trans (h2.trans hfinal)
  have killed_halfMeasure_mass_le (σ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) σ)) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) :
      (halfMeasure K σ T hT.le μ ξ).variation univ ≤
      μ univ * ENNReal.ofReal (Cdec * Real.exp
        (-(cdec * (T / 2) * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) := by
    unfold halfMeasure
    refine evolved_variation_le μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
      (measurable_halfVelocity _) _ (fun x => ?_)
    refine (fibreMeasure_variation_le K hcov σ _ (le_halfTime σ T hT.le) ξ x).trans ?_
    have h := hdec σ (σ + T / 2) (le_halfTime σ T hT.le) ξ x.1.1
    have he : σ + T / 2 - σ = T / 2 := by ring
    simpa using h
  obtain ⟨g, hgm, hgE, hgnorm⟩ := slab_marginal_density hd K hcov Cocc hocc σ₀ μ Γ hΓ hT
  have hΓfin : IsFiniteMeasure (Γ.restrict (slabSet (d := d) T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  obtain ⟨kf, hkm, hkf⟩ := exists_measurable_fourier_family hd hT Γ g hgE
  have hk : ∀ (ξ : PDE.Vec d) (γ : ℝ), 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * 2 ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) :=
    fun ξ => killed_slab_fourier_density_bound σ₀ μ Γ hΓ hT ξ (kf ξ) (hkf ξ).1 (hkf ξ).2
      (killed_halfMeasure_mass_le σ₀ μ hT ξ)
  have hCγ : ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) = ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) :=
    fun _ _ _ => rfl
  have hfin : ∫⁻ ζ, decayProfile d (cdec / 2) ζ < ⊤ :=
    lintegral_decayProfile_lt_top hd (by linarith)
  have hAeq : ∫⁻ ζ, decayProfile d (cdec / 2) ζ = ENNReal.ofReal (slabFreqConstant d (cdec / 2)) :=
    (ENNReal.ofReal_toReal hfin.ne).symm
  have hA0 : 0 ≤ slabFreqConstant d (cdec / 2) := ENNReal.toReal_nonneg
  set M : ℝ := (μ univ).toReal with hMdef
  have hM : μ univ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hq0 : (0 : ℝ) ≤ ((2 * Real.pi) ^ d)⁻¹ := by positivity
  have hF1 := one_le_slabK1_factor (d := d) hCdec cdec
  have hF2 : Cdec ≤ (1 + Cdec) * (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2)) := by
    nlinarith [mul_nonneg hq0 hA0]
  have hK1 : ∀ γ : ℝ, slabK1 d Cdec cdec γ =
      (2 : ℝ) ^ slabBeta d γ * ((1 + Cdec) *
        (1 + ((2 * Real.pi) ^ d)⁻¹ * slabFreqConstant d (cdec / 2))) := fun γ => by
    unfold slabK1; ring
  have hfam :
      (∀ ξ, Integrable (kf ξ) (slabBase d T) ∧
        ∀ E : Set (SlabBase d), MeasurableSet E →
          ∫ y in E, kf ξ y ∂slabBase d T =
            ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
              Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        (∀ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ) * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))) ∧
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2)) *
            ENNReal.ofReal (Real.exp (-((cdec / 2) * T))) := by
    refine ⟨fun ξ => ⟨(hkf ξ).1, (hkf ξ).2⟩, fun γ h1 h2 => ⟨fun ξ => ?_, ?_⟩⟩
    · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      refine (hk ξ γ h1 h2).trans ?_
      rw [hCγ γ h1 h2]
      have hle : ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) ≤
          ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK1]
        nlinarith [mul_nonneg hC0 h2b, mul_nonneg hC0 hCdec.le]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) le_rfl
    · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      have ht1 : 0 ≤ T ^ slabBeta d γ := Real.rpow_nonneg hT.le _
      have ht2 : 0 ≤ T ^ (-(3 * (d : ℝ) / 2)) := Real.rpow_nonneg hT.le _
      let Q := ENNReal.ofReal (Real.exp (-((cdec / 2) * T)))
      have hsplit (ξ : PDE.Vec d) : ENNReal.ofReal (Real.exp
          (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) =
          Q * ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) := by
        rw [show -((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))) =
          -((cdec / 2) * T) + -((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))
            by ring, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      set D : ℝ≥0∞ := ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
        ENNReal.ofReal (T ^ slabBeta d γ) * Q with hD
      have hDtop : D ≠ ⊤ := by
        rw [hD]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (measure_ne_top _ _)) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
      calc ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T)
          ≤ ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ : PDE.Vec d, D * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) :=
            mul_le_mul' le_rfl (lintegral_mono (fun ξ => by
              have h := hk ξ γ h1 h2
              rw [hsplit ξ] at h
              simpa only [hD, mul_assoc] using h))
        _ = ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            (D * (ENNReal.ofReal (T ^ (-(3 * (d : ℝ) / 2))) *
              ENNReal.ofReal (slabFreqConstant d (cdec / 2)))) := by
            rw [lintegral_const_mul' D _ hDtop, (lintegral_decayProfile_scaling d (cdec / 2) T hT), hAeq]
        _ ≤ _ := by
            rw [hCγ γ h1 h2, hD, hM]
            have hrp : T ^ (slabBeta d γ - 3 * (d : ℝ) / 2) =
                T ^ slabBeta d γ * T ^ (-(3 * (d : ℝ) / 2)) := by
              rw [← Real.rpow_add hT, sub_eq_add_neg]
            rw [hrp]
            convert mul_le_mul' (freq_ennreal (Cocc γ) Cdec ((2 : ℝ) ^ slabBeta d γ) M (T ^
              slabBeta d γ)
              (T ^ (-(3 * (d : ℝ) / 2))) (slabFreqConstant d (cdec / 2)) (((2 * Real.pi) ^ d)⁻¹)
              (slabK1 d Cdec cdec γ) _ hC0 hCdec.le h2b hM0 ht1 ht2 hA0 hq0
              (by unfold slabK1; ring) rfl) (le_rfl : Q ≤ Q) using 1; ring
  refine ⟨g, hgm, slabMeasure_fst T Γ g hgE, fun γ h1 h2 => ?_, kf, hkm, hfam⟩
  · have hC0 : 0 ≤ Cocc γ := hocc.1 γ h1 h2
    refine (hgnorm γ h1 h2).trans ?_
    rw [hCγ γ h1 h2]
    have hle : ENNReal.ofReal (Cocc γ * (2 : ℝ) ^ slabBeta d γ) ≤
        ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hK1]
      nlinarith [mul_nonneg hC0 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ))]
    exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl



/-- An interval Green measure satisfies the adapted whole-carrier characterization. -/
theorem intervalExtension_isGreenMeasure {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ : ℝ) (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)) (hΓ : IsGreenMeasure K σ ⊤ μ Γ) :
    IsGreenMeasure (intervalExtension hJ K) σ ⊤ (μ.map (intervalStateInclusion σ)) Γ := by
  intro F hF
  let Kw := intervalExtension hJ K
  have : ProbabilityTheory.IsFiniteKernel (elapsedKernel Kw σ ⊤) := by
    unfold elapsedKernel
    infer_instance
  have hf : Measurable (fun q :
      (EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ × ElapsedTime ⊤) ×
        EvolutionAmbientState 1 => F (q.1.2, q.2)) := hF.comp (by fun_prop)
  have hi : Measurable (fun q :
      EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ × ElapsedTime ⊤ =>
      ∫⁻ w, F (q.2, w) ∂elapsedKernel Kw σ ⊤ q) :=
    hf.lintegral_kernel_prod_right'
  have hm : Measurable (fun p :
      EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ =>
      ∫⁻ t : ElapsedTime ⊤, ∫⁻ w, F (t, w) ∂Kw.master (elapsedQuery σ p t)
        ∂elapsedVolume ⊤) := hi.lintegral_prod_right'
  rw [lintegral_map hm (measurable_intervalStateInclusion σ), hΓ F hF]
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall fun p => ?_
  dsimp only
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall fun t => ?_
  dsimp only
  change (∫⁻ w, F (t, w) ∂K.master (elapsedQuery σ p t)) =
    ∫⁻ w, F (t, w) ∂intervalExtensionMaster hJ K
      (intervalQueryInclusion (elapsedQuery σ p t))
  rw [intervalExtensionMaster_inside]


/-- The scalar slab exponent is the literal exponent in case I. -/
theorem interval_slab_beta (γ : ℝ) : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
  norm_num [slabBeta]

/-- Integrating frequencies gives the scalar slab height exponent. -/
theorem interval_slab_height_exponent (γ : ℝ) :
    slabBeta 1 γ - 3 * (1 : ℝ) / 2 = 3 / (2 * γ) - 2 := by
  rw [interval_slab_beta]
  ring




/-- The shared reconstruction proof with the interval killing height estimate. -/
theorem killed_slab_reconstruction {Ω : Set (PDE.Vec 1)} {γ : ℝ → PDE.Vec 1}
    (C : ℝ → ℝ≥0) (k : ℝ) (K : MovingFiberKernel Ω γ) (σ : ℝ)
    (μ : Measure (EvolutionState Ω γ σ)) [IsFiniteMeasure μ]
    (Γ : Measure (GreenCarrier 1)) (hΓ : IsGreenMeasure K σ ⊤ μ Γ)
    {q T : ℝ} (hq : 1 < q) (hq2 : q < 2) (hT : 0 < T)
    (g : SlabBase 1 → ℝ≥0∞) (hgm : Measurable g)
    (hgmarg : (slabMeasure 1 T Γ).fst = (slabBase 1 T).withDensity g)
    (hgnorm : ∀ r : ℝ, 1 ≤ r → r ≤ slabGamma0 1 →
      eLpNorm g (ENNReal.ofReal r) (slabBase 1 T) ≤
      (C r : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ slabBeta 1 r))
    (f : PDE.Vec 1 → SlabBase 1 → ℂ)
    (hf : ∀ ξ, Integrable (f ξ) (slabBase 1 T) ∧
      ∀ E : Set (SlabBase 1), MeasurableSet E → ∫ y in E, f ξ y ∂slabBase 1 T =
        ∫ p in {p : GreenCarrier 1 | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ)
    (hheight : ENNReal.ofReal ((2 * Real.pi)⁻¹) *
      ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal (slabGamma 1 q)) (slabBase 1 T) ≤
      (C (slabGamma 1 q) : ℝ≥0∞) * μ univ * ENNReal.ofReal
        (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2) * Real.exp (-k * T))) :
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
        (slabConstant 1 q C : ℝ≥0∞) * μ univ ^ q *
          ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-(k * (q - 1)) * T))  := by
  have killed_slab_arith (a : ℝ≥0) (b : ℝ≥0) (M : ℝ≥0∞) :
      ((a : ℝ≥0∞) * M * ENNReal.ofReal
        (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2) * Real.exp (-k * T))) ^ (q - 1) *
      ((b : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta 1 (slabQ1 1 q))) =
    ((a ^ (q - 1) * b : ℝ≥0) : ℝ≥0∞) * M ^ q *
      ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-(k * (q - 1)) * T)) := by
    have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq2
    have he := slab_exponent (d := 1) hq hqd
    norm_num only [Nat.cast_one, mul_one] at he
    have he' : (q - 1) * (slabBeta 1 (slabGamma 1 q) - 3 / 2) +
        slabBeta 1 (slabQ1 1 q) = 3 - 2 * q := by linarith
    have hq0 : 0 ≤ q - 1 := by linarith
    let X : ℝ≥0∞ := (a : ℝ≥0∞) * M *
      ENNReal.ofReal (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2))
    let Y : ℝ≥0∞ := (b : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta 1 (slabQ1 1 q))
    let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-k * T))
    calc
      _ = (X * E) ^ (q - 1) * Y := by
        dsimp only [X, Y, E]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
        congr 2
        ring
      _ = (X ^ (q - 1) * Y) * E ^ (q - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0]
        ring
      _ = _ := by
        dsimp only [X, Y, E]
        rw [slab_arith a b M hT hq he', ENNReal.ofReal_rpow_of_nonneg
          (Real.exp_pos _).le hq0, ← Real.exp_mul,
          ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
        rw [show -k * T * (q - 1) = -(k * (q - 1)) * T by ring]
        ring
  have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq2
  have hq0 : 0 ≤ q - 1 := by linarith
  obtain ⟨hqγ, hγ0⟩ := slab_q_lt_gamma (d := 1) hq hqd
  obtain ⟨hq1a, hq1b⟩ := slab_q1_bounds (d := 1) hq hqd
  have hγ1 : 1 ≤ slabGamma 1 q := (slab_gamma_one_lt (d := 1) hq hqd).le
  have hMfin : μ univ < ⊤ := measure_lt_top μ _
  have : IsFiniteMeasure (slabMeasure 1 T Γ) := ⟨by
    rw [slabMeasure_univ]
    exact (green_slab_le K σ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top hMfin ENNReal.ofReal_lt_top)⟩
  have hgn := hgnorm (slabQ1 1 q) hq1a hq1b
  have hgL : eLpNorm g (ENNReal.ofReal (slabQ1 1 q)) (slabBase 1 T) < ⊤ :=
    hgn.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hMfin)
      ENNReal.ofReal_lt_top)
  have hH : ENNReal.ofReal (((2 * Real.pi) ^ 1)⁻¹) *
      ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal (slabGamma 1 q)) (slabBase 1 T) < ⊤ := by
    simpa using hheight.trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hMfin)
        ENNReal.ofReal_lt_top)
  obtain ⟨G', hG'm, hΓG', hbd, -⟩ := Reconstruction.reconstruction (m := slabBase 1 T)
    (slabMeasure 1 T Γ) hgm.aemeasurable hgmarg hq hqγ (slab_hq₁ (d := 1) hq hqd) hgL f
    (fun ξ => ⟨(hf ξ).1, slabMeasure_fourier T Γ ξ (f ξ) (hf ξ).2⟩) hH
  refine ⟨fun p => G' (slabRegroup 1 p), hG'm.comp (slabRegroup 1).measurable,
    eq_withDensity_of_map_eq (slabRegroup 1) (measurePreserving_slabRegroup 1 T) hΓG', ?_⟩
  calc ∫⁻ p in slabSet T, G' (slabRegroup 1 p) ^ q ∂greenLebesgue 1
      = ∫⁻ y, G' y ^ q ∂((slabBase 1 T).prod volume) :=
        (measurePreserving_slabRegroup 1 T).lintegral_comp_emb
          (slabRegroup 1).measurableEmbedding (fun y => G' y ^ q)
    _ ≤ _ := hbd
    _ ≤ ((C (slabGamma 1 q) : ℝ≥0∞) * μ univ * ENNReal.ofReal
          (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2) * Real.exp (-k * T))) ^ (q - 1) *
        ((C (slabQ1 1 q) : ℝ≥0∞) * μ univ *
          ENNReal.ofReal (T ^ slabBeta 1 (slabQ1 1 q))) := by
        apply mul_le_mul' (ENNReal.rpow_le_rpow _ hq0) hgn
        simpa using hheight
    _ = _ := killed_slab_arith _ _ _




/-- The killed power moment is finite whenever its exponent at zero is integrable. -/
theorem killed_power_moment_finite {δ k : ℝ} (hδ : 0 < δ) (hk : 0 < k) :
    (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
      (T ^ (δ - 1) * Real.exp (-k * T))) < ⊤ := by
  have hi : IntegrableOn (fun T : ℝ => T ^ (δ - 1) * Real.exp (-k * T)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := δ - 1) (by linarith) (by norm_num) hk
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · exact ENNReal.ofReal_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
    exact mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_pos _).le

/-- The inverse-time weight combines with the killed slab power exactly. -/
theorem lintegral_inv_killed_power (δ k : ℝ) (A : ℝ≥0∞) :
    (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal T⁻¹ *
      (A * ENNReal.ofReal (T ^ δ * Real.exp (-k * T)))) =
    A * ∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
      (T ^ (δ - 1) * Real.exp (-k * T)) := by
  have hm : Measurable (fun T : ℝ => ENNReal.ofReal
      (T ^ (δ - 1) * Real.exp (-k * T))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_id.pow_const _).mul (Real.measurable_exp.comp
        (measurable_const.mul measurable_id)))
  rw [← lintegral_const_mul A hm]
  refine setLIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
  have ht : T ^ (δ - 1) = T⁻¹ * T ^ δ := by
    rw [Real.rpow_sub hT, Real.rpow_one]
    field_simp
  rw [ht, ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hT.le)
    (Real.rpow_nonneg hT.le _)), ENNReal.ofReal_mul (inv_nonneg.mpr hT.le),
    ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
  ring

/-- Logarithmic averaging over all positive times, obtained by increasing finite horizons. -/
theorem log_mul_measure_univ_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {h : X → ℝ} (hh : Measurable h)
    (hpos : ∀ x, 0 < h x) :
    ENNReal.ofReal (Real.log 2) * ν univ ≤
      ∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal T⁻¹ * ν {x | T < h x ∧ h x < 2 * T} := by
  have hm : Monotone (fun S : ℝ => {x | h x < S}) := by
    intro S R hSR x hx
    exact hx.trans_le hSR
  have hu : (⋃ S : ℝ, {x | h x < S}) = univ := by
    ext x
    simp
    exact ⟨h x + 1, by linarith⟩
  rw [← hu, hm.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun S => (log_mul_measure_le ν hh hpos S).trans ?_
  exact lintegral_mono_set (fun T hT => hT.1)


/-- The uniform constant obtained by logarithmic averaging of the killed moment. -/
def killedGreenConstant (A δ k q : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal A * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
    (T ^ (δ - 1) * Real.exp (-k * T))) *
      (ENNReal.ofReal (Real.log 2))⁻¹) ^ (1 / q)

/-- The averaging constant is finite. -/
theorem killedGreenConstant_ne_top {A δ k q : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hq : 0 < q) :
    killedGreenConstant A δ k q ≠ ⊤ := by
  unfold killedGreenConstant
  apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (killed_power_moment_finite hδ hk).ne
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr
      (Real.log_pos one_lt_two)).ne'

/-- Killed local bounds imply the global norm, with no finite horizon factor. -/
theorem killed_green_norm_bound {d : ℕ} (G : GreenCarrier d → ℝ≥0∞)
    (hGm : Measurable G) (A δ k q : ℝ) (M : ℝ≥0∞) (hq : 0 < q)
    (hslab : ∀ T : ℝ, 0 < T →
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue d ≤
        ENNReal.ofReal A * M ^ q *
          ENNReal.ofReal (T ^ δ * Real.exp (-k * T))) :
    eLpNorm G (ENNReal.ofReal q) (greenLebesgue d) ≤
      killedGreenConstant A δ k q * M := by
  let ν := (greenLebesgue d).withDensity (fun p => G p ^ q)
  have hν : ∀ T : ℝ, 0 < T → ν (slabSet T) ≤
      ENNReal.ofReal A * M ^ q *
        ENNReal.ofReal (T ^ δ * Real.exp (-k * T)) := by
    intro T hT
    dsimp only [ν]
    rw [withDensity_apply _ (measurableSet_slabSet T)]
    exact hslab T hT
  have hint : ENNReal.ofReal (Real.log 2) * ν univ ≤
      (ENNReal.ofReal A * M ^ q) * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
        (T ^ (δ - 1) * Real.exp (-k * T))) := by
    refine (log_mul_measure_univ_le ν (measurable_subtype_coe.comp measurable_fst) (fun p => p.1.2.1)).trans ?_
    rw [← lintegral_inv_killed_power]
    refine setLIntegral_mono' measurableSet_Ioi fun T hT => ?_
    exact mul_le_mul_right (hν T hT) _
  have hL0 : ENNReal.ofReal (Real.log 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)).ne'
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
    hGm.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
  simp only [enorm_eq_self]
  have hmass : (∫⁻ p, G p ^ q ∂greenLebesgue d) = ν univ := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [hmass]
  refine (ENNReal.rpow_le_rpow ((ENNReal.mul_le_iff_le_inv hL0 ENNReal.ofReal_ne_top).mp hint) (by positivity : 0 ≤ 1 / q)).trans (le_of_eq ?_)
  unfold killedGreenConstant
  rw [show (ENNReal.ofReal (Real.log 2))⁻¹ *
      ((ENNReal.ofReal A * M ^ q) * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
        (T ^ (δ - 1) * Real.exp (-k * T)))) =
      (ENNReal.ofReal A * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
        (T ^ (δ - 1) * Real.exp (-k * T))) *
        (ENNReal.ofReal (Real.log 2))⁻¹) * M ^ q by ring]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / q),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]


/-- The exponentially killed time profile has exact elapsed integral `1/k`. -/
theorem lintegral_interval_killing_profile {k : ℝ} (hk : 0 < k) :
    (∫⁻ t : ElapsedTime ⊤, ENNReal.ofReal (Real.exp (-k * t.1))
      ∂elapsedVolume ⊤) = ENNReal.ofReal k⁻¹ := by
  rw [lintegral_elapsed_top (fun t : ℝ => ENNReal.ofReal (Real.exp (-k * t)))]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) 0)
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  congr 1
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hk) 0]
  simp

/-- Infinite-horizon interval Green mass is uniformly finite. -/
theorem interval_green_finite_mass
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlength : 0 < length) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ : ℝ)
      (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
      [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)),
      IsGreenMeasure K σ ⊤ μ Γ → Γ univ ≤ ENNReal.ofReal C * μ univ ∧ Γ univ < ⊤ := by
  obtain ⟨C, k, hC, hk, hmass⟩ :=
    interval_mass_decay hH hLE lam Lam m Lb length hlam hlength
  refine ⟨C * k⁻¹, mul_pos hC (inv_pos.mpr hk), ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
  have hpoint : ∀ (p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ)
      (t : ElapsedTime ⊤), K.master (elapsedQuery σ p t) univ ≤
      ENNReal.ofReal (C * Real.exp (-k * t.1)) := by
    intro p t
    have hv : p.1.1 ∈ PDE.oneDimensionalAxisBox a c := by
      simpa [evolutionStateSet, movingDomain_stationary] using p.2.1
    have hm := hmass a c hac B b hs hJ S K hr hlen σ (σ + t.1)
      (le_add_of_nonneg_right t.2.1.le) ⟨p.1.1, hv⟩
    have he := interval_parabolic_mass_eq_master hJ K B ((interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1) σ (σ + t.1)
      (le_add_of_nonneg_right t.2.1.le) p.1.1 p.1.2 p.2.1
    unfold Measure.real at hm
    rw [he] at hm
    have hf : K.master (elapsedQuery σ p t) univ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (K.mass_le_one _)
    rw [← ENNReal.ofReal_toReal hf]
    apply ENNReal.ofReal_le_ofReal
    simpa only [movingQuery, elapsedQuery, add_sub_cancel_left] using hm
  have hbound : Γ univ ≤ ENNReal.ofReal (C * k⁻¹) * μ univ := by
    rw [← lintegral_one, hΓ _ measurable_const]
    simp only [lintegral_one]
    calc
      _ ≤ ∫⁻ _p, ∫⁻ t : ElapsedTime ⊤,
          ENNReal.ofReal (C * Real.exp (-k * t.1)) ∂elapsedVolume ⊤ ∂μ :=
        lintegral_mono fun p => lintegral_mono fun t => hpoint p t
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul hC.le]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_interval_killing_profile hk,
          lintegral_const]
  exact ⟨hbound, hbound.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ))⟩


/-- The interval Green theorem: uniform density norm and finite infinite-horizon mass. -/
theorem interval_green_density
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ : ℝ),
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ = (greenLebesgue 1).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C * μ univ ∧
      Γ univ < ⊤   := by
  have interval_slab_density (hq2 : q < 2) :
      ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ T : ℝ), 0 < T →
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
        ENNReal.ofReal C * μ univ ^ q *
          ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-k * T)) := by
    have intervalExtension_fourier_decay :
        ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
        (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
        (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1),
      totalVariationNorm (fourierKernel (intervalExtension hJ K) σ τ hστ ξ v) ≤
        ENNReal.ofReal (C * Real.exp (-k * (τ - σ) *
          (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) := by
      obtain ⟨C, k, hC, hk, hdec⟩ := interval_fourier_decay hH hLE lam Lam m Lb length
        hlam hlamLam hm hmLb hlength
      refine ⟨C, k, hC, hk, ?_⟩
      intro a c hac B b hs hJ S K hr hlen σ τ hστ ξ v
      by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
      · rw [intervalExtension_fourier_inside hJ K σ τ hστ ξ ⟨v, hv⟩]
        have h := hdec a c hac B b hs hJ S K hr hlen σ τ hστ v ξ
          (by simpa only [movingDomain_stationary] using hv) _
          (intervalFourierKernel_spec K σ τ hστ ξ ⟨v, hv⟩)
        rw [← ENNReal.ofReal_toReal
          (show totalVariationNorm (intervalFourierKernel K σ τ hστ ξ ⟨v, hv⟩) ≠ ⊤ from
            ne_top_of_le_ne_top ENNReal.one_ne_top
              (intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ ⟨v, hv⟩))]
        exact ENNReal.ofReal_le_ofReal h
      · rw [intervalExtension_fourier_outside hJ K σ τ hστ ξ v hv]
        simp [totalVariationNorm, VectorMeasure.variation_zero, Measure.coe_zero, zero_le]
    have intervalExtension_occupation :
        ∃ C : ℝ → ℝ,
      ∀ (m Lb : ℝ), 0 < m → m ≤ Lb →
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
        (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
        (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K → OccupationBoundedBy (intervalExtension hJ K) C := open HypoellipticAleksandrov.Parabolic in by
      obtain ⟨C, hC, hocc⟩ := interval_occupation hH hLE lam Lam hlam hlamLam
      refine ⟨C, ?_⟩
      intro m Lb hm hmLb a c hac B b hs hJ S K hr
      refine ⟨fun γ hγ1 hγ2 => hC γ hγ1 (by norm_num [slabGamma0] at hγ2; exact hγ2), ?_⟩
      intro ρ _ σ T hT
      let ρj : Measure (PDE.oneDimensionalAxisBox a c) := Measure.comap Subtype.val ρ
      have hρj : ρj univ ≤ ρ univ := intervalInitial_comap_mass_le hJ ρ
      have : IsFiniteMeasure ρj := ⟨hρj.trans_lt (measure_lt_top ρ univ)⟩
      obtain ⟨g, hgm, hg0, hchar, hb⟩ :=
        hocc m Lb hm hmLb a c hac B b hs hJ S K hr σ T hT ρj
      have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
      let U : Set (TimeVelocity 1) := Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c
      let gw := U.indicator g
      have hU : MeasurableSet U := measurableSet_Ioo.prod hJ
      have hUR : U ⊆ Ioo (0 : ℝ) T ×ˢ univ := prod_mono Subset.rfl (subset_univ _)
      have hgw : Measurable gw := hgm.indicator hU
      have hgw0 : ∀ p, 0 ≤ gw p := fun p => by
        by_cases hp : p ∈ U
        · simpa only [gw, indicator_of_mem hp] using hg0 p
        · simp only [gw, indicator_of_notMem hp, le_refl]
      refine ⟨gw, ⟨hgw, hgw0, ?_⟩, ?_⟩
      · intro φ
        have hfun : (fun p => φ p * gw p) = U.indicator (fun p => φ p * g p) := by
          funext p
          by_cases hp : p ∈ U <;> simp [gw, hp]
        rw [hfun, integral_indicator hU, Measure.restrict_restrict_of_subset hUR, hchar φ]
        let F : PDE.Vec 1 → ℝ := fun v =>
          ∫ t : ElapsedTime (ENNReal.ofReal T), ∫ w, φ (t.1, w)
            ∂(intervalExtension hJ K).firstMarginal
              (wholeSpaceQuery σ (σ + t.1) (le_add_of_nonneg_right t.2.1.le) v 0)
            ∂elapsedVolume (ENNReal.ofReal T)
        have hFzero : ∀ v, v ∉ PDE.oneDimensionalAxisBox a c → F v = 0 := by
          intro v hv
          dsimp only [F]
          simp_rw [intervalExtension_first_outside hJ K σ _ _ v hv]
          simp only [integral_zero_measure, integral_zero]
        change _ = ∫ v, F v ∂ρ
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFzero,
          ← integral_subtype_comap hJ F]
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun v => ?_
        dsimp only [F]
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun t => ?_
        dsimp only
        rw [intervalExtension_first_inside,
          interval_firstMarginal_eq_parabolic hJ K B hp]
      · intro γ hγ1 hγ2
        have hγ2' : γ ≤ 2 := by norm_num [slabGamma0] at hγ2; exact hγ2
        obtain ⟨hgLp, hgBound⟩ := hb γ hγ1 hγ2'
        have hnorm : eLpNorm gw (ENNReal.ofReal γ)
            (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) =
            eLpNorm g (ENNReal.ofReal γ) (volume.restrict U) := by
          dsimp only [gw]
          rw [eLpNorm_indicator_eq_eLpNorm_restrict hU,
            Measure.restrict_restrict_of_subset hUR]
        have hgwLp : MemLp gw (ENNReal.ofReal γ)
            (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) := by
          change eLpNorm gw _ _ < ⊤
          rw [hnorm]
          exact hgLp.eLpNorm_lt_top
        refine ⟨hgwLp, ?_⟩
        have hbd : eLpNorm gw (ENNReal.ofReal γ)
            (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ≤
            ENNReal.ofReal (C γ * (ρ univ).toReal * T ^ slabBeta 1 γ) := by
          rw [hnorm]
          have hβ : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
            norm_num [slabBeta]
          rw [hβ, ENNReal.ofReal_mul (mul_nonneg (hC γ hγ1 hγ2') ENNReal.toReal_nonneg),
            ENNReal.ofReal_mul (hC γ hγ1 hγ2'),
            ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
          exact hgBound.trans (mul_le_mul' (mul_le_mul' le_rfl hρj) le_rfl)
        have hpos : 0 ≤ C γ * (ρ univ).toReal * T ^ slabBeta 1 γ :=
          mul_nonneg (mul_nonneg (hC γ hγ1 hγ2') ENNReal.toReal_nonneg)
            (Real.rpow_nonneg hT.le _)
        simpa only [ENNReal.toReal_ofReal hpos] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
    have interval_slab_fourier :
        ∃ C : ℝ → ℝ≥0, ∃ k : ℝ, 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
        (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
        (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ T : ℝ), 0 < T →
      ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
      [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
      ∃ g : SlabBase 1 → ℝ≥0∞, Measurable g ∧
        (slabMeasure 1 T Γ).fst = (slabBase 1 T).withDensity g ∧
        (∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → eLpNorm g (ENNReal.ofReal γ) (slabBase 1 T) ≤
          (C γ : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2))) ∧
        ∃ f : PDE.Vec 1 → SlabBase 1 → ℂ, Measurable (Function.uncurry f) ∧
        (∀ ξ, Integrable (f ξ) (slabBase 1 T) ∧
          ∀ E : Set (SlabBase 1), MeasurableSet E → ∫ y in E, f ξ y ∂slabBase 1 T =
            ∫ p in {p : GreenCarrier 1 | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
              Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
        ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 →
          (∀ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase 1 T) ≤
            (C γ : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2) *
              Real.exp (-k * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) ∧
          ENNReal.ofReal ((2 * Real.pi)⁻¹) *
              ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase 1 T) ≤
            (C γ : ℝ≥0∞) * μ univ *
              ENNReal.ofReal (T ^ (3 / (2 * γ) - 2) * Real.exp (-k * T)) := by
      obtain ⟨Co, hoc⟩ := intervalExtension_occupation
      obtain ⟨Cd, kd, hCd, hkd, hdec⟩ := intervalExtension_fourier_decay
      refine ⟨slabConstant' 1 Co Cd kd, kd / 2, div_pos hkd (by norm_num), ?_⟩
      intro a c hac B b hs hJ S K hr hlen σ T hT μ _ Γ hΓ
      let Kw := intervalExtension hJ K
      let μw := μ.map (intervalStateInclusion σ)
      have hc : IsTranslationCovariantEvolution (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
          MeasurableSet.univ Kw := intervalExtension_covariance hJ K
        (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
      have hcomp : Kw.HasComposition MeasurableSet.univ :=
        intervalExtension_composition hJ K hr.2.2.2
      have hΓw := intervalExtension_isGreenMeasure hJ K σ μ Γ hΓ
      obtain ⟨g, hgm, hgE, hgb, f, hfm, hfE, hfb⟩ := killed_slab_fourier_of_bounds
        (by norm_num) Kw hc hcomp Co (hoc m Lb hm hmLb a c hac B b hs hJ S K hr)
        Cd kd hCd hkd (hdec a c hac B b hs hJ S K hr hlen) σ μw Γ hΓw hT
      have hM : μw univ = μ univ := by
        dsimp only [μw]
        rw [Measure.map_apply (measurable_intervalStateInclusion σ) MeasurableSet.univ,
          preimage_univ]
      refine ⟨g, hgm, hgE, ?_, f, hfm, hfE, ?_⟩
      · intro γ hγ1 hγ2
        have h := hgb γ hγ1 (by norm_num [slabGamma0]; exact hγ2)
        simpa only [hM, interval_slab_beta] using h
      · intro γ hγ1 hγ2
        obtain ⟨hf, hfreq⟩ := hfb γ hγ1 (by norm_num [slabGamma0]; exact hγ2)
        constructor
        · intro ξ
          have h := hf ξ
          rw [hM, interval_slab_beta] at h
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
          simpa only [neg_mul, mul_assoc] using h
        · rw [hM, Nat.cast_one, interval_slab_height_exponent] at hfreq
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
          simpa [neg_mul, mul_assoc] using hfreq
    obtain ⟨C, k, hk, hfourier⟩ := interval_slab_fourier
    refine ⟨(slabConstant 1 q C : ℝ) + 1, k * (q - 1),
      by positivity, mul_pos hk (by linarith), ?_⟩
    intro a c hac B b hs hJ S K hr hlen σ T hT μ _ Γ hΓ
    obtain ⟨g, hgm, hgE, hgb, f, _hfm, hf, hfb⟩ :=
      hfourier a c hac B b hs hJ S K hr hlen σ T hT μ Γ hΓ
    have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq2
    have hγ1 := (slab_gamma_one_lt (d := 1) hq hqd).le
    have hγ2 : slabGamma 1 q ≤ 2 := by
      have := (slab_q_lt_gamma (d := 1) hq hqd).2.le
      norm_num [slabGamma0] at this
      exact this
    obtain ⟨G, hGm, hGE, hbd⟩ := killed_slab_reconstruction C k K σ μ Γ hΓ hq hq2 hT
      g hgm hgE (fun r h1 h2 => by
        have h2' : r ≤ 2 := by norm_num [slabGamma0] at h2; exact h2
        simpa only [interval_slab_beta] using hgb r h1 h2') f hf (by
        have he : slabBeta 1 (slabGamma 1 q) - 3 / 2 =
            3 / (2 * slabGamma 1 q) - 2 := by rw [interval_slab_beta]; ring
        simpa only [he] using
          (hfb (slabGamma 1 q) hγ1 hγ2).2)
    refine ⟨G, hGm, hGE, hbd.trans ?_⟩
    apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have interval_green_infinite_norm :
      ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ : ℝ),
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ = (greenLebesgue 1).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C * μ univ := by
    have hq' : q < 2 := by linarith
    have hq0 : 0 < q := by linarith
    have hδ : 0 < 3 - 2 * q := by linarith
    obtain ⟨A, k, _hA, hk, hslab⟩ := interval_slab_density hq'
    let N := killedGreenConstant A (3 - 2 * q) k q
    have hN : N ≠ ⊤ := killedGreenConstant_ne_top hδ hk hq0
    refine ⟨N.toReal + 1, k, by positivity, hk, ?_⟩
    intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
    have hloc : ∀ T : ℝ, ∃ G : GreenCarrier 1 → ℝ≥0∞, 0 < T →
        Measurable G ∧
        Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
        ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
          ENNReal.ofReal A * μ univ ^ q *
            ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-k * T)) := by
      intro T
      by_cases hT : 0 < T
      · obtain ⟨G, hG⟩ := hslab a c hac B b hs hJ S K hr hlen σ T hT μ Γ hΓ
        exact ⟨G, fun _ => hG⟩
      · exact ⟨0, fun h => absurd h hT⟩
    choose Gl hGl using hloc
    obtain ⟨G, hGm, hGE, hGae⟩ := exists_global_density K σ μ Γ hΓ Gl
      (fun T hT => (hGl T hT).1) (fun T hT => (hGl T hT).2.1)
    refine ⟨G, hGm, hGE, ?_⟩
    have hbd := killed_green_norm_bound G hGm A (3 - 2 * q) k q (μ univ) hq0 (by
      intro T hT
      calc ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1
          = ∫⁻ p in slabSet T, Gl T p ^ q ∂greenLebesgue 1 := by
            refine lintegral_congr_ae ?_
            filter_upwards [hGae T hT] with p hp
            rw [hp]
        _ ≤ _ := (hGl T hT).2.2)
    apply hbd.trans
    apply mul_le_mul' ?_ le_rfl
    calc N = ENNReal.ofReal N.toReal := (ENNReal.ofReal_toReal hN).symm
      _ ≤ ENNReal.ofReal (N.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨C, k, hC, _hk, hnorm⟩ := interval_green_infinite_norm
  obtain ⟨_Cm, _hCm, hmass⟩ := interval_green_finite_mass hH hLE
    lam Lam m Lb length hlam hlength
  refine ⟨C, hC, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
  obtain ⟨G, hGm, hGE, hGn⟩ := hnorm a c hac B b hs hJ S K hr hlen σ μ Γ hΓ
  exact ⟨G, hGm, hGE, hGn, (hmass a c hac B b hs hJ S K hr hlen σ μ Γ hΓ).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo TheoremA Evolution Parabolic Green
open scoped ENNReal NNReal






/-- Restrict literal physical C112 regularity to a smaller set. -/
theorem clock_C112_mono {u : Point → ℝ} {D E : Set Point}
    (hu : IsKineticC112On u D) (hi : E ⊆ D) : IsKineticC112On u E :=
  ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
    fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
    hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
    hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩


/-- The starting state for the normalized killed evolution has normalized transported coordinate
  zero. -/
def clockInitialState (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    EvolutionState (intervalDomain clockNormalizedInterval) (fun _ => 0) 0 :=
  ⟨((fun _ => (e.velocity 0 - c.vbar) / c.r), fun _ => 0), by
    refine ⟨?_, mem_univ _⟩
    change (fun _ : Fin 1 => (e.velocity 0 - c.vbar) / c.r) ∈
      movingDomain (intervalDomain clockNormalizedInterval) (fun _ => 0) 0
    rw [mem_movingDomain_iff, sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
    exact (c.mem_active_iff (e.velocity 0)).mp he⟩

/-- The normalized Green carrier measure is obtained from the actual, uniquely realized
  evolution. -/
def clockNativeGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure (GreenCarrier 1) :=
  greenMeasure (clockEvolution hH hLE hlam hLam A c e).2 0 ⊤ (by simp)
    (Measure.dirac (clockInitialState c e he))

/-- The normalized physical Green measure uses the established elapsed-to-physical coordinate
  map. -/
def clockGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure Point :=
  (clockNativeGreen hH hLE hlam hLam A c e he).map (elapsedPhysicalPoint 0)

/-- The actual normalized carrier measure has the exact canonical Green characterization. -/
theorem clockNativeGreen_spec
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsGreenMeasure (clockEvolution hH hLE hlam hLam A c e).2 0 ⊤
      (Measure.dirac (clockInitialState c e he))
      (clockNativeGreen hH hLE hlam hLam A c e he) :=
  greenMeasure_spec _ 0 ⊤ (by simp) _

/-- The landed interval theorem gives a uniform density for the actual normalized clock Green.
The constant depends only on ellipticity and the exponent, not on the clock or coefficient jets. -/
theorem clockNativeGreen_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active),
      ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
        clockNativeGreen hH hLE hlam hLam A c e he = (greenLebesgue 1).withDensity G ∧
        eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C ∧
        clockNativeGreen hH hLE hlam hLam A c e he univ < ⊤ := by
  obtain ⟨C, hC, hc⟩ := Interval.interval_green_density hH hLE
    (3 * lam / 5) (3 * Lam) (9 / 25) 9 (3 / 2)
    (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num) q hq hq2
  refine ⟨C, hC, ?_⟩
  intro A c e he
  obtain ⟨G, hm, hd, hn, hf⟩ := @hc (-3 / 4) (3 / 4) (by norm_num)
    (c.extendedCoefficient lam A.a e) c.extendedVectorDrift
    (c.extended_sourceSetting hlam hLam A e)
    (intervalDomain_measurable clockNormalizedInterval)
    (clockEvolution hH hLE hlam hLam A c e).1
    (clockEvolution hH hLE hlam hLam A c e).2
    (clockEvolution_spec hH hLE hlam hLam A c e) (by norm_num) 0
    (Measure.dirac (clockInitialState c e he)) isFiniteMeasure_dirac
    (clockNativeGreen hH hLE hlam hLam A c e he)
    (clockNativeGreen_spec hH hLE hlam hLam A c e he)
  have hm1 : (Measure.dirac (clockInitialState c e he)) univ = 1 :=
    Measure.dirac_apply_of_mem (mem_univ _)
  exact ⟨G, hm, hd, hn.trans (le_of_eq ((congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal C * x) hm1).trans
    (mul_one _))), hf⟩


/-- A weighted compact normalized probe expressed in physical coordinates. -/
def clockWeightedProbe (c : Clock) (e : Point) (f : exitProbeSubmodule) : Point → ℝ :=
  fun p => |p.velocity 0| * exitProbePhysical f (c.map e p)


/-- The literal full-test strip identity gives the weighted compact-probe integral.
All regularity, boundedness and the zero exit term are proved from the actual normalized solver. -/
theorem clock_weighted_test_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (R T U : ℝ) (hRT : R < T) (hU : e.time + 2 * c.r ^ 2 * R ≤ U)
    (ep : StripPole c.activeInterval (U : WithTop ℝ)) (hep : ep.1 = e)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval U ep) =
      (|c.vbar| * c.r ^ 2) * clockSourcePotential hH hLE hlam hLam A c e T f
        (sectionTwoPoint (c.map e e))     := by
  have closed_active_image (p : Point) (hp : p.velocity 0 ∈ Icc c.activeInterval.lo c.activeInterval.hi) :
      (sectionTwoPoint (c.map e p)).position ∈ closure (intervalDomain clockNormalizedInterval) := by
    apply (nested_intervalDomain_closure_iff clockNormalizedInterval _).mpr
    change -3 / 4 ≤ (p.velocity 0 - c.vbar) / c.r ∧
      (p.velocity 0 - c.vbar) / c.r ≤ 3 / 4
    constructor
    · apply (le_div_iff₀ c.positive).mpr
      have hh : c.vbar - 3 * c.r / 4 ≤ p.velocity 0 := hp.1
      linarith
    · apply (div_le_iff₀ c.positive).mpr
      have hh : p.velocity 0 ≤ c.vbar + 3 * c.r / 4 := hp.2
      linarith
  have clock_test_exit_zero :
      (∫ p, clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e p)) ∂stripExit hH hLE hlam hLam A c.activeInterval U ep) = 0 := by
    have clockSourcePotential_pullback_zero_faces (p : Point) (hp : p.velocity 0 = c.activeInterval.lo ∨
        p.velocity 0 = c.activeInterval.hi) :
        clockSourcePotential hH hLE hlam hLam A c e T f (sectionTwoPoint (c.map e p)) = 0 := by
      apply (clockSourcePotential_boundary hH hLE hlam hLam A c e R T hRT f hfn hs hz).2
      change (p.velocity 0 - c.vbar) / c.r = -3 / 4 ∨
        (p.velocity 0 - c.vbar) / c.r = 3 / 4
      rcases hp with hp | hp
      · left
        rw [hp]
        dsimp [Clock.activeInterval]
        field_simp [ne_of_gt c.positive]
        ring
      · right
        rw [hp]
        dsimp [Clock.activeInterval]
        field_simp [ne_of_gt c.positive]
        ring
    have hc := (clock_forward_cone_finite hH hLE hlam hLam A c U ep).1
    have hex : ∀ᵐ p ∂stripExit hH hLE hlam hLam A c.activeInterval U ep,
        p ∈ reconstructionExit c.activeInterval (ep.1.time - 1) U := by
      rw [ae_iff]
      exact (strip_exit_probability hH hLE hlam hLam A c.activeInterval
        (ep.1.time - 1) U ep (by linarith)).2.1
    apply integral_eq_zero_of_ae
    filter_upwards [hc, hex] with p hp hx
    rcases hx with hx | hx
    · have ht : R ≤ (c.map e p).time := by
        have hp' : p.time - e.time ≤ 2 * c.r ^ 2 * (c.map e p).time := by
          simpa only [hep] using hp
        have hsqr := sq_pos_of_pos c.positive
        rw [hx.1] at hp'
        nlinarith
      exact (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT
        f hfn hs hz).2.2.1 _ ht
    · exact clockSourcePotential_pullback_zero_faces p hx.2.2
  have clockSourcePotential_pullback_bounded :
      ∃ M : ℝ, ∀ p, p.velocity 0 ∈ c.active →
      |((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘
        c.map e) p| ≤ M ∧
      |forwardScalarOperator A.a
        ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘
          c.map e) p| ≤ M := by
    obtain ⟨C, -, hb⟩ :=
      (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz).1
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    let D := |c.vbar| * c.r ^ 2
    have hD : 0 < D := mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)
    refine ⟨max C ((3 * |c.vbar| / 2 / D) * max M 0), ?_⟩
    intro p hp
    refine ⟨(hb _).trans (le_max_left _ _), ?_⟩
    rw [clockSourcePotential_physical_equation hH hLE hlam hLam A c e R T hRT
      f hfn hs hz p hp, abs_mul, abs_neg,
      abs_of_nonneg (div_nonneg (abs_nonneg _) hD.le)]
    apply le_trans _ (le_max_right _ _)
    apply mul_le_mul
    · exact div_le_div_of_nonneg_right (c.active_abs_bounds hp).2 hD.le
    · exact (hM _).1.trans (le_max_left _ _)
    · exact abs_nonneg _
    · exact div_nonneg (by positivity) hD.le
  have clockSourcePotential_pullback_continuous :
      ContinuousOn
      ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ c.map e)
      {p | p.velocity 0 ∈ Icc c.activeInterval.lo c.activeInterval.hi} := by
    apply ((clockSourcePotential_boundary hH hLE hlam hLam A c e R T hRT f hfn hs hz).1).comp ((continuous_sectionTwoPoint 1).comp (c.homeomorph e).continuous).continuousOn
    intro p hp
    exact closed_active_image p hp
  let u := (clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ c.map e
  have hreg := clock_C112_mono (clock_pullback_C112 c e _ (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz).2.1)
    (show reconstructionStrip c.activeInterval (ep.1.time - 1) U ⊆
      {p | p.velocity 0 ∈ c.active} from fun _ hp => hp.2.2)
  obtain ⟨M, hM⟩ := clockSourcePotential_pullback_bounded
  have heU : ep.1.time < U := WithTop.coe_lt_coe.mp ep.2.1
  have hi := strip_identity_C112 hH hLE hlam hLam A c.activeInterval (ep.1.time - 1) U
    (by linarith) ep (by linarith) u hreg
    (clockSourcePotential_pullback_continuous.mono (fun p hp => (nested_strip_union_exit_subset_closed c.activeInterval
      c.activeInterval subset_rfl (ep.1.time - 1) U hp).2))
    ⟨M, fun p hp => hM p hp.2.2⟩
  have hzero := clock_test_exit_zero
  have hsource : (fun p => forwardScalarOperator A.a u p) =ᵐ[
      stripGreen hH hLE hlam hLam A c.activeInterval U ep]
      fun p => -(1 / (|c.vbar| * c.r ^ 2)) * clockWeightedProbe c e f p := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast c.activeInterval
      (stripEvolution hH hLE hlam hLam A c.activeInterval).2 U ep] with p hp
    exact (clockSourcePotential_physical_equation hH hLE hlam hLam A c e R T hRT
      f hfn hs hz p hp.2).trans (by dsimp [clockWeightedProbe]; ring)
  rw [integral_congr_ae hsource, integral_const_mul] at hi
  change u ep.1 = _ - _ at hi
  change (∫ p, u p ∂stripExit hH hLE hlam hLam A c.activeInterval U ep) = 0 at hzero
  rw [hzero] at hi
  have hv : |c.vbar| * c.r ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive))
  have heval : u ep.1 = clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e e)) := congrArg u hep
  rw [heval] at hi
  have hi' : clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e e)) =
      (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A
        c.activeInterval U ep) / (|c.vbar| * c.r ^ 2) := hi.trans (by ring)
  exact ((eq_div_iff hv).mp hi').symm.trans (mul_comm _ _)


/-- The physical normalized initial pole has time and transported coordinate zero. -/
def clockPhysicalPole (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    StripPole clockNormalizedInterval ⊤ :=
  ⟨⟨0, fun _ => 0, fun _ => (e.velocity 0 - c.vbar) / c.r⟩,
    WithTop.coe_lt_top _, (c.mem_active_iff (e.velocity 0)).mp he⟩


/-- The actual physical normalized Green is exactly the established strip map of the same kernel. -/
theorem clockGreen_eq_stripGreenOfKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    clockGreen hH hLE hlam hLam A c e he =
      stripGreenOfKernel clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e).2
        ⊤ (clockPhysicalPole c e he) := rfl

/-- Late vanishing identifies the genuine clock test value with the actual infinite Green
  integral. -/
theorem clockSourcePotential_eq_infinite_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active)
    (R T : ℝ) (hT : 0 < T) (hRT : R < T) (f : exitProbeSubmodule)
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    clockSourcePotential hH hLE hlam hLam A c e T f (sectionTwoPoint (c.map e e)) =
      ∫ p, exitProbePhysical f p ∂clockGreen hH hLE hlam hLam A c e he  := by
  have clock_map_pole :
      c.map e e = (clockPhysicalPole c e he).1 := by
    ext i <;> simp [Clock.map, clockPhysicalPole]
  let ep := stripPoleFinite clockNormalizedInterval (clockPhysicalPole c e he) T hT
  have hleft : clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e e)) = nestedSourcePotential clockNormalizedInterval
        (clockEvolution hH hLE hlam hLam A c e) T f ep.1 := by
    rw [clock_map_pole]
    rfl
  have hep : stripPoleInfinite clockNormalizedInterval T ep = clockPhysicalPole c e he :=
    Subtype.ext rfl
  have hm := (congrArg (fun μ : Measure Point => μ.restrict {p | p.time < T}) (congrArg (stripGreenOfKernel clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e).2 ⊤) hep)).trans
    (congrArg (fun μ : Measure Point => μ.restrict {p | p.time < T})
      (clockGreen_eq_stripGreenOfKernel hH hLE hlam hLam A c e he).symm)
  have hrestricted := (stripGreenOfKernel_horizonRestriction clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e).2 T ep).trans hm
  exact hleft.trans ((nestedSourcePotential_eq_green A clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e) T f ep).trans ((congrArg (fun μ : Measure Point =>
    ∫ p, exitProbePhysical f p ∂μ) hrestricted).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp =>
      hz p (hRT.le.trans (not_lt.mp hp))))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

