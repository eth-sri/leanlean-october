module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierBound
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier

/-! # Joint slab Fourier densities with killing retained

The shared measurable density construction and frequency scaling are reused.
The evolved initial mass supplies the extra exponential factor in both estimates.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal ProbabilityTheory

/-- Shared slab reconstruction inputs with the half-time killing factor retained. -/
theorem killed_slab_fourier_of_bounds {d : ℕ} (hd : 0 < d)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 )))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) _ MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hcdec : 0 < cdec)
    (hdec : ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d),
      totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤
        ENNReal.ofReal (Cdec * Real.exp (-cdec * (τ - σ) *
          (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))
    (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 )) σ₀))
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
              Complex.exp (-((PDE.vecDot ξ p.2.2 ) * Complex.I)) ∂Γ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        (∀ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ) * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))) ∧
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2)) *
            ENNReal.ofReal (Real.exp (-((cdec / 2) * T))) := by
  let sharedTerm_45ec3f8eb6 := ((((2 * Real.pi) ^ d)⁻¹))
  let sharedTerm_63f16c2046 := (((2 : ℝ) / 3))
  let sharedTerm_b01a63d765 := ((T ^ (-(3 * (d : ℝ) / 2))))
  let sharedTerm_47d9020fa7 := ((-((cdec / 2) * T)))
  obtain ⟨g, hgm, hgE, hgnorm⟩ := slab_marginal_density hd K hcov Cocc hocc σ₀ μ Γ hΓ hT
  have hΓfin : IsFiniteMeasure (Γ.restrict (slabSet  T)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  obtain ⟨kf, hkm, hkf⟩ := exists_measurable_fourier_family hd hT Γ g hgE
  have hk  :=
    fun ξ => killed_slab_fourier_density_bound K hd hcov hcomp Cocc hocc
      Cdec cdec hCdec σ₀ μ Γ hΓ hT ξ (kf ξ) (hkf ξ).1 (hkf ξ).2
      (killed_halfMeasure_mass_le K hcov Cdec cdec hdec σ₀ μ hT ξ)
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
  have hq0 : (0 : ℝ) ≤ sharedTerm_45ec3f8eb6 := by positivity
  have hF1 := one_le_slabK1_factor (d := d) hCdec cdec
  have hF2 : Cdec ≤ (1 + Cdec) * (1 + sharedTerm_45ec3f8eb6 * slabFreqConstant d (cdec / 2)) := by
    nlinarith [mul_nonneg hq0 hA0]
  have hK1 : ∀ γ : ℝ, slabK1 d Cdec cdec γ =
      (2 : ℝ) ^ slabBeta d γ * ((1 + Cdec) *
        (1 + sharedTerm_45ec3f8eb6 * slabFreqConstant d (cdec / 2))) := fun γ => by
    unfold slabK1; ring
  have hfam :
      (∀ ξ, Integrable (kf ξ) (slabBase d T) ∧
        ∀ E : Set (SlabBase d), MeasurableSet E →
          ∫ y in E, kf ξ y ∂slabBase d T =
            ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
              Complex.exp (-((PDE.vecDot ξ p.2.2 ) * Complex.I)) ∂Γ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        (∀ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ slabBeta d γ) * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ sharedTerm_63f16c2046))))) ∧
        ENNReal.ofReal sharedTerm_45ec3f8eb6 *
            ∫⁻ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (slabConstant' d Cocc Cdec cdec γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2)) *
            ENNReal.ofReal (Real.exp sharedTerm_47d9020fa7) := by
    refine ⟨fun ξ => ⟨(hkf ξ).1, (hkf ξ).2⟩, fun γ h1 h2 => ⟨fun ξ => ?_, ?_⟩⟩
    · have hC0  := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      refine (hk ξ γ h1 h2).trans ?_
      rw [hCγ γ h1 h2]
      have hle : ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) ≤
          ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK1]
        nlinarith [mul_nonneg hC0 h2b, mul_nonneg hC0 hCdec.le]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl) le_rfl
    · have hC0  := hocc.1 γ h1 h2
      have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
      have ht1 : 0 ≤ T ^ slabBeta d γ := Real.rpow_nonneg hT.le _
      have ht2 : 0 ≤ sharedTerm_b01a63d765 := Real.rpow_nonneg hT.le _
      let Q := ENNReal.ofReal (Real.exp sharedTerm_47d9020fa7)
      have hsplit (ξ : PDE.Vec d) : ENNReal.ofReal (Real.exp
          (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ sharedTerm_63f16c2046)))) =
          Q * ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ sharedTerm_63f16c2046))) := by
        rw [show -((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ sharedTerm_63f16c2046)) =
          sharedTerm_47d9020fa7 + -((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ sharedTerm_63f16c2046)
            by ring, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      set D : ℝ≥0∞ := ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
        ENNReal.ofReal (T ^ slabBeta d γ) * Q with hD
      have hDtop : D ≠ ⊤ := by
        rw [hD]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (measure_ne_top _ _)) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
      have hscale := lintegral_decayProfile_scaling d (cdec / 2) T hT
      calc ENNReal.ofReal sharedTerm_45ec3f8eb6 *
            ∫⁻ ξ, eLpNorm (kf ξ) (ENNReal.ofReal γ) (slabBase d T)
          ≤ ENNReal.ofReal sharedTerm_45ec3f8eb6 *
            ∫⁻ ξ : PDE.Vec d, D * ENNReal.ofReal (Real.exp
              (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ sharedTerm_63f16c2046))) :=
            mul_le_mul' le_rfl (lintegral_mono (fun ξ => by
              have h := hk ξ γ h1 h2
              rw [hsplit ξ] at h
              simpa only [hD, mul_assoc] using h))
        _ = ENNReal.ofReal sharedTerm_45ec3f8eb6 *
            (D * (ENNReal.ofReal sharedTerm_b01a63d765 *
              ENNReal.ofReal (slabFreqConstant d (cdec / 2)))) := by
            rw [lintegral_const_mul' D _ hDtop, hscale, hAeq]
        _ ≤ _ := by
            rw [hCγ γ h1 h2, hD, hM]
            have hrp : T ^ (slabBeta d γ - 3 * (d : ℝ) / 2) =
                T ^ slabBeta d γ * sharedTerm_b01a63d765 := by
              rw [← Real.rpow_add hT, sub_eq_add_neg]
            rw [hrp]
            convert mul_le_mul' (freq_ennreal (Cocc γ) Cdec ((2 : ℝ) ^ slabBeta d γ) M (T ^
              slabBeta d γ)
              sharedTerm_b01a63d765 (slabFreqConstant d (cdec / 2)) sharedTerm_45ec3f8eb6
              (slabK1 d Cdec cdec γ) _ hC0 hCdec.le h2b hM0 ht1 ht2 hA0 hq0
              (by unfold slabK1; ring) rfl) (le_rfl : Q ≤ Q) using 1; ring
  refine ⟨g, hgm, slabMeasure_fst T Γ g hgE, fun γ h1 h2 => ?_, kf, hkm, hfam⟩
  · have hC0  := hocc.1 γ h1 h2
    have h2b := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (slabBeta d γ)
    refine (hgnorm γ h1 h2).trans ?_
    rw [hCγ γ h1 h2]
    have hle : ENNReal.ofReal (Cocc γ * (2 : ℝ) ^ slabBeta d γ) ≤
        ENNReal.ofReal (Cocc γ * slabK1 d Cdec cdec γ) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hK1]
      nlinarith [mul_nonneg hC0 h2b]
    exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl


end HypoellipticAleksandrov.KineticAleksandrov.Interval
