module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierDomination

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green
section

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

/-- A density `k` with `‖∫_E k‖ ≤ ∫_E ĝ` for all measurable `E` satisfies `‖k‖ ≤ ĝ` a.e. -/
theorem ae_enorm_le_of_setIntegral_enorm_le {α : Type*} [MeasurableSpace α] (m : Measure α)
    [SigmaFinite m] (k : α → ℂ) (hk : Integrable k m) (G : α → ℝ≥0∞)
    (h : ∀ E, MeasurableSet E → ‖∫ y in E, k y ∂m‖ₑ ≤ ∫⁻ y in E, G y ∂m) :
    ∀ᵐ y ∂m, ‖k y‖ₑ ≤ G y := by
  have hle : (m.withDensityᵥ k).variation ≤ m.withDensity G := by
    refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
    rw [withDensityᵥ_apply hk hE, withDensity_apply _ hE]
    exact h E hE
  rw [(Measure.variation_withDensityᵥ hk)] at hle
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hk.aestronglyMeasurable.enorm
    (fun E hE _ => ?_)
  have := Measure.le_iff.1 hle E hE
  rwa [withDensity_apply _ hE, withDensity_apply _ hE] at this


variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))

/-- **Lemma 5.1: pointwise domination of any density `k^ξ`.**
`gξ` is the occupation density of `|η_T^ξ|` (start time `σ₀ + T/2`, horizon `3T/2`); `k` is any
integrable density of the Fourier marginal. -/
theorem slab_fourier_ae_bound
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (gξ : ℝ × PDE.Vec d → ℝ)
    (hgξ : SlabOccupationDensity K (σ₀ + T / 2) (3 * T / 2)
      (halfMeasure K σ₀ T hT.le μ ξ).variation gξ)
    (hint : Integrable gξ (volume.restrict (Ioo (0 : ℝ) (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))))
    (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T))
    (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) :
    ∀ᵐ y ∂slabBase d T, ‖k y‖ₑ ≤ ENNReal.ofReal (gξ (slabShift d (T / 2) y)) := by
  have hρfin : IsFiniteMeasure (halfMeasure K σ₀ T hT.le μ ξ).variation :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  refine ae_enorm_le_of_setIntegral_enorm_le (slabBase d T) k hk _ (fun E hE => ?_)
  rw [hkE E hE]
  refine (slab_domination_ineq K hcov hcomp σ₀ μ Γ hΓ hT ξ hE).trans (le_of_eq ?_)
  exact (slab_occupation_identity K (σ₀ + T / 2) (T / 2) T (3 * T / 2) (by linarith) hT
    (by linarith) (by linarith) _ gξ hgξ hint hE).symm

end

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))



/-- `β_γ ≥ 0` for `1 ≤ γ ≤ γ₀`. -/
lemma slabBeta_nonneg {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ slabGamma0 d) :
    0 ≤ slabBeta d γ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ : 0 < γ := by linarith
  have h1 : (d : ℝ) * γ ≤ d + 1 := by
    have := (le_div_iff₀ hd').1 hγ2
    linarith
  unfold slabBeta
  have : (d : ℝ) / 2 ≤ ((d : ℝ) + 2) / (2 * γ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

/-- Real arithmetic of the `L^γ` bound for `k^ξ`. -/
lemma fourier_bound_arith (Cocc Cdec M E β T ρm : ℝ) (hC : 0 ≤ Cocc) (hCd : 0 ≤ Cdec)
    (hM : 0 ≤ M) (hE : 0 ≤ E) (hT : 0 < T) (hβ : 0 ≤ β) (hρ : ρm ≤ M * (Cdec * E)) :
    Cocc * ρm * (3 * T / 2) ^ β ≤ (Cocc * Cdec * (2 : ℝ) ^ β) * M * T ^ β * E := by
  have h32 : (3 * T / 2) ^ β = (3 / 2 : ℝ) ^ β * T ^ β := by
    rw [show 3 * T / 2 = (3 / 2) * T by ring, Real.mul_rpow (by norm_num) hT.le]
  have h2 : (3 / 2 : ℝ) ^ β ≤ 2 ^ β := Real.rpow_le_rpow (by norm_num) (by norm_num) hβ
  have hT' : 0 ≤ T ^ β := Real.rpow_nonneg hT.le _
  have h3 : 0 ≤ (3 / 2 : ℝ) ^ β := Real.rpow_nonneg (by norm_num) _
  calc Cocc * ρm * (3 * T / 2) ^ β
      ≤ Cocc * (M * (Cdec * E)) * ((3 / 2 : ℝ) ^ β * T ^ β) := by
        rw [h32]
        gcongr
    _ ≤ Cocc * (M * (Cdec * E)) * (2 ^ β * T ^ β) := by gcongr
    _ = (Cocc * Cdec * 2 ^ β) * M * T ^ β * E := by ring


/-- **Lemma 5.1.**  Any integrable density `k^ξ` of the Fourier marginal
satisfies `‖k^ξ‖_{L^γ} ≤ C_γ C 2^{β_γ} M T^{β_γ} exp(-(c/2) T |ξ|^{2/3})` for `1 ≤ γ ≤ γ₀`
(`C_γ` the occupation constant, `C, c` the decay constants). -/
theorem slab_fourier_density_bound (hd : 0 < d)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hdec : FourierDecayBoundedBy K Cdec cdec) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T))
    (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) :
    ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))  := by
  have halfMeasure_mass_le (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) σ₀)) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) :
      (halfMeasure K σ₀ T hT.le μ ξ).variation univ ≤
      μ univ * ENNReal.ofReal (Cdec * Real.exp
        (-(cdec * (T / 2) * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) := by
    unfold halfMeasure
    refine evolved_variation_le μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
      (measurable_halfVelocity _) _ (fun x => ?_)
    refine (fibreMeasure_variation_le K hcov σ₀ _ (le_halfTime σ₀ T hT.le) ξ x).trans ?_
    have hlt : σ₀ < σ₀ + T / 2 := by linarith
    have h := hdec σ₀ (σ₀ + T / 2) hlt x.1.1 ξ
    have he : σ₀ + T / 2 - σ₀ = T / 2 := by ring
    rwa [he] at h
  intro γ hγ1 hγ2
  have hρfin : IsFiniteMeasure (halfMeasure K σ₀ T hT.le μ ξ).variation :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
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
    refine eLpNorm_mono_enorm_ae
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
  -- step 3: arithmetic
  set E : ℝ := Real.exp (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hmass := halfMeasure_mass_le σ₀ μ hT ξ
  have hrho : ((halfMeasure K σ₀ T hT.le μ ξ).variation univ).toReal ≤
      (μ univ).toReal * (Cdec * E) := by
    have hexp : Real.exp (-(cdec * (T / 2) * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))) = E := by
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
  exact h1.trans ((eLpNorm_slabShift_le gξ hgξ.1 hgξ.2.1 (T / 2) T (3 * T / 2) γ Cn hT.le (by linarith) (by linarith) hbd').trans hfinal)

end HypoellipticAleksandrov.KineticAleksandrov.Green

