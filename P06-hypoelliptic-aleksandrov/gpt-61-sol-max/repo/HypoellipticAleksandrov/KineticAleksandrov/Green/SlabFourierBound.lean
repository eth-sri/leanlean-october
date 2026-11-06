module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierDensity

/-!
# `L^γ` bound of the Fourier marginal density (Lemma 5.1)

Given the occupation estimate and the decay estimate for the realized kernel, the density `k^ξ`
of the Fourier marginal satisfies
`‖k^ξ‖_{L^γ} ≤ C_γ C M T^{β_γ} 2^{β_γ} exp(-(c/2) T |ξ|^{2/3})` for `1 ≤ γ ≤ γ₀`.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ProbabilityTheory

variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 )))

/-- The mass of `|η_T^ξ|` is at most `M · C exp(-c (T/2) |ξ|^{2/3})`. -/
theorem halfMeasure_mass_le
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) _ MeasurableSet.univ K)
    (Cdec cdec : ℝ) (hdec : FourierDecayBoundedBy K Cdec cdec) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 )) σ₀))
    [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) :
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
  rw [he] at h
  exact h


/-- `β_γ ≥ 0` for `1 ≤ γ ≤ γ₀`. -/
lemma slabBeta_nonneg {d : ℕ} (hd : 0 < d) {γ : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ slabGamma0 d) :
    0 ≤ slabBeta d γ := by


  have h1 : (d : ℝ) * γ ≤ d + 1 := by
    have := (le_div_iff₀ (by exact_mod_cast hd)).1 hγ2
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
  let sharedTerm_9a320e2cb4 := ((3 / 2 : ℝ) ^ β)
  have h32 : (3 * T / 2) ^ β = sharedTerm_9a320e2cb4 * T ^ β := by
    rw [show 3 * T / 2 = (3 / 2) * T by ring, Real.mul_rpow (by norm_num) hT.le]
  have h2 : sharedTerm_9a320e2cb4 ≤ (2 : ℝ) ^ β := Real.rpow_le_rpow (by norm_num) (by norm_num) hβ


  calc Cocc * ρm * (3 * T / 2) ^ β
      ≤ Cocc * (M * (Cdec * E)) * (sharedTerm_9a320e2cb4 * T ^ β) := by
        rw [h32]
        gcongr
    _ ≤ Cocc * (M * (Cdec * E)) * ((2 : ℝ) ^ β * T ^ β) := by gcongr
    _ = (Cocc * Cdec * (2 : ℝ) ^ β) * M * T ^ β * E := by ring


/-- **Lemma 5.1.**  Any integrable density `k^ξ` of the Fourier marginal
satisfies `‖k^ξ‖_{L^γ} ≤ C_γ C 2^{β_γ} M T^{β_γ} exp(-(c/2) T |ξ|^{2/3})` for `1 ≤ γ ≤ γ₀`
(`C_γ` the occupation constant, `C, c` the decay constants). -/
theorem slab_fourier_density_bound (hd : 0 < d)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) _ MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec) (hdec : FourierDecayBoundedBy K Cdec cdec) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 )) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T))
    (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 ) * Complex.I)) ∂Γ) :
    ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) := by
  let sharedTerm_f8fbec2ace := ((volume.restrict (Ioo (0 : ℝ) (3 * T / 2) ×ˢ (univ : PDE.VelocityRegion d))))
  let sharedTerm_d8bdc6ee64 := ((halfMeasure K σ₀ T hT.le μ ξ))
  let sharedTerm_b5a1d8e446 := (PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))
  intro γ hγ1 hγ2
  have hρfin : IsFiniteMeasure sharedTerm_d8bdc6ee64.variation :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  obtain ⟨gξ, hgξ, hnorm⟩ := hocc.2 sharedTerm_d8bdc6ee64.variation (σ₀ + T / 2)
    (3 * T / 2) (by positivity)
  have hint : Integrable gξ
      sharedTerm_f8fbec2ace := by
    have := (hnorm 1 le_rfl (one_le_slabGamma0 hd)).1
    rw [ENNReal.ofReal_one] at this
    exact memLp_one_iff_integrable.1 this

  obtain ⟨hmem, hbd⟩ := hnorm γ hγ1 hγ2
  have hC0  := hocc.1 γ hγ1 hγ2
  have hβ := slabBeta_nonneg hd hγ1 hγ2
  -- step 1: domination

  -- step 2: the occupation bound
  set Cn : ℝ := Cocc γ * (sharedTerm_d8bdc6ee64.variation univ).toReal *
    (3 * T / 2) ^ slabBeta d γ with hCn

  have h2 := eLpNorm_slabShift_le gξ hgξ.1 hgξ.2.1 (T / 2) T (3 * T / 2) γ Cn hT.le
    (by linarith) (by linarith) (show _ by
        rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
        exact ENNReal.ofReal_le_ofReal hbd)
  -- step 3: arithmetic
  set E : ℝ := Real.exp (-((cdec / 2) * T * sharedTerm_b5a1d8e446)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hmass := halfMeasure_mass_le K hcov Cdec cdec hdec σ₀ μ hT ξ
  have hrho : (sharedTerm_d8bdc6ee64.variation univ).toReal ≤
      (μ univ).toReal * (Cdec * E) := by
    have hexp : Real.exp (-(cdec * (T / 2) * sharedTerm_b5a1d8e446)) = E := by
      rw [hE]; congr 1; ring
    rw [hexp] at hmass

    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top) hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this


  exact (show eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
      eLpNorm (fun y => ENNReal.ofReal (gξ (slabShift d (T / 2) y))) (ENNReal.ofReal γ)
        (slabBase d T) by
      refine eLpNorm_mono_enorm_ae (f := k)
        (g := fun y => ENNReal.ofReal (gξ (slabShift d (T / 2) y))) hk.aestronglyMeasurable ?_
      filter_upwards [(slab_fourier_ae_bound K hcov hcomp σ₀ μ Γ hΓ hT ξ gξ hgξ hint k hk hkE)] with y hy
      rwa [enorm_eq_self]).trans (h2.trans (by
      refine (ENNReal.ofReal_le_ofReal (fourier_bound_arith _ _ _ _ _ _ _ hC0 hCdec.le ENNReal.toReal_nonneg hE0 hT hβ hrho)).trans (le_of_eq ?_)

      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC0 hCdec.le) (Real.rpow_nonneg (by norm_num) _)), ENNReal.ofReal_toReal (measure_ne_top _ _)]))

end HypoellipticAleksandrov.KineticAleksandrov.Green
