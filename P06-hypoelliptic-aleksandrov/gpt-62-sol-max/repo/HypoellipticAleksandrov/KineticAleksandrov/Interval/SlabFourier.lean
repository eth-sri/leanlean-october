module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierGreen

/-! # The interval slab Fourier theorem

Occupation, killing and frequency decay are discharged by their proved interval
lemmas. The only hypotheses are the explicit analytic inputs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal

/-- The scalar slab exponent is the literal exponent in case I. -/
theorem interval_slab_beta (γ : ℝ) : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
  norm_num [slabBeta]

/-- Integrating frequencies gives the scalar slab height exponent. -/
theorem interval_slab_height_exponent (γ : ℝ) :
    slabBeta 1 γ - 3 * (1 : ℝ) / 2 = 3 / (2 * γ) - 2 := by
  rw [interval_slab_beta]
  ring

/-- Uniform interval slab Fourier densities, with both killing and frequency decay. -/
theorem interval_slab_fourier
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length) :
    ∃ C : ℝ → ℝ≥0, ∃ k : ℝ, 0 < k ∧
    ∀ (E : IntervalEvolution lam Lam m Lb),
    E.length = length → ∀ (σ T : ℝ), 0 < T →
    ∀ (μ : Measure (EvolutionState (E.domain) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure E.kernel σ ⊤ μ Γ →
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
  obtain ⟨Co, hoc⟩ := intervalExtension_occupation lam Lam hlam hlamLam
  obtain ⟨Cd, kd, hCd, hkd, hdec⟩ := intervalExtension_fourier_decay
    lam Lam m Lb length hlam hlamLam hm hmLb hlength
  refine ⟨slabConstant' 1 Co Cd kd, kd / 2, div_pos hkd (by norm_num), ?_⟩
  intro E hlen σ T hT μ _ Γ hΓ
  let Kw := intervalExtension E.measurableSet E.kernel
  let μw := μ.map (intervalStateInclusion σ)
  have hc : IsTranslationCovariantEvolution (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
      MeasurableSet.univ Kw := intervalExtension_covariance E.measurableSet E.kernel
    (E.clauses).2.2
  have hcomp : Kw.HasComposition MeasurableSet.univ :=
    intervalExtension_composition E.measurableSet E.kernel E.realizes.2.2.2
  have hΓw := intervalExtension_isGreenMeasure E.measurableSet E.kernel σ μ Γ hΓ
  obtain ⟨g, hgm, hgE, hgb, f, hfm, hfE, hfb⟩ := slab_fourier_of_halfMass
    (by norm_num) Kw hc hcomp Co (hoc E)
    Cd kd 1 hCd hkd σ μw Γ hΓw hT (fun ξ => halfMeasure_mass_le Kw hc σ μw hT ξ fun v => by
      have h := hdec E hlen σ (σ + T / 2) (le_halfTime σ T hT.le) ξ v
      simpa only [show σ + T / 2 - σ = T / 2 by ring, neg_mul,
        show (kd / 2) * T = kd * (T / 2) by ring] using h)
  have hM : μw univ = μ univ := by
    dsimp only [μw]
    rw [Measure.map_apply (measurable_intervalStateInclusion σ) MeasurableSet.univ,
      preimage_univ]
  refine ⟨g, hgm, slabMeasure_fst T Γ g hgE, ?_, f, hfm, hfE, ?_⟩
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
    · rw [hM, Nat.cast_one, interval_slab_height_exponent, mul_one] at hfreq
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
      simpa only [pow_one, neg_mul, mul_assoc] using hfreq

end HypoellipticAleksandrov.KineticAleksandrov.Interval
