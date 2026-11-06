module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakSupport
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-! # Positive compact-test weights for bounded-source weak testing -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

/- The positive part of a compact test defines a positive source measure. -/
def sourcePositiveMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  volume.withDensity (fun q => ENNReal.ofReal (max (Λ q) 0))

/- Integrable positive parts give finite test weights. -/
theorem sourcePositiveMeasure_isFinite (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    IsFiniteMeasure (sourcePositiveMeasure Λ) := by
  have hint : Integrable (fun q => max (Λ q) 0) :=
    (hΛ.max continuous_const).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun r : ℝ => max r 0) (max_self 0))
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun q => le_max_right (Λ q) 0)]
  exact ENNReal.ofReal_ne_top

/- The same test weight on physical starting points uses the coordinate equivalence. -/
def sourcePositiveStartMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ) :
    Measure (KineticPoint d) :=
  (sourcePositiveMeasure Λ).map (KineticPoint.equivProd d).symm

/- Positive compact test weights are finite also in the starting-point carrier. -/
theorem sourcePositiveStartMeasure_isFinite (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Continuous Λ) (hc : HasCompactSupport Λ) :
    IsFiniteMeasure (sourcePositiveStartMeasure Λ) := by
  have := sourcePositiveMeasure_isFinite Λ hΛ hc
  unfold sourcePositiveStartMeasure
  infer_instance

/- Integrals against positive test weights are the ordinary weighted integrals. -/
theorem integral_sourcePositiveMeasure (Λ : ℝ × EvolutionAmbientState d → ℝ)
    (hΛ : Measurable Λ) (f : ℝ × EvolutionAmbientState d → ℝ) :
    (∫ q, f q ∂sourcePositiveMeasure Λ) = ∫ q, max (Λ q) 0 * f q := by
  unfold sourcePositiveMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((hΛ.max measurable_const).ennreal_ofReal)
    (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

/- A starting-coordinate weight integrates by the literal coordinate permutation. -/
theorem integral_boundedSourceAction_positive_potential
    {Ω γ}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (Λ : ℝ × EvolutionAmbientState d → ℝ) (hΛ : Continuous Λ)
    (hc : HasCompactSupport Λ) (a T : ℝ) (hfloor : ∀ q, Λ q ≠ 0 → a ≤ q.1)
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M ) (hM : 0 ≤ M) (hb : ∀ p, |g p| ≤ M) :
    (∫ q, g ⟨q.1, q.2.1, q.2.2⟩
      ∂boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T) =
      ∫ q, max (Λ q) 0 * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ := by
  have _h_inl_17 : (∫ q, g ⟨q.1, q.2.1, q.2.2⟩
      ∂boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T) =
      ∫ q, max (Λ q) 0 *
        (∫ r in Ioo a T, duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r) := by
    have := sourcePositiveStartMeasure_isFinite Λ hΛ hc
    rw [integral_boundedSourceActionMeasure K hΩ hγ _ a T g hg M hM hb]
    have _h_inl_16 : Measurable (fun p => ∫ r in Ioo a T, duhamelIntegrand K g p r) := by
        exact (
      ((measurable_duhamelIntegrand K hΩ hγ g hg).stronglyMeasurable.integral_prod_right'
          (ν := volume.restrict (Ioo a T))).measurable
      )
    have hΛ : Measurable Λ := hΛ.measurable
    unfold sourcePositiveStartMeasure
    rw [integral_map (KineticPoint.measurable_equivProd_symm d).aemeasurable
      _h_inl_16.aestronglyMeasurable]
    exact integral_sourcePositiveMeasure Λ hΛ _
  rw [_h_inl_17]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change max (Λ q) 0 *
    (∫ r in Ioo a T, duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r) =
      max (Λ q) 0 * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
  by_cases hq : Λ q = 0
  · simp only [hq, max_self, zero_mul]
  · rw [duhamelPotential_eq_integral_window K g ⟨q.1, q.2.1, q.2.2⟩ (hfloor q hq)]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
