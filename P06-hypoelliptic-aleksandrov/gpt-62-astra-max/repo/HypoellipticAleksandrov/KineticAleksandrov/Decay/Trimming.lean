module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Common marginal trimming

Two finite measures `E₁, E₂` on `Vec d × Vec d` whose sum is dominated by `M`, and whose
first marginals both dominate a measure `Θ`, can be *trimmed* to measures `F₁ ≤ E₁`, `F₂ ≤ E₂`
that have first marginal exactly `Θ` and still satisfy `F₁ + F₂ ≤ M`.  The trimming is the
weighted restriction `Fᵢ = Eᵢ.withDensity (gᵢ ∘ Prod.fst)`, where `gᵢ` is a measurable
Radon-Nikodym density of `Θ` with respect to the first marginal of `Eᵢ`.  It is not a
restriction to a set.  No integrability premise is needed: all measures are finite and the
densities are bounded by one almost everywhere.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open MeasureTheory Set
open scoped ENNReal

/-- The first marginal of `E.withDensity (g ∘ Prod.fst)` is the first marginal of `E`
reweighted by `g`. -/
theorem map_fst_withDensity_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E : Measure (α × β)) (g : α → ℝ≥0∞) (hg : Measurable g) :
    (E.withDensity (g ∘ Prod.fst)).map Prod.fst = (E.map Prod.fst).withDensity g := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA, Measure.restrict_map measurable_fst hA,
    lintegral_map hg measurable_fst]
  rfl

/-- One trimming step: a measure below the first marginal of a finite measure `E` is the
first marginal of a trimmed `F ≤ E`. -/
theorem exists_trimming_of_le_map_fst {d : ℕ}
    (E : Measure (EvolutionAmbientState d)) [IsFiniteMeasure E]
    (Θ : Measure (PDE.Vec d)) (hΘ : Θ ≤ E.map Prod.fst) :
    ∃ g : PDE.Vec d → ℝ≥0∞, Measurable g ∧ (∀ᵐ w ∂E.map Prod.fst, g w ≤ 1) ∧
      Θ = (E.map Prod.fst).withDensity g ∧
      (E.withDensity (g ∘ Prod.fst)).map Prod.fst = Θ ∧
      E.withDensity (g ∘ Prod.fst) ≤ E := by
  have : IsFiniteMeasure Θ := isFiniteMeasure_of_le _ hΘ
  have hac : Θ ≪ E.map Prod.fst := Measure.absolutelyContinuous_of_le hΘ
  have hle : ∀ᵐ w ∂E.map Prod.fst, Θ.rnDeriv (E.map Prod.fst) w ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hΘ] with w hw using hw
  have hΘeq : Θ = (E.map Prod.fst).withDensity (Θ.rnDeriv (E.map Prod.fst)) :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  have hmeas : Measurable (Θ.rnDeriv (E.map Prod.fst)) := Measure.measurable_rnDeriv _ _
  refine ⟨Θ.rnDeriv (E.map Prod.fst), hmeas, hle, hΘeq, ?_, ?_⟩
  · rw [map_fst_withDensity_comp_fst E _ hmeas]
    exact hΘeq.symm
  · have hae : ∀ᵐ x ∂E, (Θ.rnDeriv (E.map Prod.fst) ∘ Prod.fst) x ≤ 1 :=
      ae_of_ae_map measurable_fst.aemeasurable hle
    calc E.withDensity (Θ.rnDeriv (E.map Prod.fst) ∘ Prod.fst)
        ≤ E.withDensity (fun _ => 1) := withDensity_mono hae
      _ = E := withDensity_one

end HypoellipticAleksandrov.KineticAleksandrov.Decay
