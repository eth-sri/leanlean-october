module

public import NearlyMinimax.HighMarkedSelection
public import NearlyMinimax.SpatialPairProductIntegration


@[expose] public section

/-! Actual response-product marginalization for the selected complete
marked score. Unused responses integrate to one under the true ternary
probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem high_marked_selected_response_energy {ι E : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace E] {n r : ℕ} (e : Fin r ↪ Fin n)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
        (fun b => (hp i b).le))) =
    ∫ y, highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
      ∂Measure.pi (fun l => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ e) (w ∘ e) (φ ∘ e) c l) V ha (fun b => (hp (e l) b).le)) := by
  let μ (i : Fin n) := ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
    (fun b => (hp i b).le)
  have hpres := finite_probability_pi_embedding_preserving μ e
  let H := fun y =>
    highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
  have hHm := measurable_of_countable H
  calc
    _ = ∫ y, H (fun l => y (e l)) ∂Measure.pi μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact congrArg (fun z : ℝ => z ^ 2)
        (high_marked_local_score_selected e π activation a V η p pReset cReset g w φ c y hpd hp hw hReset)
    _ = ∫ y, H y ∂Measure.pi (fun l => μ (e l)) :=
      (integral_map hpres.measurable.aemeasurable hHm.aestronglyMeasurable).symm.trans
        (congrArg (fun M => ∫ y, H y ∂M) hpres.map_eq)
    _ = _ := rfl

end NearlyMinimax
