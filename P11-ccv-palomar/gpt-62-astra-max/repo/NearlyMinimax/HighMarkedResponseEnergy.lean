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

theorem finite_probability_pi_embedding_preserving {I J α : Type*}
    [Fintype I] [Fintype J] [MeasurableSpace α]
    (μ : J → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (e : I ↪ J) :
    MeasurePreserving (fun y => fun l => y (e l))
      (Measure.pi μ) (Measure.pi (fun l => μ (e l))) := by
  have hc : iIndepFun (fun j y => y j) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  refine ⟨(by fun_prop), ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map
    (fun l => (measurable_pi_apply (e l)).aemeasurable)).mp (iIndepFun.precomp e.injective hc)
  simpa only [(measurePreserving_eval μ _).map_eq] using he

theorem high_marked_selected_response_energy {ι E : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace E] {n r : ℕ} {e : Fin r ↪ Fin n}
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    {p : Fin n → ℝ} {pReset : E → Fin n → ℝ} (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    let score := highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e) cReset (g ∘ e) (w ∘ e) (φ ∘ e) c
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure (coefficientRegression η g w φ c i) V ha
        (fun b => (hp i b).le))) =
    ∫ y, score y ^ 2
      ∂Measure.pi (fun l => ternaryIndexMeasure
        (coefficientRegression η (g ∘ e) (w ∘ e) (φ ∘ e) c l) V ha (fun b => (hp (e l) b).le)) := by
  intro score
  let μ i := ternaryIndexMeasure _ V ha (fun b => (hp i b).le)
  have hpres := finite_probability_pi_embedding_preserving μ e
  let H  := fun y =>
    score y ^ 2
  calc
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact congrArg (fun z => z ^ 2)
        (high_marked_local_score_selected π activation cReset y hpd hp hw hReset)
    _ = _ :=
      (integral_map hpres.measurable.aemeasurable (measurable_of_countable H).aestronglyMeasurable).symm.trans
        (congrArg (fun M => ∫ y, H y ∂M) hpres.map_eq)
    _ = _ := rfl

end NearlyMinimax
