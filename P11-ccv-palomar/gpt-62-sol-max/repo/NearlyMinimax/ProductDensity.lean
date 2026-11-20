module

public import NearlyMinimax.ConditionalLaw

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax

/-! Density tensorization for a finite iid product. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- Projection onto distinct finite coordinates preserves the corresponding product law. -/
theorem finite_probability_pi_embedding_preserving {I J α : Type*}
    [Fintype I] [Fintype J] [MeasurableSpace α]
    (μ : J → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (e : I ↪ J) :
    MeasurePreserving (fun y : J → α => fun l => y (e l))
      (Measure.pi μ) (Measure.pi (fun l => μ (e l))) := by
  have hc : iIndepFun (fun j (y : J → α) => y j) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ : J => (id : α → α)) (fun _ => aemeasurable_id)
  have hs := iIndepFun.precomp e.injective hc
  have hm : Measurable (fun y : J → α => fun l => y (e l)) :=
    measurable_pi_iff.mpr (fun l => measurable_pi_apply (e l))
  refine ⟨hm, ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map
    (fun l => (measurable_pi_apply (e l)).aemeasurable)).mp hs
  simpa only [(measurePreserving_eval μ _).map_eq] using he

section
variable {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f))
include hf hprob

theorem fintype_probability_pi_withDensity :
    Measure.pi (fun _ : κ => μ.withDensity f) =
      (Measure.pi (fun _ : κ => μ)).withDensity (fun x => ∏ i, f (x i)) := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator]
  · have he (x : κ → α) :
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
          ∏ i, (s i).indicator f (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp_all
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, (s j).indicator f (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)
        rw [hz]
        simp_all
    simp_rw [he]
    let G : κ → α → ℝ≥0∞ := fun i => (s i).indicator f
    have hG : ∀ i, Measurable (G i) := fun i => hf.indicator (hs i)
    change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ : κ => μ)) = _
    rw [lintegral_coordinate_product _ G hG]
    simp_rw [G, lintegral_indicator (hs _), withDensity_apply f (hs _)]
  · exact MeasurableSet.univ_pi hs

end
end NearlyMinimax
