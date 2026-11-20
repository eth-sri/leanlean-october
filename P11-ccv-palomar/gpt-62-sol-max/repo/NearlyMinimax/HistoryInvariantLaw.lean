module

public import NearlyMinimax.HistoryInvariantObservable


@[expose] public section

/-!
# Invariant pushforward law from actual conditional signed update annihilation
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Actual weak transport and local signed annihilation prove equality of pushforward laws.
The hypothesis is the local packet integral for indicators; law invariance is the conclusion. -/
theorem historyMarkedPrior_invariant_law {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {X : Type*} [MeasurableSpace X]
    (f : HistoryMarked dependent E → X) (hf : Measurable f)
    (hkill : ∀ j h S, MeasurableSet S →
      ∫ e, (S.indicator (fun _ : X => (1 : ℝ)))
        (f (historyMarkedAppend dependent P.symm j (h, e))) * a e ∂π = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Measure.map f (historyMarkedPrior dependent Δ t π a) =
      Measure.map f (historyMarkedReference dependent Δ π) := by
  let := P.probability ht
  let := P.reference_probability
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  let F := (f ⁻¹' S).indicator (fun _ : HistoryMarked dependent E => (1 : ℝ))
  have hF := (measurable_const : Measurable (fun _ : HistoryMarked dependent E => (1 : ℝ))).indicator (hf hS)
  have hbound : ∀ h, |F h| ≤ 1 := by
    intro h
    by_cases hh : f h ∈ S <;> simp [F, hh]
  have hzero : ∀ j h, ∫ e, F (historyMarkedAppend dependent P.symm j (h, e)) * a e ∂π = 0 := by
    tauto
  have he := historyMarkedPrior_invariant_observable P F hF 1 (by norm_num) hbound hzero ht
  change (∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h
    ∂historyMarkedPrior dependent Δ t π a) =
      ∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h
        ∂historyMarkedReference dependent Δ π at he
  rw [integral_indicator_one (hf hS), integral_indicator_one (hf hS)] at he
  exact he

end NearlyMinimax
