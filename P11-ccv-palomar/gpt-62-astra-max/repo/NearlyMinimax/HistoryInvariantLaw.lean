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
theorem historyMarkedPrior_invariant_law {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {T B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E X : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace X]
    {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ} (ha : Measurable a)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ historyActivityRadius Δ)
    {f : HistoryMarked dependent E → X} (hf : Measurable f)
    (hkill : ∀ j h S, MeasurableSet S →
      ∫ e, (S.indicator (fun _ => 1))
        (f (historyMarkedAppend j (h, e))) * a e ∂π = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Measure.map f (historyMarkedPrior dependent Δ t π a) =
      Measure.map f (historyMarkedReference dependent Δ π) := by
  have hs  :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB) (historyReferenceRho_pos Δ).le).trans hsmall
  let := historyMarkedPrior_probability hΔ hlabels ht.1 hB (Integrable.of_bound ha.aestronglyMeasurable B (Eventually.of_forall fun e => by simpa using habound e)) hcenter habound hs
  let := historyMarkedReference_probability hΔ hlabels π
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  let F := (f ⁻¹' S).indicator (fun _ => (1 : ℝ))
  have hF : Measurable F := measurable_const.indicator (hf hS)
  have hbound : ∀ h, |F h| ≤ 1 := by
    intro h
    by_cases hh : f h ∈ S <;> simp [F, hh]
  have he := historyMarkedPrior_invariant_observable hΔ hlabels hT hB ha habound hsmall hF (by norm_num) hbound (by
    tauto) ht
  change (∫ h, (f ⁻¹' S).indicator 1 h
    ∂historyMarkedPrior dependent Δ t π a) =
      ∫ h, (f ⁻¹' S).indicator 1 h
        ∂historyMarkedReference dependent Δ π at he
  rw [integral_indicator_one (hf hS), integral_indicator_one (hf hS)] at he
  exact he

end NearlyMinimax
