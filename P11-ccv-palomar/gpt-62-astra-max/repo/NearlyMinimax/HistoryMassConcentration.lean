module

public import NearlyMinimax.LabelBlockConcentration
public import NearlyMinimax.HistoryReferenceFiberIntegral


@[expose] public section

/-!
# Mass exponential moment from actual canonical-history label blocks
-/

noncomputable section
open MeasureTheory Filter
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlabels : DegreeAtMost dependent Δ) {E : Type*} [MeasurableSpace E]
include hlabels hΔ

/-- The genuine reference mean is one when every actual canonical mark fiber has mean one. -/
theorem historyMarkedReference_mean_one {π : Measure E} [IsProbabilityMeasure π]
    {m : HistoryMarked dependent E → ℝ} (hm : Measurable m) (R : ℝ) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength g) => π)) = 1) :
    (∫ h, m h ∂historyMarkedReference dependent Δ π) = 1 := by
  have hu := historyMarkedReference_integral_le_of_fiber_bound hΔ hlabels
    π hm 1 hbound (fun g => (hmean g).le)
  have hl := historyMarkedReference_integral_le_of_fiber_bound hΔ hlabels
    π (F := (fun h => -m h)) hm.neg (-1) (fun h => by simpa using hbound h)
    (fun g => by rw [integral_neg, hmean g])
  rw [integral_neg] at hl
  linarith

/-- Actual source mean-one and label-block oscillation prove the mass MGF under the true infinite reference.
The hypotheses describe the actual measurable mass function, its finite recursion mean, and geometric locality.
No mass concentration or statistical rate bound is a premise. -/
theorem historyMarkedReference_mass_mgf [Nonempty E] {π : Measure E} [IsProbabilityMeasure π]
    {m : HistoryMarked dependent E → ℝ} (hm : Measurable m)
    (R c : ℝ) (hc : 0 ≤ c) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength g) => π)) = 1)
    (hosc : ∀ g j (marks marks' : Fin (historyShapeLength g) → E),
      (∀ i, historyShapeCanonicalLabels g i ≠ j → marks i = marks' i) →
        |m ⟨g, marks⟩ - m ⟨g, marks'⟩| ≤ c) (u : ℝ) :
    (∫ h, Real.exp (u * (m h - 1)) ∂historyMarkedReference dependent Δ π) ≤
      Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  let F := fun h : HistoryMarked dependent E => Real.exp (u * (m h - 1))
  have hF : Measurable F := by fun_prop
  have hFb : ∀ h, |F h| ≤ Real.exp (|u| * (R + 1)) := by
    intro h
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc
      _ ≤ _ := le_abs_self _
      _ = _ := abs_mul _ _
      _ ≤ |u| * (R + 1) := mul_le_mul_of_nonneg_left
        (by grind) (abs_nonneg _)
  apply historyMarkedReference_integral_le_of_fiber_bound hΔ hlabels π hF _ hFb
  intro g
  have hmf  :=
    hm.comp (measurable_sigma_mk_actual g)
  have hh := label_block_centered_mgf_le π
    (F := (fun marks => m ⟨g, marks⟩)) hmf R c hc (fun marks => hbound ⟨g, marks⟩) (hosc g) u
  rw [hmean g] at hh
  exact hh

end NearlyMinimax
