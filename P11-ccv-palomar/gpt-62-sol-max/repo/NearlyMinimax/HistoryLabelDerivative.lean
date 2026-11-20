module

public import NearlyMinimax.HistoryExpectationDerivative


@[expose] public section

/-!
# Actual maximal-label decomposition of the history derivative
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The actual maximal-deletion contribution of one spatial label. -/
def historyMarkedLabelTerm (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (j : J) (h : HistoryMarked dependent E) : ℝ :=
  ∑ x ∈ (historyMaximalPieces Finset.univ).filter (fun x => wordHeapLabel x = j),
    historyMarkedDeleteContribution dependent ρ t a h x

section
variable (dependent : J → J → Prop)

/-- Genuine finite maximal pieces partition by their actual labels. -/
theorem historyMarkedDensityDerivative_eq_labelSum (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) :
    historyMarkedDensityDerivative dependent ρ t a h =
      ρ⁻¹ * ∑ j, historyMarkedLabelTerm dependent ρ t a j h := by
  classical
  unfold historyMarkedDensityDerivative historyMarkedLabelTerm
  rw [Finset.sum_fiberwise]

/-- There is no contribution when the actual shape has no maximal piece of that label. -/
theorem historyMarkedLabelTerm_eq_zero
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (j : J) (h : HistoryMarked dependent E)
    (hn : h ∉ historyMarkedTerminalSet dependent j) : historyMarkedLabelTerm dependent ρ t a j h = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨hm, hl⟩ := Finset.mem_filter.mp hx
  exact (hn ((historyShape_terminal_iff_maximal dependent hsymm j h.1).2 ⟨x, hm, hl⟩)).elim

/-- On a genuine append, the unique fresh maximal label has exactly the old deleted density. -/
theorem historyMarkedLabelTerm_append
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ρ t : ℝ) {E : Type*} [MeasurableSpace E] (a : E → ℝ) (j : J)
    (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedLabelTerm dependent ρ t a j (historyMarkedAppend dependent hsymm j (h, fresh)) =
      a fresh * historyMarkedDensity dependent ρ t a h := by
  classical
  rcases h with ⟨g, marks⟩
  change (∑ y ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece (historyShapeAppend dependent j g).out dependent))
    with wordHeapLabel y = j,
    historyMarkedDeleteContribution dependent ρ t a (historyMarkedAppend dependent hsymm j (⟨g, marks⟩, fresh)) y) = _
  rw [Finset.sum_eq_single (historyCanonicalAppendedPiece dependent hsymm j g)]
  · exact historyMarkedDeleteContribution_append dependent hsymm ρ t a j g fresh marks
  · intro y hy hn
    obtain ⟨hm, hl⟩ := Finset.mem_filter.mp hy
    exact (hn (wordHeap_maximal_label_injective hrefl hsymm Finset.univ hm
      (historyCanonicalAppendedPiece_maximal dependent hsymm j g)
      (hl.trans (historyCanonicalAppendedPiece_label dependent hsymm j g).symm))).elim
  · simp [historyCanonicalAppendedPiece_maximal, historyCanonicalAppendedPiece_label]

/-- Every fixed maximal-label contribution is actually measurable. -/
theorem historyMarkedLabelTerm_measurable (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) (j : J) :
    Measurable (historyMarkedLabelTerm dependent ρ t a j) := by
  classical
  rw [historySigma_measurable_iff]
  intro g
  change Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)) with wordHeapLabel x = j,
      historyMarkedDeleteContribution dependent ρ t a ⟨g, marks⟩ x)
  exact Finset.measurable_fun_sum _ fun x _ => historyMarkedDeleteContribution_fiber_measurable dependent ρ t a ha g x

end

/-- The label contribution is bounded uniformly over all finite histories. -/
theorem HistoryPriorBounds.labelTerm_abs_le {dependent : J → J → Prop} {Δ : ℕ}
    {E : Type*} [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} {T B : ℝ} (P : HistoryPriorBounds dependent Δ π a T B) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (j : J) (h : HistoryMarked dependent E) :
    |historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h| ≤ B * (3 / 2 : ℝ) ^ Fintype.card J := by
  classical
  let S := (historyMaximalPieces (Finset.univ : Finset (WordHeapPiece h.1.out dependent))).filter (fun x => wordHeapLabel x = j)
  have hc : S.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy =>
    wordHeap_maximal_label_injective P.refl P.symm Finset.univ (Finset.mem_filter.mp hx).1
      (Finset.mem_filter.mp hy).1 ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have hb := P.bound_nonneg
  refine (abs_sum_le_card_mul (s := S) (fun x hx => P.deleteContribution_abs_le ht h x (Finset.mem_filter.mp hx).1)).trans ?_
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hc)

end NearlyMinimax
