module

public import NearlyMinimax.HistoryReferenceAppendTransport
public import NearlyMinimax.FiniteBounds


@[expose] public section

/-!
# Genuine uniform derivative bound for the marked-history density
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The derivative contribution from deleting one occurrence. -/
def historyMarkedDeleteContribution (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  historyMarkedPieceWeight dependent a h x *
    historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t

theorem historyMarkedDeleteContribution_append (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ) {E : Type*} [MeasurableSpace E]
    (a : E → ℝ) (j : J) (g : HistoryShape (fun i j => ¬ dependent i j)) (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E) :
    historyMarkedDeleteContribution dependent ρ t a (historyMarkedAppend dependent hsymm j (⟨g, marks⟩, fresh))
      (historyCanonicalAppendedPiece dependent hsymm j g) = a fresh * historyMarkedDensity dependent ρ t a ⟨g, marks⟩ :=
  congrArg₂ (· * ·) (congrArg a (historyCanonicalMarkAppendEquiv_fresh dependent hsymm j g fresh marks))
    (historyCanonicalAppend_density_delete dependent hsymm j g fresh marks a ρ t)

section
variable {dependent : J → J → Prop} {Δ : ℕ} {E : Type*} [MeasurableSpace E]
    {π : Measure E} [IsProbabilityMeasure π] {a : E → ℝ} {T B : ℝ}
    (P : HistoryPriorBounds dependent Δ π a T B)
include P

theorem HistoryPriorBounds.deleteContribution_abs_le {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent)
    (hx : x ∈ historyMaximalPieces Finset.univ) :
    |historyMarkedDeleteContribution dependent (historyReferenceRho Δ) t a h x| ≤ B * (3 / 2 : ℝ) ^ Fintype.card J := by
  classical
  rcases h with ⟨g, marks⟩
  generalize hj : wordHeapLabel x = j
  obtain ⟨old, rfl⟩ := (historyShape_terminal_iff_maximal dependent P.symm j g).2 ⟨x, hx, hj⟩
  rw [wordHeap_maximal_label_injective P.refl P.symm Finset.univ hx
    (historyCanonicalAppendedPiece_maximal dependent P.symm j old)
    (hj.trans (historyCanonicalAppendedPiece_label dependent P.symm j old).symm)]
  let e := historyCanonicalMarkAppendEquiv dependent P.symm j old (E := E)
  obtain ⟨⟨fresh, oldMarks⟩, rfl⟩ := e.surjective marks
  change |historyMarkedDeleteContribution dependent (historyReferenceRho Δ) t a
    (historyMarkedAppend dependent P.symm j (⟨old, oldMarks⟩, fresh)) _| ≤ _
  rw [historyMarkedDeleteContribution_append, abs_mul, abs_of_nonneg (P.density_nonneg ht _)]
  exact mul_le_mul (P.bound _) (P.density_bounds ht _).2 (P.density_nonneg ht _) P.bound_nonneg

end

/-- The true finite maximal-deletion expression for the time derivative. -/
def historyMarkedDensityDerivative (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  ρ⁻¹ * ∑ x ∈ historyMaximalPieces Finset.univ,
    historyMarkedDeleteContribution dependent ρ t a h x

/-- Differentiability comes from the actual finite upper-set polynomial. -/
theorem historyMarkedDensity_hasDerivAt (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) :
    HasDerivAt (fun u => historyMarkedDensity dependent ρ u a h)
      (historyMarkedDensityDerivative dependent ρ t a h) t :=
  historyScaledUpperDensity_hasDerivAt _ ρ Finset.univ t

/-- The derivative bound depends on the label count rather than history length. -/
theorem HistoryPriorBounds.densityDerivative_abs_le {dependent : J → J → Prop} {Δ : ℕ}
    {E : Type*} [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} {T B : ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (h : HistoryMarked dependent E) :
    |historyMarkedDensityDerivative dependent (historyReferenceRho Δ) t a h| ≤
      (historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J := by
  have hp := P.bound_nonneg
  have hρ := historyReferenceRho_pos Δ
  rw [historyMarkedDensityDerivative, abs_mul, abs_of_pos (inv_pos.mpr hρ), mul_assoc, mul_assoc]
  gcongr
  refine (abs_sum_le_card_mul (P.deleteContribution_abs_le ht h)).trans ?_
  gcongr
  exact_mod_cast wordHeap_maximal_card_le_labels P.refl P.symm Finset.univ

section
variable (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a)
include ha

theorem historyMarkedDeleteContribution_fiber_measurable
    (g : HistoryShape (fun i j => ¬ dependent i j)) (x : WordHeapPiece g.out dependent) :
    Measurable (fun marks => historyMarkedDeleteContribution dependent ρ t a ⟨g, marks⟩ x) :=
  (historyMarkedPieceWeight_fiber_measurable dependent a ha g x).mul
    (historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g (Finset.univ.erase x))

/-- The actual finite derivative is measurably evaluable under the countable reference law. -/
theorem historyMarkedDensityDerivative_measurable :
    Measurable (historyMarkedDensityDerivative dependent ρ t a) :=
  (historySigma_measurable_iff _).2 fun g =>
    (Finset.measurable_fun_sum (historyMaximalPieces Finset.univ) fun x _ =>
      historyMarkedDeleteContribution_fiber_measurable dependent ρ t a ha g x).const_mul ρ⁻¹

end

end NearlyMinimax
