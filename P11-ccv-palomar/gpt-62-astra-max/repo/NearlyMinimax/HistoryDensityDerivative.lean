module

public import NearlyMinimax.HistoryReferenceAppendTransport


@[expose] public section

/-!
# Genuine uniform derivative bound for the marked-history density
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

section
variable {dependent : J → J → Prop} (ρ t : ℝ) {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E)

/-- Every genuine maximal deletion is the old canonical density of an actual append inverse. -/
theorem historyMarkedDensity_deleted_bounds
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    {ρ t B : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] {a : E → ℝ} (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ historyActivityRadius Δ)
    {g : DependenceHeap dependent} (marks : Fin (historyShapeLength g) → E)
    {x : WordHeapPiece g.out dependent} (hx : x ∈ historyMaximalPieces Finset.univ) :
    let upperDensity := historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t
    (1 / 2 : ℝ) ^ Fintype.card J ≤
      upperDensity ∧
      upperDensity ≤
        (3 / 2 : ℝ) ^ Fintype.card J := by
  classical
  generalize hj : wordHeapLabel x = j
  have hg  :=
    (historyShape_terminal_iff_maximal dependent j g).2 ⟨x, hx, hj⟩
  obtain ⟨old, rfl⟩ := hg
  have hxe  :=
    wordHeap_maximal_label_injective Finset.univ hx
      (historyCanonicalAppendedPiece_maximal dependent j old)
      (hj.trans (historyCanonicalAppendedPiece_label dependent j old).symm)
  rw [hxe]
  let p := (historyCanonicalMarkAppendEquiv j old (E := E)).symm marks
  have hm  :=
    (historyCanonicalMarkAppendEquiv j old).apply_symm_apply marks
  rw [← hm, historyCanonicalAppend_density_delete]
  exact historyMarkedDensity_bounds hlabels hρ ht hB ha hsmall ⟨old, p.2⟩

/-- The true finite maximal-deletion expression for the time derivative. -/
def historyMarkedDensityDerivative : ℝ :=
  ρ⁻¹ * ∑ x ∈ historyMaximalPieces Finset.univ,
    historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t

/-- Differentiability comes from the actual finite upper-set polynomial. -/
theorem historyMarkedDensity_hasDerivAt :
    HasDerivAt (fun u => historyMarkedDensity ρ u a h)
      (historyMarkedDensityDerivative ρ t a h) t :=
  historyScaledUpperDensity_hasDerivAt _ ρ Finset.univ t

/-- The derivative bound depends on the finite label set, not the unbounded history length. -/
theorem historyMarkedDensityDerivative_bound
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hlabels : DegreeAtMost dependent Δ)
    {ρ t B : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] {a : E → ℝ} (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ historyActivityRadius Δ) (h : HistoryMarked dependent E) :
    |historyMarkedDensityDerivative ρ t a h| ≤
      ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J := by
  classical
  let S := historyMaximalPieces (Finset.univ : Finset (WordHeapPiece h.1.out dependent))
  let C  := (3 / 2 : ℝ) ^ Fintype.card J
  have hC : 0 ≤ C := by positivity
  have hw : ∀ x ∈ S, |historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t| ≤ B * C := by
    intro x hx
    have hb := historyMarkedDensity_deleted_bounds hlabels hρ ht hB ha hsmall h.2 hx
    have hn  :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul (ha _) hb.2 hn hB
  have hc : (S.card : ℝ) ≤ Fintype.card J := by
    exact_mod_cast wordHeap_maximal_card_le_labels Finset.univ
  unfold historyMarkedDensityDerivative
  rw [abs_mul, abs_of_pos (inv_pos.2 hρ)]
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hρ.le)
    _ ≤ _ := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (inv_nonneg.2 hρ.le)
    _ ≤ _ := by
      nlinarith [mul_nonneg hB hC, mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.2 hρ.le) (mul_nonneg hB hC))]

/-- Actual polynomial measurability on every fixed canonical deletion subset. -/
theorem historyMarkedSubdensity_fiber_measurable [MeasurableSpace E] {a : E → ℝ} (ha : Measurable a)
    {g : DependenceHeap dependent} (S : Finset (WordHeapPiece g.out dependent)) :
    Measurable (fun marks : Fin (historyShapeLength g) → E =>
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ S t) := by
  classical
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable (fun marks : Fin (historyShapeLength g) → E =>
    ∑ P ∈ historyUpperSets S, (t / ρ) ^ P.card * historyOrderVolume P *
      ∏ x ∈ P, a (marks (Fin.cast (historyShapeLength_out g).symm x.position)))
  fun_prop

end

/-- The actual finite derivative is measurably evaluable under the countable reference law. -/
theorem historyMarkedDensityDerivative_measurable (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] {a : E → ℝ} (ha : Measurable a) :
    Measurable (historyMarkedDensityDerivative (dependent := dependent) ρ t a) := by
  classical
  rw [sigma_measurable_iff]
  intro g
  change Measurable (fun marks : Fin (historyShapeLength g) → E =>
    ρ⁻¹ * ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      a (marks (Fin.cast (historyShapeLength_out g).symm x.position)) *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t)
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum _
  intro x hx
  exact (ha.comp (by fun_prop)).mul
    (historyMarkedSubdensity_fiber_measurable ρ t ha (Finset.univ.erase x))

end NearlyMinimax
