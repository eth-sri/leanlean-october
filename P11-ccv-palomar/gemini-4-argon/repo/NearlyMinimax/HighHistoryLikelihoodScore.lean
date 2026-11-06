module
public import NearlyMinimax.HistoryCanonicalDeletion
public import NearlyMinimax.HighMassTilt
@[expose] public section
noncomputable section
open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
section
variable {I X E : Type*} {d : ℕ}
section
section
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMeasure_smul_sum  [MeasurableSpace X]
    (c : ℝ≥0∞) (μ : I → Measure X) : c • Measure.sum μ = Measure.sum (fun i => c • μ i) := by
  ext s hs
  simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul]
  exact ENNReal.tsum_mul_left.symm
theorem historyMarkedAppend_fiber_map (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    Measure.map (historyMarkedAppend dependent hsymm j (E := E))
      ((Measure.map (Sigma.mk g) (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π))).prod π) =
      Measure.map (Sigma.mk (historyShapeAppend dependent j g))
        (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π)) := by
  let ν := Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)
  let f : (Fin (historyShapeLength dependent g) → E) × E → HistoryMarked dependent E :=
    fun p => historyMarkedAppend dependent hsymm j (⟨g, p.1⟩, p.2)
  have : Measurable f := (historyMarkedAppend_measurable dependent hsymm j).comp
    ((historyMarked_measurable_mk dependent g).prodMap measurable_id)
  have hm : (Measure.map (Sigma.mk g) ν).prod π =
      Measure.map (Prod.map (fun marks : Fin (historyShapeLength dependent g) → E =>
        (⟨g, marks⟩ : HistoryMarked dependent E)) id) (ν.prod π) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map ν π (historyMarked_measurable_mk dependent g) measurable_id
  rw [hm, Measure.map_map (historyMarkedAppend_measurable dependent hsymm j)
    ((historyMarked_measurable_mk dependent g).prodMap measurable_id)]
  let m := fun p : (Fin (historyShapeLength dependent g) → E) × E =>
    historyCanonicalMarkAppendEquiv dependent hsymm j g (p.2, p.1)
  have h_historyCanonicalMarkAppendEquiv_preserving  := (measurePreserving_piCongrLeft (fun _ => π) (historyCanonicalAppendCoordinates dependent hsymm j g)).comp
    (historyFiniteMarkAppendEquiv_preserving _ π)
  have hp : MeasurePreserving m (ν.prod π)
      (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π)) :=
    h_historyCanonicalMarkAppendEquiv_preserving.comp Measure.measurePreserving_swap
  change Measure.map ((fun marks : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E =>
    (⟨historyShapeAppend dependent j g, marks⟩ : HistoryMarked dependent E)) ∘ m) (ν.prod π) = _
  rw [← Measure.map_map (historyMarked_measurable_mk dependent _) hp.measurable, hp.map_eq]
def historyMarkedTerminalReferenceRaw (dependent : J → J → Prop)
    (Δ : ℕ) (j : J)  [MeasurableSpace E] (π : Measure E) :
    Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ (historyShapeAppend dependent j g)) •
    Measure.map (Sigma.mk (historyShapeAppend dependent j g))
      (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π))
theorem historyMarkedReferenceRaw_append (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J)  [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReferenceRaw dependent Δ π).prod π) =
      historyMarkedTerminalReferenceRaw dependent Δ j π := by
  unfold historyMarkedReferenceRaw historyMarkedTerminalReferenceRaw
  rw [Measure.prod_sum_left, Measure.map_sum (historyMarkedAppend_measurable dependent hsymm j).aemeasurable, historyMeasure_smul_sum]
  congr 1
  funext g
  have h_historyShapeReferenceWeight_append (g : HistoryShape (fun a b => ¬ dependent a b)) : historyShapeReferenceWeight dependent Δ (historyShapeAppend dependent j g) =
      historyReferenceRho Δ * historyShapeReferenceWeight dependent Δ g := by
    unfold historyShapeReferenceWeight
    have h_historyShapeLength_append : historyShapeLength dependent (historyShapeAppend dependent j g) = historyShapeLength dependent g + 1 := by
      induction g using Quotient.inductionOn
      rename_i word
      rw [historyShapeAppend_mk, historyShapeLength_mk, historyShapeLength_mk]
      simp
    rw [h_historyShapeLength_append, pow_succ, mul_comm]
  rw [Measure.prod_smul_left, Measure.map_smul, smul_smul,
    historyMarkedAppend_fiber_map, h_historyShapeReferenceWeight_append,
    ENNReal.ofReal_mul (historyReferenceRho_pos Δ).le]
  exact (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
def historyMarkedTerminalSet (dependent : J → J → Prop) (j : J)  :
    Set (HistoryMarked dependent E) := {h | h.1 ∈ Set.range (historyShapeAppend dependent j)}
end
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyMarkedDensityDerivative (dependent : J → J → Prop) (ρ t : ℝ)
     (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  ρ⁻¹ * ∑ x ∈ historyMaximalPieces Finset.univ,
    historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t
theorem historyMarkedDensity_hasDerivAt (dependent : J → J → Prop) (ρ t : ℝ)
     (a : E → ℝ) (h : HistoryMarked dependent E) :
    HasDerivAt (fun u => historyMarkedDensity dependent ρ u a h)
      (historyMarkedDensityDerivative dependent ρ t a h) t :=
  historyScaledUpperDensity_hasDerivAt _ ρ Finset.univ t
theorem historyMarkedDensityDerivative_bound (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
     [MeasurableSpace E] (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    |historyMarkedDensityDerivative dependent ρ t a h| ≤
      ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J := by
  let S := historyMaximalPieces (Finset.univ : Finset (WordHeapPiece h.1.out dependent))
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  have hC : 0 ≤ C := by positivity
  have hw : ∀ x ∈ S, |historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t| ≤ B * C := by
    intro x hx
    have h_historyMarkedDensity_deleted_bounds (g : HistoryShape (fun a b => ¬ dependent a b)) (marks : Fin (historyShapeLength dependent g) → E) (x : WordHeapPiece g.out dependent) (hx : x ∈ historyMaximalPieces Finset.univ) : (1 / 2 : ℝ) ^ Fintype.card J ≤
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t ∧
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t ≤
          (3 / 2 : ℝ) ^ Fintype.card J := by
      generalize hj : wordHeapLabel x = j
      obtain ⟨old, rfl⟩ := (historyShape_terminal_iff_maximal dependent hsymm j g).2 ⟨x, hx, hj⟩
      have hxe  :=
        wordHeap_maximal_label_injective hrefl hsymm Finset.univ hx
          (historyCanonicalAppendedPiece_maximal dependent hsymm j old)
          (hj.trans (historyCanonicalAppendedPiece_label dependent hsymm j old).symm)
      rw [hxe, ← ((historyCanonicalMarkAppendEquiv dependent hsymm j old).apply_symm_apply marks), historyCanonicalAppend_density_delete]
      exact historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a ha hsmall ⟨old, ((historyCanonicalMarkAppendEquiv dependent hsymm j old (E := E)).symm marks).2⟩
    have hb := h_historyMarkedDensity_deleted_bounds h.1 h.2 x hx
    have hn  :=
      (by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul (ha _) hb.2 hn hB
  have hc : (S.card : ℝ) ≤ Fintype.card J := by
    exact_mod_cast wordHeap_maximal_card_le_labels hrefl hsymm Finset.univ
  unfold historyMarkedDensityDerivative
  rw [abs_mul, abs_of_pos (inv_pos.2 hρ)]
  calc
    _ ≤ ρ⁻¹ * ∑ x ∈ S, |historyMarkedPieceWeight dependent a h x *
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hρ.le)
    _ ≤ ρ⁻¹ * (S.card : ℝ) * (B * C) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (inv_nonneg.2 hρ.le)
    _ ≤ _ := by
      nlinarith [mul_nonneg hB hC, mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.2 hρ.le) (mul_nonneg hB hC))]
theorem historyMarkedSubdensity_fiber_measurable (dependent : J → J → Prop) (ρ t : ℝ)
     [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a)
    (g : HistoryShape (fun i j => ¬ dependent i j)) (S : Finset (WordHeapPiece g.out dependent)) :
    Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ S t) := by
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ P ∈ historyUpperSets S, (t / ρ) ^ P.card * historyOrderVolume P *
      ∏ x ∈ P, a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)))
  apply Finset.measurable_fun_sum _
  intro P hP
  apply Measurable.const_mul
  apply Finset.measurable_fun_prod _
  intro x hx
  exact ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))
theorem historyMarkedDensityDerivative_measurable (dependent : J → J → Prop) (ρ t : ℝ)
     [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) :
    Measurable (historyMarkedDensityDerivative dependent ρ t a) := by
  rw [historyMarked_measurable_iff]
  intro g
  change Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
    ρ⁻¹ * ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)) *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t)
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum _
  intro x hx
  exact (ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))).mul
    (historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g (Finset.univ.erase x))
end
section
section
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyMarkedExpectation (dependent : J → J → Prop) (ρ : ℝ)
     [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E))
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) (t : ℝ) : ℝ :=
  ∫ h, F h * historyMarkedDensity dependent ρ t a h ∂μ
theorem historyMarkedExpectation_hasDerivAt (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B t : ℝ) (hρ : 0 < ρ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
     [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    Integrable (fun h => F h * historyMarkedDensityDerivative dependent ρ t a h) μ ∧
      HasDerivAt (historyMarkedExpectation dependent ρ μ a F)
        (∫ h, F h * historyMarkedDensityDerivative dependent ρ t a h ∂μ) t := by
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have : 0 ≤ C := by positivity
  have hs : ∀ u ∈ Ioo 0 T, u * B / ρ ≤ 1 / (2 + 8 * ↑Δ ^ 2) := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB) hρ.le).trans hsmall
  have hbound : ∀ u ∈ Ioo 0 T, ∀ h : HistoryMarked dependent E,
      |F h * historyMarkedDensityDerivative dependent ρ u a h| ≤ M * D := by
    intro u hu h
    rw [abs_mul]
    exact mul_le_mul (hFbound h)
      (historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1.le hB
        a habound (hs u hu) h) (abs_nonneg _) hM
  have hFM : ∀ u, Measurable (fun h => F h * historyMarkedDensity dependent ρ u a h) :=
    fun u => hF.mul (historyMarkedDensity_measurable dependent ρ u a ha)
  have hInt : Integrable (fun h => F h * historyMarkedDensity dependent ρ t a h) μ := by
    apply Integrable.of_bound (hFM t).aestronglyMeasurable (M * C)
    apply Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_mul]
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht.le hB
      a habound (hs t ⟨ht, htT⟩) h
    have hn  :=
      (by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hn]
    exact mul_le_mul (hFbound h) hb.2 hn hM
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u h => F h * historyMarkedDensity dependent ρ u a h)
    (F' := fun u h => F h * historyMarkedDensityDerivative dependent ρ u a h)
    (bound := fun _ => M * D) (s := Ioo 0 T)
    (Ioo_mem_nhds ht htT) (Eventually.of_forall fun u => (hFM u).aestronglyMeasurable)
    hInt ((fun u => hF.mul (historyMarkedDensityDerivative_measurable dependent ρ u a ha)) t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => by simpa only [Real.norm_eq_abs] using hbound u hu h)
    (integrable_const (M * D))
    (Eventually.of_forall fun h u _ => (historyMarkedDensity_hasDerivAt dependent ρ u a h).const_mul (F h))
end
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyMarkedLabelTerm (dependent : J → J → Prop) (ρ t : ℝ) 
    (a : E → ℝ) (j : J) (h : HistoryMarked dependent E) : ℝ :=
  ∑ x ∈ historyMaximalPieces Finset.univ,
    if wordHeapLabel x = j then historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t else 0
theorem historyMarkedLabelTerm_eq_zero (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t )
     (a : E → ℝ) (j : J) (h : HistoryMarked dependent E)
    (hn : h ∉ historyMarkedTerminalSet dependent j) : historyMarkedLabelTerm dependent ρ t a j h = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hl : wordHeapLabel x ≠ j := by
    intro he
    apply hn
    exact (historyShape_terminal_iff_maximal dependent hsymm j h.1).2 ⟨x, hx, he⟩
  simp [hl]
theorem historyMarkedLabelTerm_append (dependent )
    (hrefl : ∀ j, dependent j j) (hsymm )
    (ρ t : ℝ)  [MeasurableSpace E] (a : E → ℝ) (j : J)
    (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedLabelTerm dependent ρ t a j (historyMarkedAppend dependent hsymm j (h, fresh)) =
      a fresh * historyMarkedDensity dependent ρ t a h := by
  rcases h with ⟨g, marks⟩
  unfold historyMarkedLabelTerm
  change (∑ y ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece (historyShapeAppend dependent j g).out dependent)),
    if wordHeapLabel y = j then historyMarkedPieceWeight dependent a
      ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩ y *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
        ρ (Finset.univ.erase y) t else 0) = _
  rw [Finset.sum_eq_single (historyCanonicalAppendedPiece dependent hsymm j g)]
  · rw [ite_eq_left (historyCanonicalAppendedPiece_label dependent hsymm j g)]
    have h_historyCanonicalMarkAppendEquiv_fresh : historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
      (historyCanonicalFreshCoordinate dependent hsymm j g) = fresh := by
      have h_historyCanonicalAppendCoordinates_last : historyCanonicalAppendCoordinates dependent hsymm j g (Fin.last (historyShapeLength dependent g)) =
          historyCanonicalFreshCoordinate dependent hsymm j g := by
        let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
          rw [historyShapeLength_out]; simp
        have hl : (finCongr hlen) (Fin.last (historyShapeLength dependent g)) =
            (wordHeapAppendedPiece g.out dependent j).position := by
          apply Fin.ext
          exact historyShapeLength_out dependent g
        unfold historyCanonicalAppendCoordinates historyCanonicalFreshCoordinate historyCanonicalAppendedPiece
        change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
          (historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
            ((finCongr hlen) (Fin.last (historyShapeLength dependent g)))) = _
        rw [hl, historyHeapCoordinateEquiv_position]
      rw [← h_historyCanonicalAppendCoordinates_last]
      have hh := MeasurableEquiv.piCongrLeft_apply_apply
        (historyCanonicalAppendCoordinates dependent hsymm j g)
        (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.last _)
      change MeasurableEquiv.piCongrLeft
        (fun _ => E)
        (historyCanonicalAppendCoordinates dependent hsymm j g)
        (historyFiniteMarkAppendEquiv _ (fresh, marks))
        (historyCanonicalAppendCoordinates dependent hsymm j g (Fin.last (historyShapeLength dependent g))) = fresh
      rw [hh, historyFiniteMarkAppendEquiv_last]
    exact congrArg₂ (fun u v => u * v) (congrArg a h_historyCanonicalMarkAppendEquiv_fresh)
      (historyCanonicalAppend_density_delete dependent hsymm j g fresh marks a ρ t)
  · intro y hy hne
    have hn : wordHeapLabel y ≠ j := by
      intro hj
      apply hne
      exact wordHeap_maximal_label_injective hrefl hsymm Finset.univ hy
        (historyCanonicalAppendedPiece_maximal dependent hsymm j g)
        (hj.trans (historyCanonicalAppendedPiece_label dependent hsymm j g).symm)
    simp [hn]
  · intro hn
    exact (hn (historyCanonicalAppendedPiece_maximal dependent hsymm j g)).elim
theorem historyMarkedLabelTerm_measurable (dependent ρ t)
     [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) (j : J) :
    Measurable (historyMarkedLabelTerm dependent ρ t a j) := by
  rw [historyMarked_measurable_iff]
  intro g
  change Measurable (fun marks =>
    ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      if wordHeapLabel x = j then
        a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)) *
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t else 0)
  apply Finset.measurable_fun_sum _
  intro x hx
  split_ifs
  · exact (ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))).mul
      (historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g (Finset.univ.erase x))
  · exact measurable_const
end
section
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyMarkedGeneratorExpectation (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
     [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) (π : Measure E)
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2 *
      historyMarkedDensity dependent ρ t a p.1 ∂μ.prod π
theorem historyMarkedLabelTerm_integrable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
     [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) (j : J) :
    Integrable (fun h => F h * historyMarkedLabelTerm dependent ρ t a j h) μ := by
  apply Integrable.of_bound (hF.mul (historyMarkedLabelTerm_measurable dependent ρ t a ha j)).aestronglyMeasurable
    (M * (B * (3 / 2 : ℝ) ^ Fintype.card J))
  apply Eventually.of_forall
  intro h
  change ‖F h * historyMarkedLabelTerm dependent ρ t a j h‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  have h_historyMarkedLabelTerm_bound : |historyMarkedLabelTerm dependent ρ t a j h| ≤ B * (3 / 2 : ℝ) ^ Fintype.card J := by
    by_cases hn : h ∈ historyMarkedTerminalSet dependent j
    · rcases h with ⟨g, marks⟩
      obtain ⟨old, rfl⟩ := hn
      let p := (historyCanonicalMarkAppendEquiv dependent hsymm j old (E := E)).symm marks
      rw [← ((historyCanonicalMarkAppendEquiv dependent hsymm j old).apply_symm_apply marks)]
      change |historyMarkedLabelTerm dependent ρ t a j
        (historyMarkedAppend dependent hsymm j (⟨old, p.2⟩, p.1))| ≤ _
      rw [historyMarkedLabelTerm_append dependent hrefl hsymm, abs_mul]
      have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a habound hsmall ⟨old, p.2⟩
      have hp  :=
        (by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
      rw [abs_of_nonneg hp]
      exact mul_le_mul (habound _) hb.2 hp hB
    · rw [historyMarkedLabelTerm_eq_zero dependent hsymm ρ t a j h hn, abs_zero]
      positivity
  exact mul_le_mul (hFbound h)
    h_historyMarkedLabelTerm_bound
    (abs_nonneg _) hM
theorem historyMarkedDensityDerivative_integral_eq_generator (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)  [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    (∫ h, F h * historyMarkedDensityDerivative dependent (historyReferenceRho Δ) t a h
      ∂historyMarkedReference dependent Δ π) =
      historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  have h_historyMarkedTerminalSet_measurable (j : J) : MeasurableSet (historyMarkedTerminalSet dependent j (E := E)) := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro g
    change MeasurableSet {marks : Fin (historyShapeLength dependent g) → E |
      g ∈ Set.range (historyShapeAppend dependent j)}
    by_cases hg : g ∈ Set.range (historyShapeAppend dependent j) <;> simp [hg]
  let μ := historyMarkedReference dependent Δ π
  let : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hi : ∀ j, Integrable (fun h => F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h) μ :=
    fun j => historyMarkedLabelTerm_integrable dependent hrefl hsymm Δ hlabels _ t B
      (historyReferenceRho_pos Δ) ht hB μ a ha habound hsmall F hF M hM hFbound j
  have hp : ∀ h : HistoryMarked dependent E,
      F h * historyMarkedDensityDerivative dependent (historyReferenceRho Δ) t a h =
        (historyReferenceRho Δ)⁻¹ * ∑ j, F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h := by
    intro h
    have h_historyMarkedDensityDerivative_eq_labelSum (ρ : ℝ) (t : ℝ) (a : E → ℝ) (h : HistoryMarked dependent E) : historyMarkedDensityDerivative dependent ρ t a h =
      ρ⁻¹ * ∑ j, historyMarkedLabelTerm dependent ρ t a j h := by
      unfold historyMarkedDensityDerivative historyMarkedLabelTerm
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      simp
    rw [h_historyMarkedDensityDerivative_eq_labelSum]
    calc
      _ = (historyReferenceRho Δ)⁻¹ *
          (F h * ∑ j, historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h) := by ring
      _ = _ := by rw [Finset.mul_sum]
  simp_rw [hp]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hi j)]
  have h_historyMarkedLabelTerm_integral (j : J) : (∫ h, F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h
      ∂historyMarkedReference dependent Δ π) =
    historyReferenceRho Δ * ∫ p : HistoryMarked dependent E × E,
      F (historyMarkedAppend dependent hsymm j p) * a p.2 *
        historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1
        ∂(historyMarkedReference dependent Δ π).prod π := by
    let μ := historyMarkedReference dependent Δ π
    let G := fun h : HistoryMarked dependent E =>
      F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h
    have hG : Measurable G := hF.mul (historyMarkedLabelTerm_measurable dependent _ t a ha j)
    have h_historyMarkedReference_append_restrict : ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReference dependent Δ π).prod π) =
      (historyMarkedReference dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := by
      let c := (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹
      change ENNReal.ofReal (historyReferenceRho Δ) •
          Measure.map (historyMarkedAppend dependent hsymm j) ((c • historyMarkedReferenceRaw dependent Δ π).prod π) =
            (c • historyMarkedReferenceRaw dependent Δ π).restrict _
      rw [Measure.prod_smul_left, Measure.map_smul, Measure.restrict_smul]
      swap
      · exact (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
      have h_historyMarkedTerminalReferenceRaw_eq_restrict : historyMarkedTerminalReferenceRaw dependent Δ j π =
          (historyMarkedReferenceRaw dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := by
        classical
        let G := Set.range (historyShapeAppend dependent j)
        let μ := fun g : HistoryShape (fun a b => ¬ dependent a b) =>
          ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
            Measure.map (fun marks : Fin (historyShapeLength dependent g) → E =>
              (⟨g, marks⟩ : HistoryMarked dependent E)) (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π))
        have hr : ∀ g, (μ g).restrict (historyMarkedTerminalSet dependent j) =
            if g ∈ G then μ g else 0 := by
          intro g
          rw [Measure.restrict_smul, Measure.restrict_map (historyMarked_measurable_mk dependent g)
            (h_historyMarkedTerminalSet_measurable j)]
          have hp : (fun marks : Fin (historyShapeLength dependent g) → E =>
              (⟨g, marks⟩ : HistoryMarked dependent E)) ⁻¹' historyMarkedTerminalSet dependent j =
              if g ∈ G then Set.univ else ∅ := by
            ext marks
            simp only [Set.mem_preimage, historyMarkedTerminalSet, Set.mem_ofPred_eq]
            by_cases hg : g ∈ G <;> simp [G, hg]
          rw [hp]
          by_cases hg : g ∈ G <;> simp [hg, μ]
        change _ = (Measure.sum μ).restrict _
        rw [Measure.restrict_sum _ (h_historyMarkedTerminalSet_measurable j)]
        simp_rw [hr]
        have h_historyMeasure_sum_subtype {X} {I} [MeasurableSpace X] (S : Set I) (μ : I → Measure X) : Measure.sum (fun i => if i ∈ S then μ i else 0) = Measure.sum (fun i : S => μ i.val) := by
          ext s hs
          simp only [Measure.sum_apply _ hs]
          calc
            _ = ∑' i, if i ∈ S then μ i s else 0 := by
              apply tsum_congr
              intro i
              split_ifs <;> rfl
            _ = _ := by simpa [Set.indicator_apply] using (tsum_subtype S (fun i => μ i s)).symm
        rw [h_historyMeasure_sum_subtype]
        have h_historyShapeAppend_injective : Function.Injective (historyShapeAppend dependent j) := by
          intro g h heq
          induction g using Quotient.inductionOn
          rename_i u
          induction h using Quotient.inductionOn
          rename_i v
          apply Quotient.sound
          apply historyShapeRelation_of_pair_projections hrefl hsymm
          intro i k hik
          have hc := congrArg (fun shape => historyShapePairCode dependent hrefl hsymm shape ⟨(i, k), hik⟩) heq
          change historyPairProjection i k (u ++ [j]) = historyPairProjection i k (v ++ [j]) at hc
          unfold historyPairProjection at hc ⊢
          rw [List.filter_append, List.filter_append] at hc
          exact List.append_cancel_right hc
        let e := Equiv.ofInjective (historyShapeAppend dependent j)
          h_historyShapeAppend_injective
        exact Measure.sum_comp_equiv e (fun g : G => μ g.val)
      have h_historyMarkedReferenceRaw_append_restrict : ENNReal.ofReal (historyReferenceRho Δ) •
          Measure.map (historyMarkedAppend dependent hsymm j (E := E))
            ((historyMarkedReferenceRaw dependent Δ π).prod π) =
          (historyMarkedReferenceRaw dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := (historyMarkedReferenceRaw_append dependent hsymm Δ j π).trans
        h_historyMarkedTerminalReferenceRaw_eq_restrict
      rw [smul_smul, mul_comm, ← smul_smul,
        h_historyMarkedReferenceRaw_append_restrict]
    have hm := h_historyMarkedReference_append_restrict
    have he := congrArg (fun ν : Measure (HistoryMarked dependent E) => ∫ h, G h ∂ν) hm
    rw [integral_smul_measure, integral_map (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
      hG.aestronglyMeasurable] at he
    have hi : (historyMarkedTerminalSet dependent j).indicator G = G := by
      funext h
      by_cases ht : h ∈ historyMarkedTerminalSet dependent j
      · simp [ht]
      · simp [ht, G, historyMarkedLabelTerm_eq_zero dependent hsymm _ t a j h ht]
    rw [← integral_indicator (h_historyMarkedTerminalSet_measurable j), hi] at he
    rw [ENNReal.toReal_ofReal (historyReferenceRho_pos Δ).le] at he
    change historyReferenceRho Δ *
        (∫ p : HistoryMarked dependent E × E, G (historyMarkedAppend dependent hsymm j p) ∂μ.prod π) =
          ∫ h, G h ∂μ at he
    have hp : ∀ p : HistoryMarked dependent E × E,
        G (historyMarkedAppend dependent hsymm j p) =
          F (historyMarkedAppend dependent hsymm j p) * a p.2 *
            historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1 := by
      intro p
      dsimp only [G]
      rw [historyMarkedLabelTerm_append dependent hrefl hsymm]
      ring
    simp_rw [hp] at he
    exact he.symm
  change (historyReferenceRho Δ)⁻¹ *
    (∑ j, ∫ h, F h * historyMarkedLabelTerm dependent (historyReferenceRho Δ) t a j h
      ∂historyMarkedReference dependent Δ π) = _
  simp_rw [h_historyMarkedLabelTerm_integral]
  unfold historyMarkedGeneratorExpectation
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (historyReferenceRho_pos Δ)), one_mul]
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_integral_eq_expectation (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)  [MeasurableSpace E]
    (π : Measure E) (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) =
      historyMarkedExpectation dependent (historyReferenceRho Δ) (historyMarkedReference dependent Δ π) a F t := by
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
    integral_withDensity_eq_integral_toReal_smul
      (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall h
  simp only [ENNReal.toReal_ofReal ((by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1), smul_eq_mul]
  ring
def historyMarkedPriorGenerator (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (Δ : ℕ) (t : ℝ)
     [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π
end
section
section
variable {Ω : Type*} [MeasurableSpace Ω]
def highRawSampleVarianceDerivative  (n ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∏ i, p (z.1 i)) * ∑ i, (∏ j ∈ Finset.univ.erase i,
    ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)
theorem highRawSampleLikelihood_hasDerivAt_path  (n : ℕ) (a v η t : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    HasDerivAt (fun u => highRawSampleLikelihood n a (v - η ^ 2 * u) p F z)
      (-η ^ 2 * highRawSampleVarianceDerivative n a (v - η ^ 2 * t) p F z) t := by
  have h_highRawSampleLikelihood_hasDerivAt_variance : HasDerivAt (fun W => highRawSampleLikelihood n a W p F z)
      (highRawSampleVarianceDerivative n a (v - η ^ 2 * t) p F z) (v - η ^ 2 * t) := by
    have h := (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
      (fun i _ => ternary_hasDerivAt_variance a (F (z.1 i)) (v - η ^ 2 * t) (z.2 i))).const_mul
        (∏ i, p (z.1 i))
    simpa only [highRawSampleLikelihood, highRawSampleVarianceDerivative,
      Finset.prod_mul_distrib, smul_eq_mul] using h
  have h := h_highRawSampleLikelihood_hasDerivAt_variance.comp t
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2)))
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_one, mul_comm] using h
theorem highRawSampleLikelihood_abs_le  (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highRawSampleLikelihood n a V p F z| ≤ P ^ n := by
  unfold highRawSampleLikelihood
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin n, P := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i _
      rw [abs_mul, abs_of_nonneg (hq (z.1 i) (z.2 i))]
      calc
        |p (z.1 i)| * ternaryMass a (F (z.1 i)) V (z.2 i) ≤ P * 1 :=
          mul_le_mul (hp _) (ternary_mass_le_one a _ V ha (hq _) _) (hq _ _) hP
        _ = P := mul_one _
    _ = _ := by simp
theorem highRawSampleVarianceDerivative_abs_le  (n : ℕ) (a V P : ℝ)
    (ha : 0 < a) (hP : 0 ≤ P) (p F : Covariate d → ℝ)
    (hp : ∀ x, |p x| ≤ P) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highRawSampleVarianceDerivative n a V p F z| ≤ P ^ n * (↑n / a ^ 2) := by
  have hpp : |∏ i : Fin n, p (z.1 i)| ≤ P ^ n := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => abs_nonneg (p (z.1 i)))
      (fun i (_ : i ∈ Finset.univ) => hp (z.1 i))
  have hqprod (i : Fin n) :
      |∏ j ∈ Finset.univ.erase i, ternaryMass a (F (z.1 j)) V (z.2 j)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => by
      rw [abs_of_nonneg (hq (z.1 j) (z.2 j))]
      exact ternary_mass_le_one a _ V ha.ne' (hq _) _)
  have hs : |∑ i : Fin n, (∏ j ∈ Finset.univ.erase i,
      ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)| ≤
        ↑n / a ^ 2 := by
    calc
      _ ≤ ∑ i : Fin n, |(∏ j ∈ Finset.univ.erase i,
          ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact (mul_le_mul (hqprod i) (ternary_variance_derivative_abs_bound a ha (z.2 i))
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  rw [highRawSampleVarianceDerivative, abs_mul]
  exact mul_le_mul hpp hs (abs_nonneg _) (pow_nonneg hP n)
theorem highRawSampleVarianceDerivative_joint_measurable  (n a V p F) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2) := by
  have hx (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact (Finset.measurable_prod _ (fun i _ => hp.comp (hx i))).mul
    (Finset.measurable_sum _ (fun i _ =>
      (Finset.measurable_prod _ (fun j _ =>
        (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx j).prodMk (hy j)))).mul
      ((measurable_of_countable (ternaryVarianceDerivative a)).comp (hy i))))
end
section
variable {Ω : Type*} [MeasurableSpace Ω]
def highRawObservable  (n ) (a V : ℝ) (p F : Covariate d → ℝ)
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleLikelihood n a V p F z
    ∂highSampleReference d n
def highRawObservableVarianceDerivative  (n ) (a V : ℝ) (p F : Covariate d → ℝ)
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleVarianceDerivative n a V p F z
    ∂highSampleReference d n
theorem highRawObservable_measurable  (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (H : (Fin n → Observation d) → ℝ)
    (hH : Measurable H) : Measurable (fun ω => highRawObservable n a V (p ω) (F ω) H) := by
  have h  :=
    ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
  exact h.stronglyMeasurable.integral_prod_right'.measurable
theorem highRawObservable_abs_le  (n : ℕ) (a V P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (H : (Fin n → Observation d) → ℝ) (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservable n a V p F H| ≤ B * P ^ n * (highSampleReference d n).real Set.univ := by
  rw [highRawObservable, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a V P hP p F hp ha hq z)
      (abs_nonneg _) hB
theorem massPowerTilt_highReal_observable_mean  (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B) :
    (∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
      ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable n a V (p ω) (F ω) H ∂ν := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν m (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw hbound
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  have hM : Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2)) := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hpabs (ω : Ω) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hIntRaw : Integrable (fun z =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H (encodeDesignResponse a z.2))
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).mul hM).aestronglyMeasurable
      (|bRaw| ^ n * B)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) (p z.1) (F z.1)
        (hpabs z.1) ha (hq z.1) z.2) (hHb _) (abs_nonneg _) (pow_nonneg (abs_nonneg _) n)
  have h_massPowerTilt_highSample_integral : (∫ z, (fun z => H (encodeDesignResponse a z.2)) z ∂(massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z, highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * (fun z => H (encodeDesignResponse a z.2)) z
          ∂ν.prod (highSampleReference d n) := by
    let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
    have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
      highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
        (Filter.Eventually.of_forall (hraw ω))
    have hG := massPowerNormalizer_pos ν m (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw hbound
    have hu0 (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) :
        0 ≤ highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 (z.2.1 i)).1)
        (hq z.1 (z.2.1 i) (z.2.2 i)))
    have hD : Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 /
          massPowerNormalizer ν m n)) :=
      ENNReal.measurable_ofReal.comp ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).div_const _)
    rw [massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw,
      integral_withDensity_eq_integral_toReal_smul hD
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (div_nonneg (hu0 _) hG.le), smul_eq_mul]
    calc
      _ = ∫ z, (massPowerNormalizer ν m n)⁻¹ *
          (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * (fun z => H (encodeDesignResponse a z.2)) z)
            ∂ν.prod (highSampleReference d n) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by ring
      _ = _ := integral_const_mul _ _
  have he := h_massPowerTilt_highSample_integral
  rw [Measure.integral_compProd (by apply Integrable.of_bound hM.aestronglyMeasurable B; exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hHb _), MeasureTheory.integral_prod _ hIntRaw] at he
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only
      rw [highRealSampleKernel_apply,
        integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hH.stronglyMeasurable]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only [highRawObservable]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _
end
variable {Ω : Type*} [MeasurableSpace Ω]
theorem highRawObservable_hasDerivAt_path  (n a v η t T P B)
    (ha : 0 < a) (ht : 0 < t) (htT : t < T) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H ) (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω ) :
    HasDerivAt (fun u => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H)
      (-η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H) t := by
  let L : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z
  let L' : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)
  have hLM u : Measurable (L u) := by
    have hj : Measurable (Function.uncurry (fun ω z =>
        highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z)) :=
      highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    have hw : Measurable (fun z => highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z) :=
      hj.of_uncurry_left
    exact (hH.comp (encodeDesignResponse_measurable a)).mul hw
  have hL'M u : Measurable (L' u) := by
    have hj : Measurable (Function.uncurry (fun ω z =>
        highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)) :=
      highRawSampleVarianceDerivative_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    have hw : Measurable (fun z => highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z) :=
      hj.of_uncurry_left
    exact (hH.comp (encodeDesignResponse_measurable a)).mul (hw.const_mul (-η ^ 2))
  have hi : Integrable (L t) (highSampleReference d n) := by
    apply Integrable.of_bound (hLM t).aestronglyMeasurable (B * P ^ n)
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * t) (p ω) (F ω) z‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a (v - η ^ 2 * t) P
        hP (p ω) (F ω) (hpb ω) ha.ne' (hq t ⟨ht, htT⟩ ω) z) (abs_nonneg _) hB
  have hb u (hu : u ∈ Ioo 0 T) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
      ‖L' u z‖ ≤ B * (η ^ 2 * (P ^ n * (n / a ^ 2))) := by
    change ‖H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul (hHb _) (mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a (v - η ^ 2 * u) P ha hP
        (p ω) (F ω) (hpb ω) (hq u hu ω) z) (sq_nonneg η)) (by positivity) hB
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := highSampleReference d n) (F := L) (F' := L')
    (bound := fun _ => B * (η ^ 2 * (P ^ n * (n / a ^ 2))))
    (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hLM u).aestronglyMeasurable) hi
    (hL'M t).aestronglyMeasurable
    (Eventually.of_forall fun z u hu => hb u hu z)
    (integrable_const _)
    (Eventually.of_forall fun z u _ =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
        (H (encodeDesignResponse a z)))).2
  change HasDerivAt (fun u => ∫ z, L u z ∂highSampleReference d n) _ t
  apply hd.congr_deriv
  change (∫ z, L' t z ∂highSampleReference d n) =
    -η ^ 2 * ∫ z, H (encodeDesignResponse a z) *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) z ∂highSampleReference d n
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by dsimp [L']; ring
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_rawObservable_hasDerivAt (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba t : ℝ) (ht : 0 < t) (htT : t < T) (hBa : 0 ≤ Ba)
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
     (n : ℕ) (a v η P B : ℝ) (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Ioo 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    HasDerivAt (fun u => ∫ ω, highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
      ∂historyMarkedPrior dependent Δ u π activation)
      ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H
        ∂historyMarkedPrior dependent Δ t π activation) +
        historyMarkedPriorGenerator dependent hsymm Δ t π activation
          (fun ω => highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H)) t := by
  let G : ℝ → HistoryMarked dependent E → ℝ := fun u ω =>
    highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H
  let G' : ℝ → HistoryMarked dependent E → ℝ := fun u ω =>
    -η ^ 2 * highRawObservableVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) H
  let M : ℝ := B * P ^ n * (highSampleReference d n).real Set.univ
  let M' : ℝ := η ^ 2 * (B * (P ^ n * (n / a ^ 2)) * (highSampleReference d n).real Set.univ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hM' : 0 ≤ M' := by dsimp [M']; positivity
  have hGM u : Measurable (G u) := highRawObservable_measurable n a (v - η ^ 2 * u) p F hp hF H hH
  have h_highRawObservableVarianceDerivative_measurable (V : ℝ) : Measurable (fun ω => highRawObservableVarianceDerivative n a V (p ω) (F ω) H) := by
    have h  :=
      ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        (highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF)
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  have hG'M u : Measurable (G' u) :=
    (h_highRawObservableVarianceDerivative_measurable (v - η ^ 2 * u)).const_mul (-η ^ 2)
  have hGb u (hu : u ∈ Ioo 0 T) (ω : HistoryMarked dependent E) : |G u ω| ≤ M :=
    highRawObservable_abs_le n a (v - η ^ 2 * u) P B hP hB (p ω) (F ω) (hpb ω)
      ha.ne' (hq u hu ω) H hHb
  have hG'b u (hu : u ∈ Ioo 0 T) (ω : HistoryMarked dependent E) : |G' u ω| ≤ M' := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    have h_highRawObservableVarianceDerivative_abs_le (V) (p : Covariate d → ℝ) (F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y) : |highRawObservableVarianceDerivative n a V p F H| ≤
        B * (P ^ n * (↑n / a ^ 2)) * (highSampleReference d n).real Set.univ := by
      rw [highRawObservableVarianceDerivative, ← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le_const
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le n a V P ha hP p F hp hq z)
          (abs_nonneg _) hB
    exact mul_le_mul_of_nonneg_left (h_highRawObservableVarianceDerivative_abs_le (v - η ^ 2 * u) (p ω) (F ω) (hpb ω) (hq u hu ω)) (sq_nonneg η)
  have hGD (ω : HistoryMarked dependent E) u (hu : u ∈ Ioo 0 T) :
      HasDerivAt (fun w => G w ω) (G' u ω) u :=
    highRawObservable_hasDerivAt_path n a v η u T P B ha hu.1 hu.2 hP hB p F hp hF hpb hq H hH hHb ω
  have h_historyMarkedPrior_observable_product_rule : HasDerivAt (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π activation)
      ((∫ h, G' t h ∂historyMarkedPrior dependent Δ t π activation) +
        historyMarkedPriorGenerator dependent hsymm Δ t π activation (G t)) t := by
    let μ := historyMarkedReference dependent Δ π
    let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
    let ρ := historyReferenceRho Δ
    let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
    let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * Ba * C
    have : 0 < ρ := historyReferenceRho_pos Δ
    have : 0 ≤ C := by positivity
    have : 0 ≤ D := by dsimp [D]; positivity
    have hs (u : ℝ) (hu : u ∈ Ioo 0 T) : u * Ba / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    have hφ (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
        |historyMarkedDensity dependent ρ u activation h| ≤ C := by
      have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u Ba
        (historyReferenceRho_pos Δ) hu.1.le hBa activation habound (hs u hu) h
      have hn  :=
        (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
      rw [abs_of_nonneg hn]
      exact hb.2
    have hφd (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
        |historyMarkedDensityDerivative dependent ρ u activation h| ≤ D :=
      historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u Ba
        (historyReferenceRho_pos Δ) hu.1.le hBa activation habound (hs u hu) h
    let H : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
      G u h * historyMarkedDensity dependent ρ u activation h
    let H' : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
      G' u h * historyMarkedDensity dependent ρ u activation h +
        G u h * historyMarkedDensityDerivative dependent ρ u activation h
    have hHM (u : ℝ) : Measurable (H u) :=
      (hGM u).mul (historyMarkedDensity_measurable dependent ρ u activation hactivation)
    have hH'M (u : ℝ) : Measurable (H' u) :=
      ((hG'M u).mul (historyMarkedDensity_measurable dependent ρ u activation hactivation)).add
        ((hGM u).mul (historyMarkedDensityDerivative_measurable dependent ρ u activation hactivation))
    have hHb (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) : ‖H u h‖ ≤ M * C := by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGb u hu h) (hφ u hu h) (abs_nonneg _) hM
    have hH'b (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
        ‖H' u h‖ ≤ M' * C + M * D := by
      rw [Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul (hG'b u hu h) (hφ u hu h) (abs_nonneg _) hM')
        (by rw [abs_mul]; exact mul_le_mul (hGb u hu h) (hφd u hu h) (abs_nonneg _) hM))
    have hi : Integrable (H t) μ := Integrable.of_bound (hHM t).aestronglyMeasurable
      (M * C) (Eventually.of_forall (hHb t ⟨ht, htT⟩))
    have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := H) (F' := H') (bound := fun _ => M' * C + M * D)
      (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
      (Eventually.of_forall fun u => (hHM u).aestronglyMeasurable)
      hi (hH'M t).aestronglyMeasurable
      (Eventually.of_forall fun h u hu => hH'b u hu h)
      (integrable_const (M' * C + M * D))
      (Eventually.of_forall fun h u hu => (hGD h u hu).mul
        (historyMarkedDensity_hasDerivAt dependent ρ u activation h))).2
    have hi1 : Integrable (fun h => G' t h * historyMarkedDensity dependent ρ t activation h) μ := by
      apply Integrable.of_bound ((hG'M t).mul
        (historyMarkedDensity_measurable dependent ρ t activation hactivation)).aestronglyMeasurable (M' * C)
      exact Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
        exact mul_le_mul (hG'b t ⟨ht, htT⟩ h) (hφ t ⟨ht, htT⟩ h) (abs_nonneg _) hM'
    have hi2 : Integrable (fun h => G t h * historyMarkedDensityDerivative dependent ρ t activation h) μ := by
      apply Integrable.of_bound ((hGM t).mul
        (historyMarkedDensityDerivative_measurable dependent ρ t activation hactivation)).aestronglyMeasurable (M * D)
      exact Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
        exact mul_le_mul (hGb t ⟨ht, htT⟩ h) (hφd t ⟨ht, htT⟩ h) (abs_nonneg _) hM
    have hfirst := historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
      t Ba ht.le hBa π activation hactivation habound (hs t ⟨ht, htT⟩) (G' t)
    unfold historyMarkedExpectation at hfirst
    have hsecond := historyMarkedDensityDerivative_integral_eq_generator dependent hrefl hsymm Δ hΔ hlabels
      t Ba ht.le hBa π activation hactivation habound (hs t ⟨ht, htT⟩) (G t) (hGM t) M hM
        (hGb t ⟨ht, htT⟩)
    have h_historyMarkedPriorGenerator_eq_reference (hsmall : t * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * ↑Δ ^ 2)) (F : HistoryMarked dependent E → ℝ) : historyMarkedPriorGenerator dependent hsymm Δ t π activation F =
        historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
          (historyMarkedReference dependent Δ π) π activation F := by
      unfold historyMarkedPriorGenerator historyMarkedGeneratorExpectation
      apply Finset.sum_congr rfl
      intro j hj
      have hm : Measurable (fun p : HistoryMarked dependent E × E =>
          ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t activation p.1)) :=
        (historyMarkedDensity_measurable dependent (historyReferenceRho Δ) t activation hactivation).ennreal_ofReal.comp measurable_fst
      rw [historyMarkedPrior_eq_withDensity dependent Δ t π activation hactivation,
        prod_withDensity_left (historyMarkedDensity_measurable dependent _ t activation hactivation).ennreal_ofReal,
        integral_withDensity_eq_integral_toReal_smul hm
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro p
      have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
        (historyReferenceRho Δ) t Ba (historyReferenceRho_pos Δ) ht.le hBa activation habound hsmall p.1
      simp only [ENNReal.toReal_ofReal ((by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1), smul_eq_mul]
      ring
    rw [← (h_historyMarkedPriorGenerator_eq_reference (hs t ⟨ht, htT⟩) (G t))] at hsecond
    change HasDerivAt (fun u => ∫ h, H u h ∂μ) _ t at hd
    have he : (∫ h, H' t h ∂μ) =
        (∫ h, G' t h ∂historyMarkedPrior dependent Δ t π activation) +
          historyMarkedPriorGenerator dependent hsymm Δ t π activation (G t) := by
      rw [integral_add hi1 hi2, ← hfirst, hsecond]
    rw [he] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht htT] with u hu
    exact historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
      u Ba hu.1.le hBa π activation hactivation habound (hs u hu) (G u)
  have h := h_historyMarkedPrior_observable_product_rule
  simpa only [G, G', integral_const_mul] using h
end
variable {E : Type*} {d : ℕ}
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedDensity_lipschitzOn (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B : ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B)  [MeasurableSpace E]
    (a : E → ℝ) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    LipschitzOnWith ⟨ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J, by positivity⟩
      (fun t => historyMarkedDensity dependent ρ t a h) (Icc 0 T) := by
  apply (convex_Icc ↑0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u hu => (historyMarkedDensity_hasDerivAt dependent ρ u a h).hasDerivWithinAt)
  intro u hu
  apply NNReal.coe_le_coe.1
  change ‖historyMarkedDensityDerivative dependent ρ u a h‖ ≤ _
  rw [Real.norm_eq_abs]
  exact historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB a habound
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall) h
theorem historyMarkedDensityObservable_integrable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
     [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F ) (hF : Measurable F)
    (M ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    Integrable (fun h => F h * historyMarkedDensity dependent ρ t a h) μ := by
  apply Integrable.of_bound (hF.mul (historyMarkedDensity_measurable dependent ρ t a ha)).aestronglyMeasurable
    (M * (3 / 2 ) ^ Fintype.card J)
  apply Eventually.of_forall
  intro h
  change ‖F h * historyMarkedDensity dependent ρ t a h‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a habound hsmall h
  have hp  :=
    (by positivity : ↑0 ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  rw [abs_of_nonneg hp]
  exact mul_le_mul (hFbound h) hb.2 hp hM
end
section
variable {Ω : Type*} [MeasurableSpace Ω]
theorem highRawObservable_lipschitzOn  (n a v η T P B)
    (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (H ) (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) (ω ) :
    LipschitzOnWith
      ⟨B * (η ^ 2 * (P ^ n * (n / a ^ 2))) * (highSampleReference d n).real Set.univ, by positivity⟩
      (fun u => highRawObservable n a (v - η ^ 2 * u) (p ω) (F ω) H) (Icc 0 T) := by
  let c : ℝ := B * (η ^ 2 * (P ^ n * (n / a ^ 2)))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let L : ℝ → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun u z =>
    H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z
  have hLM u : Measurable (L u) := by
    have hj : Measurable (Function.uncurry (fun ω z =>
        highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z)) :=
      highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * u) p F hp hF
    have hw : Measurable (fun z => highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z) := hj.of_uncurry_left
    exact (hH.comp (encodeDesignResponse_measurable a)).mul hw
  have hi u (hu : u ∈ Icc 0 T) : Integrable (L u) (highSampleReference d n) := by
    apply Integrable.of_bound (hLM u).aestronglyMeasurable (B * P ^ n)
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z) * highRawSampleLikelihood n a (v - η ^ 2 * u) (p ω) (F ω) z‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a (v - η ^ 2 * u) P hP
        (p ω) (F ω) (hpb ω) ha.ne' (hq u hu ω) z) (abs_nonneg _) hB
  have hl (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
      LipschitzOnWith ⟨c, hc⟩ (fun u => L u z) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun u _ => ((highRawSampleLikelihood_hasDerivAt_path n a v η u (p ω) (F ω) z).const_mul
        (H (encodeDesignResponse a z))).hasDerivWithinAt)
    intro u hu
    apply NNReal.coe_le_coe.1
    change ‖H (encodeDesignResponse a z) * (-η ^ 2 *
      highRawSampleVarianceDerivative n a (v - η ^ 2 * u) (p ω) (F ω) z)‖ ≤ c
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul (hHb _) (mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a (v - η ^ 2 * u) P ha hP
        (p ω) (F ω) (hpb ω) (hq u hu ω) z) (sq_nonneg η)) (by positivity) hB
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  change dist (∫ z, L u z ∂highSampleReference d n) (∫ z, L v z ∂highSampleReference d n) ≤
    c * (highSampleReference d n).real Set.univ * dist u v
  rw [dist_eq_norm, ← integral_sub (hi u hu) (hi v hv)]
  have hb : ∀ᵐ z ∂highSampleReference d n, ‖L u z - L v z‖ ≤ c * dist u v :=
    Eventually.of_forall fun z => by
      have he : dist (L u z) (L v z) ≤ c * dist u v := (hl z).dist_le_mul u hu v hv
      simpa only [dist_eq_norm] using he
  calc
    _ ≤ c * dist u v * (highSampleReference d n).real Set.univ := norm_integral_le_of_norm_le_const hb
    _ = _ := by ring
variable {J : Type*} [Fintype J] [LinearOrder J]
end
section
section
def highTiltedObservableMean  [MeasurableSpace Ω] 
    (ν : Measure Ω) (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
    ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_tiltedObservable_eq_raw (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
     [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
     (n a v η aRaw bRaw) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F )
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    highTiltedObservableMean (historyMarkedPrior dependent Δ t π activation)
      n a (v - η ^ 2 * t) p F hp hF H =
      (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ t π activation := by
  have hs  :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
      (historyReferenceRho_pos Δ).le).trans hsmall
  let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.1 hBa π
    activation (by apply Integrable.of_bound hactivation.aestronglyMeasurable Ba; exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e) hcenter habound hs
  rw [highTiltedObservableMean, massPowerTilt_highReal_observable_mean
    (historyMarkedPrior dependent Δ t π activation) n a (v - η ^ 2 * t) p F hp hF
      aRaw bRaw haRaw hraw ha.ne' (hq t ht) H hH B hB hHb,
    massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp) n (hmass t ht)]
end
variable {J : Type*} [Fintype J] [LinearOrder J]
def highAppendLikelihoodAction  [MeasurableSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ) (j : J)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ e, activation e * highRawSampleLikelihood n a V
    (p (historyMarkedAppend dependent hsymm j (ω,e)))
    (F (historyMarkedAppend dependent hsymm j (ω,e))) z ∂π
theorem highAppendLikelihoodAction_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent hsymm π) [SFinite π] (activation ) (ha : Measurable activation) (n a V p F)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (j : J) :
    Measurable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2) := by
  have hcoord : Measurable (fun z :
      (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) × E =>
      (historyMarkedAppend dependent hsymm j (z.1.1,z.2),z.1.2)) :=
    ((historyMarkedAppend_measurable dependent hsymm j).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)
  have hj  :=
    (ha.comp measurable_snd).mul
      ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp hcoord)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable
theorem highAppendLikelihoodAction_abs_le  [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (j : J) (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| ≤ Ba * P^n := by
  rw [highAppendLikelihoodAction, ← Real.norm_eq_abs]
  have hb : ∀ e, ‖activation e * highRawSampleLikelihood n a V
      (p (historyMarkedAppend dependent hsymm j (ω,e)))
      (F (historyMarkedAppend dependent hsymm j (ω,e))) z‖ ≤ Ba * P^n := by
    intro e
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (habound e) (highRawSampleLikelihood_abs_le n a V P hP
      (p (historyMarkedAppend dependent hsymm j (ω,e)))
      (F (historyMarkedAppend dependent hsymm j (ω,e)))
      (hp _) ha (hq _) z) (abs_nonneg _) hBa
  simpa using norm_integral_le_of_norm_le_const (μ := π) (Eventually.of_forall hb)
theorem highAppendLikelihoodAction_prior_observable  [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] 
    (dependent hsymm)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (activation ) (ham : Measurable activation)
    (Ba ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n a V P B) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : a ≠ 0)
    (p F )
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B)
    (j : J) :
    (∫ z : HistoryMarked dependent E × E, highRawObservable n a V
        (p (historyMarkedAppend dependent hsymm j z))
        (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π) =
      ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
        H (encodeDesignResponse a z.2) *
          highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2
            ∂ν.prod (highSampleReference d n) := by
  have hg := (highRawObservable_measurable n a V p F hp hF H hH).comp
    (historyMarkedAppend_measurable dependent hsymm j)
  have hi : Integrable (fun z : HistoryMarked dependent E × E => highRawObservable n a V
      (p (historyMarkedAppend dependent hsymm j z))
      (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2) (ν.prod π) := by
    apply Integrable.of_bound (hg.mul (ham.comp measurable_snd)).aestronglyMeasurable
      ((B * P^n * (highSampleReference d n).real univ) * Ba)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, Function.comp_apply, abs_mul]
      exact mul_le_mul (highRawObservable_abs_le n a V P B hP hB _ _ (hpb _) ha (hq _) H hHb)
        (habound _) (abs_nonneg _) (by positivity)
  have hi' : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2)
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        (highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n))
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, Function.comp_apply, abs_mul]
      exact mul_le_mul (hHb _) (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
        habound n a V P hP ha p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  rw [MeasureTheory.integral_prod _ hi, MeasureTheory.integral_prod _ hi']
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    have h_highAppendLikelihoodAction_observable : (∫ e, activation e * highRawObservable n a V
        (p (historyMarkedAppend dependent hsymm j (ω,e)))
        (F (historyMarkedAppend dependent hsymm j (ω,e))) H ∂π) =
      ∫ z, H (encodeDesignResponse a z) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z
          ∂highSampleReference d n := by
      have hcoord : Measurable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
          (historyMarkedAppend dependent hsymm j (ω,z.1),z.2)) :=
        ((historyMarkedAppend_measurable dependent hsymm j).comp
          (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
      have hM : Measurable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
          activation z.1 * (H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V
            (p (historyMarkedAppend dependent hsymm j (ω,z.1)))
            (F (historyMarkedAppend dependent hsymm j (ω,z.1))) z.2)) :=
        (ham.comp measurable_fst).mul
          (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
            ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp hcoord))
      have hi : Integrable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
          activation z.1 * (H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V
            (p (historyMarkedAppend dependent hsymm j (ω,z.1)))
            (F (historyMarkedAppend dependent hsymm j (ω,z.1))) z.2))
          (π.prod (highSampleReference d n)) := by
        apply Integrable.of_bound hM.aestronglyMeasurable (Ba * (B * P^n))
        exact Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul (habound _) (mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a V P hP
            _ _ (hpb _) ha (hq _) z.2) (abs_nonneg _) hB) (by positivity) hBa
      calc
        _ = ∫ e, ∫ z, activation e * (H (encodeDesignResponse a z) * highRawSampleLikelihood n a V
            (p (historyMarkedAppend dependent hsymm j (ω,e)))
            (F (historyMarkedAppend dependent hsymm j (ω,e))) z) ∂highSampleReference d n ∂π := by
          simp_rw [highRawObservable, integral_const_mul]
        _ = ∫ z, ∫ e, activation e * (H (encodeDesignResponse a z) * highRawSampleLikelihood n a V
            (p (historyMarkedAppend dependent hsymm j (ω,e)))
            (F (historyMarkedAppend dependent hsymm j (ω,e))) z) ∂π ∂highSampleReference d n :=
          integral_integral_swap hi
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            dsimp only
            rw [highAppendLikelihoodAction, ← integral_const_mul]
            apply integral_congr_ae
            exact Eventually.of_forall fun e => by ring
    convert (h_highAppendLikelihoodAction_observable) using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun e => mul_comm _ _
end
variable {J : Type*} [Fintype J] [LinearOrder J]
def highHistoryLikelihoodDerivative  [MeasurableSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z) -
    η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z
def highHistoryLikelihoodScore  [MeasurableSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z /
    highRawSampleLikelihood n a V (p ω) (F ω) z
theorem highHistoryLikelihoodDerivative_measurable  [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2) := by
  exact (Finset.measurable_sum _ (fun j _ =>
    highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).sub
      ((highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF).const_mul (η^2))
theorem highRawSampleLikelihood_pos {Ω : Type*}  (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : ∀ ω x, 0 < p ω x)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (ω : Ω) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    0 < highRawSampleLikelihood n a V (p ω) (F ω) z :=
  Finset.prod_pos (fun i _ => mul_pos (hp ω _) (hq ω _ _))
theorem highHistoryLikelihoodDerivative_observable  [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
      H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
      ∂ν.prod (highSampleReference d n)) =
      (-η^2 * ∫ ω, highRawObservableVarianceDerivative n a V (p ω) (F ω) H ∂ν) +
        ∑ j, ∫ z : HistoryMarked dependent E × E,
          highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
            (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π := by
  let Q := HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))
  let μ : Measure Q := ν.prod (highSampleReference d n)
  let test : Q → ℝ := fun z => H (encodeDesignResponse a z.2)
  let A : J → Q → ℝ := fun j z =>
    highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2
  let D : Q → ℝ := fun z => highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2
  have htest : Measurable test := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hiA (j : J) : Integrable (fun z => test z * A j z) μ := by
    apply Integrable.of_bound (htest.mul
      (highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
        habound n a V P hP ha.ne' p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  have hiD : Integrable (fun z => test z * D z) μ := by
    apply Integrable.of_bound (htest.mul
      (highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF)).aestronglyMeasurable
      (B * (P^n * (↑n/a^2)))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) * highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le n a V P ha hP _ _ (hpb _) (hq _) z.2)
        (abs_nonneg _) hB
  have heD : (∫ z, test z * D z ∂μ) =
      ∫ ω, highRawObservableVarianceDerivative n a V (p ω) (F ω) H ∂ν := by
    exact MeasureTheory.integral_prod _ hiD
  calc
    _ = ∫ z, ((∑ j, test z * A j z) - η^2 * (test z * D z)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highHistoryLikelihoodDerivative, test, A, D]
        rw [mul_sub, Finset.mul_sum]
        ring
    _ = (∑ j, ∫ z, test z * A j z ∂μ) - η^2 * ∫ z, test z * D z ∂μ := by
      rw [integral_sub (integrable_finsetSum _ (fun j _ => hiA j)) (hiD.const_mul _),
        integral_finsetSum _ (fun j _ => hiA j), integral_const_mul]
    _ = _ := by
      rw [heD]
      have heA (j : J) := highAppendLikelihoodAction_prior_observable π dependent hsymm ν
        activation ham Ba hBa habound n a V P B hP hB ha.ne' p F hp hF hpb hq H hH hHb j
      have hs : (∑ j, ∫ z, test z * A j z ∂μ) =
          ∑ j, ∫ z : HistoryMarked dependent E × E,
            highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
              (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π := by
        apply Finset.sum_congr rfl
        intro j _
        exact (heA j).symm
      rw [hs]
      ring
theorem highHistoryLikelihoodDerivative_abs_le  [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P : ℝ) (hP : 0 ≤ P) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z| ≤
      (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * (↑n/a^2)) := by
  unfold highHistoryLikelihoodDerivative
  calc
    _ ≤ |∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| +
        |η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z)
          ↑0 (η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z)
    _ ≤ (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * (↑n/a^2)) := by
      apply add_le_add
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc
          _ ≤ ∑ j : J, Ba * P^n := Finset.sum_le_sum (fun j _ =>
            highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa habound n a V P hP
              ha.ne' p F hpb hq j ω z)
          _ = _ := by simp
      · rw [abs_mul, abs_of_nonneg (sq_nonneg η)]
        exact mul_le_mul_of_nonneg_left (highRawSampleVarianceDerivative_abs_le n a V P ha hP
          (p ω) (F ω) (hpb ω) (hq ω) z) (sq_nonneg η)
end NearlyMinimax
