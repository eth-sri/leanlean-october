module

public import proofs.RAFCriticalWindowQuantitative.SeedDeficit

public section

namespace RAFCriticalWindowQuantitative
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

variable (b : ℚ)

/-- Uniform finite closure deficit at the executable seed cutoff. -/
theorem effective_closure_deficit  (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (d : ℕ) (hd : 0 < d) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    let η := (m : ENNReal)⁻¹/(m+1)
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure (10*k) $ staticOpenReactions ω).card+d ≤ Fintype.card (Molecule N)} ≤
      η + (Fintype.card $ Molecule N)*η/d := by
  have hk := (seedIndex_spec b hb hb1 m).1
  have hbound := selected_contour_deficit b hb hb1 m hm
  rw [show 1 / (m*(m+1)) = (m : ENNReal)⁻¹/(m+1) by
    simp [div_eq_mul_inv, ENNReal.mul_inv]] at hbound
  have hL : 2*(5*seedIndex b hb hb1 m) ≤ 10*seedIndex b hb hb1 m := by omega
  rw [card_molecules_exact, ← actualBinaryWords_card]
  have hbad s : staticReactionMeasure N (rationalParameter b hb.le hb1) {ω | s ∈ badMolecularWords hL ω} ≤
      (m : ENNReal)⁻¹/(m+1) := by
    simpa only [badMolecularWords, Finset.mem_filter, Finset.mem_univ, true_and] using
      (measure_moleculeContourBad_le hL le_rfl s.val _).trans hbound
  have hm := (meas_ge_le_lintegral_div (f := fun ω => ((badMolecularWords hL ω).card))
    (measurable_of_finite _).aemeasurable (ε := d) (by positivity) $ by simp).trans
    (ENNReal.div_le_div_right ((lintegral_bad_card _ _).trans_le
      ((Finset.sum_le_sum fun x _ => hbad x).trans_eq $ by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])) _)
  refine (measure_mono fun ω hω => ?_).trans $ (measure_union_le
    {ω | actualBinaryRoot N hN ∈ badMolecularWords hL ω} {ω | d ≤ (badMolecularWords hL ω).card}).trans
    (add_le_add (hbad _) $ by simpa using hm)
  by_cases hr : actualBinaryRoot N hN ∈ badMolecularWords hL ω
  · exact .inl hr
  have hreach x (hx : x ∉ badMolecularWords hL ω) : x ∈ rootedMolecularWords hL ω := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← molecularWordVertex_food (N := N) (actualBinaryRoot N hN).val $ by simp [actualBinaryRoot]; omega]
    generalize 10 * seedIndex b hb hb1 m = L at *
    by_contra hn
    obtain ⟨f, hneq, hcut, hnonempty, hmin⟩ := exists_disabled_separating_bond (wordBasicEdges L N) _
      Prod.fst wordEdgeParent _ _ (wordGraph_connected L N _ _) hn
    rw [molecularWordVertex_label f, molecularWordVertex_label f] at hneq
    change (wordGraphCut f).Nonempty at hnonempty
    have hfailed : contourDetoursFailed hL (wordGraphCut f) (fun r ω => ω r) ω := fun d hd hopen =>
      let h := Finset.mem_sdiff.mp $ hcut (Finset.mem_product.mp hd).1
      h.2 $ Finset.mem_filter.mpr ⟨h.1, d.2, hopen⟩
    have key c (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card) s
        (hs : s ∈ wordMolecularSide f c) : moleculeContourBad hL s ω := by
      refine ⟨(wordGraphCut f).card-1, wordGraphCut f, ?_, hfailed⟩
      simp_all
      obtain ⟨e, he⟩ := hnonempty
      suffices ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card by
        obtain ⟨p, hp⟩ := this
        exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.filter_subset _ _ he,
          endWord_walk_mem_ball p _ hp⟩, wordBond_mem_anchored f hmin e he⟩
      have hconn d hd := wordBond_diamond_connected f hmin e d he hd
      have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
      have hloc d hd := wordContour_product_locality _ hsub e he hconn d hd
      generalize hrdef : 4 * (wordGraphCut f).card = r
      have hcut d (hd : d ∈ wordGraphCut f) : d.1.val.length ≤ e.1.val.length + r := by
        obtain ⟨p, hp⟩ := hloc d hd
        have hh := endWord_walk_length_bound p
        omega
      have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
      have hL : L < e.1.val.length := by
        rcases e.1.property with h | h
        · exact (hn $ Subtype.ext h).elim
        omega
      have hLM : L < e.1.val.length + r := by omega
      obtain ⟨hsU, hslabel⟩ := Finset.mem_filter.mp hs
      have hsN := ((mem_actualBinaryWords s N).mp hsU).2
      obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val [] ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
      by_cases hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card
      · have hsM : s.length ≤ e.1.val.length + r := by
          by_cases hMN : e.1.val.length + r < N
          · refine (molecular_minor_side_below_band N _ hMN (wordMolecularSide f c)
              (Finset.filter_subset _ _) hminor (fun u hu v hv hMu hMv => ?_) s hs).le
            have heq := highBand_label_constant (boundedWordLabel f) _ N hMN
              (wordCut_above_boundary_parents f hLM hcut) u v
              ⟨hMu, ((mem_actualBinaryWords u N).mp hu).2⟩
              ⟨hMv, ((mem_actualBinaryWords v N).mp hv).2⟩
            simp only [wordMolecularSide, Finset.mem_filter, hu, true_and]
            simp_all
          omega
        grind
      obtain ⟨core, left, right, hne, ha, hl, hr⟩ := word_exists_padded_core e.1.val r $ by omega
      have hcore d (hd : d ∈ wordGraphCut f) : ∃ a b : List Bool, d.1.val = a ++ core ++ b :=
        let ⟨p, hp⟩ := hloc d hd
        endWord_walk_protects_core p core left right ha (by omega) $ by omega
      have hlen : e.1.val.length = core.length + 2 * r := by
        grind
      by_cases hc : c = f (boundedFoodRoot L N)
      · subst hc
        have hp := Finset.card_sdiff_add_card_eq_card (s := wordMolecularSide f $ f $ boundedFoodRoot L N)
          (Finset.filter_subset _ _)
        rw [molecular_food_complement] at hp hminor
        rw [actualBinaryWords_card] at hp
        have hc : ((wordNonfoodSide f).image fun u : BoundedFoodWord L N => u.val).card <
            2 ^ (2 * (3 * r + 1)) :=
          core_containing_words_card_lt _ core _ (Finset.forall_mem_image.2 fun u hu =>
            wordCut_nonfood_side_contains_core f core hcore _ (Finset.mem_filter.1 hu).2) $ Finset.forall_mem_image.2 fun u hu =>
            (wordCut_nonfood_length_le f hLM hcut core hne hcore _ (Finset.mem_filter.1 hu).2).trans $ by omega
        rw [Finset.card_image_of_injective (f := fun u : BoundedFoodWord L N => u.val) _ Subtype.val_injective] at hc
        have hN : N ≤ 2 * (3 * r + 1) := (pow_le_pow_iff_right₀ (by omega : 1 < 2)).mp $ by
          omega
        grind
      obtain ⟨v, rfl, hv⟩ := nonfood_label_preimage f s hsU $ hslabel ▸ hc
      have hvl := wordCut_nonfood_length_le f hLM hcut core hne hcore v hv
      obtain ⟨p, hp⟩ := endWord_common_core_walk v.val e.1.val core
        (wordCut_nonfood_side_contains_core f core hcore v hv) ⟨left, right, ha⟩
      grind
    have h1 := fun h => hr $ Finset.mem_filter.mpr ⟨Finset.mem_univ _, key _ h _
      (Finset.mem_filter.mpr ⟨(actualBinaryRoot N hN).property, rfl⟩)⟩
    have h2 := fun h => hx $ Finset.mem_filter.mpr ⟨Finset.mem_univ _, key _ h _
      (Finset.mem_filter.mpr ⟨x.property, rfl⟩)⟩
    rw [wordMolecularSide_complement_of_ne f _ _ hneq] at h1
    rw [wordMolecularSide_complement_of_ne f _ _ hneq.symm] at h2
    simp at h1 h2
    omega
  have := (Finset.card_le_card (s := Finset.univ) fun x _ => (Classical.em _).elim (Finset.mem_union_left _)
    fun hx => Finset.mem_union_right _ $ hreach x hx).trans
    (Finset.card_union_le (badMolecularWords hL ω) $ rootedMolecularWords hL ω)
  have hh := Finset.card_le_card_of_injOn _ (rootedMolecularWords_source_mem hL ω) actualWordSource_injective.injOn
  simp at *
  grind

/-- The computed cutoff gives the literal uniform supplied-seed mass guarantee. -/
theorem effective_static_bulk  (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        m*(temporaryReactionClosure (10*k) $ staticOpenReactions ω).card <
          (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  intro N hN
  have hUd := Nat.lt_mul_div_succ (Fintype.card $ Molecule N) hm
  refine (measure_mono fun ω hω => ?_).trans $ (effective_closure_deficit b hb hb1 m hm N hN _
    (Nat.succ_pos $ Fintype.card (Molecule N)/m)).trans ?_
  · have := Nat.div_mul_le_self (Fintype.card $ Molecule N) m
    have : m-1+1 = m := by omega
    simp only [Set.mem_ofPred_eq] at *
    nlinarith
  · calc _ ≤ (m : ℝ≥0∞)⁻¹/(m+1) + m*((m : ℝ≥0∞)⁻¹/(m+1)) := add_le_add le_rfl
          (ENNReal.div_le_of_le_mul $ by rw [mul_right_comm]; gcongr; exact_mod_cast hUd.le)
      _ = _ := by rw [← one_add_mul, add_comm, ENNReal.mul_div_cancel (by simp) $ by simp]

end RAFCriticalWindowQuantitative
