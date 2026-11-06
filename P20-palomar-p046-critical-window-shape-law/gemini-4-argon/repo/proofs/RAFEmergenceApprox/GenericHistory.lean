module

public import proofs.HordijkSteelThreshold.ScalarHistoryDistribution

@[expose] public section

namespace RAFEmergenceApprox.Generic
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Concrete

variable {X R : Type*} [Fintype X] [Fintype R]

noncomputable def colLaw (X : Type*) [Fintype X] (p : I) : Measure (X → Prop) :=
  Measure.pi (fun _ : X => ambientCoordLaw p)

instance colLaw_probability (p : I) : IsProbabilityMeasure (colLaw X p) := by
  unfold colLaw
  infer_instance

noncomputable def law (p : R → I) : Measure (R → X → Prop) :=
  Measure.pi (fun r => colLaw X (p r))

instance law_probability (p : R → I) : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance

theorem closed_probability (p : I) (C : Finset X) :
    colLaw X p {v | ¬ ∃ x ∈ C, v x} = (toNNReal (σ p) : ENNReal)^C.card := by
  rw [colLaw, show {v : X → Prop | ¬ ∃ x ∈ C, v x} = (C : Set X).pi fun _ => {False} by ext; simp,
    Measure.pi_pi_finset]
  simp [ambientCoordLaw_false]

theorem column_history_probability (p : I) (C : ℕ → Finset X) (hC : Antitone C)
    (T d : ℕ) (hd : d ≤ T+1) :
    colLaw X p {v | decreasingHistory (fun t => ∃ x ∈ C t, v x) T d} =
      columnHistoryWeight (toNNReal (σ p)) (fun t => (C t).card) T d := by
  have hm (v : X → Prop) (a b : ℕ) (hab : a ≤ b) : (∃ x ∈ C b, v x) → ∃ x ∈ C a, v x :=
    fun ⟨x, hx, hv⟩ => ⟨x, hC hab hx, hv⟩
  by_cases hz : d = 0
  · subst d
    simp only [columnHistoryWeight, ↓reduceIte]
    rw [show {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T 0} =
      {v | ¬ ∃ x ∈ C 0, v x} by ext v; exact decreasingHistory_zero_iff _ _ (hm v), closed_probability]
  · by_cases hs : T < d
    · obtain rfl : d = T+1 := by omega
      simp only [columnHistoryWeight, ite_eq_right hz, ite_eq_left hs]
      have he : {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T (T+1)} =
          {v | ¬ ∃ x ∈ C T, v x}ᶜ := by
        ext v; simpa [not_not] using decreasingHistory_survives_iff _ _ (hm v)
      rw [he, measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _), measure_univ, closed_probability]
    · simp only [columnHistoryWeight, ite_eq_right hz, ite_eq_right hs]
      have he : {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T d} =
          {v | ¬ ∃ x ∈ C d, v x} \ {v | ¬ ∃ x ∈ C (d-1), v x} := by
        ext v; simpa [Set.mem_sdiff, not_not] using decreasingHistory_dies_iff _ _ _ (by omega) (by omega) (hm v)
      have hsub : {v : X → Prop | ¬ ∃ x ∈ C (d-1), v x} ⊆ {v | ¬ ∃ x ∈ C d, v x} :=
        fun v hv hp => hv (hm v (d-1) d (by omega) hp)
      rw [he, measure_sdiff hsub (Set.toFinite _).measurableSet.nullMeasurableSet (measure_ne_top _ _),
        closed_probability, closed_probability]

theorem measure_catalystHistories (p : R → I) (C : ℕ → Finset X) (hC : Antitone C)
    (T : ℕ) (death : R → ℕ) (hd : ∀ r, death r ≤ T+1) :
    law (X := X) p {ω | ∀ r : R, decreasingHistory (fun t => ∃ x ∈ C t, ω r x) T (death r)} =
      ∏ r : R, columnHistoryWeight (toNNReal (σ (p r))) (fun t => (C t).card) T (death r) := by
  let E r := {v : X → Prop | decreasingHistory (fun t => ∃ x ∈ C t, v x) T (death r)}
  have hi : iIndepFun (fun r (ω : R → X → Prop) => ω r) (law (X := X) p) :=
    iIndepFun_pi fun _ => measurable_id.aemeasurable
  have he : {ω : R → X → Prop | ∀ r : R, decreasingHistory (fun t => ∃ x ∈ C t, ω r x) T (death r)} =
      ⋂ r ∈ Finset.univ, (fun ω : R → X → Prop => ω r) ⁻¹' E r := by ext; simp [E]
  rw [he, hi.measure_inter_preimage_eq_mul Finset.univ (fun r _ => (Set.toFinite (E r)).measurableSet)]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [law, ← Measure.map_apply (measurable_pi_apply r) (Set.toFinite (E r)).measurableSet,
    (measurePreserving_eval (fun r => colLaw X (p r)) r).map_eq]
  exact column_history_probability (p r) C hC T (death r) (hd r)

omit [Fintype X] in
noncomputable def catalystActive (ω : R → X → Prop) (C : Finset X) : Finset R :=
  Finset.univ.filter fun r => ∃ x ∈ C, ω r x

omit [Fintype X] in
@[simp] theorem mem_catalystActive (ω : R → X → Prop) (C : Finset X) (r : R) :
    r ∈ catalystActive ω C ↔ ∃ x ∈ C, ω r x := by
  simp [catalystActive]

omit [Fintype X] in
theorem catalystActive_mono (ω : R → X → Prop) : Monotone (catalystActive ω) :=
  fun _ _ h _ hr => (mem_catalystActive ω _ _).mpr <|
    let ⟨x, hx, hω⟩ := (mem_catalystActive ω _ _).mp hr; ⟨x, h hx, hω⟩

theorem peeling_event_eq_column_histories (transform : Finset X → Finset X)
    (closure : Finset R → Finset X) (history : ℕ → Finset R) (T : ℕ) (death : R → ℕ)
    (hdeath : ∀ r t, t ≤ T → (r ∈ history t ↔ t < death r)) :
    {ω : R → X → Prop | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (transform C)) closure t = history t} =
    {ω | ∀ r : R, decreasingHistory
      (fun t => ∃ x ∈ transform (prescribedPoolAt closure history t), ω r x) T (death r)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, peeling_history_iff]
  exact ⟨fun h r t ht => by rw [← hdeath r t ht, ← h t ht, mem_catalystActive],
    fun h t ht => Finset.ext fun r => by rw [mem_catalystActive]; exact (h r t ht).trans (hdeath r t ht).symm⟩

theorem peeling_statistic (p : R → I) (closure : Finset R → Finset X)
    (hclosure : Monotone closure) (T : ℕ) (stat : Finset R → Prop) :
    law (X := X) p {ω | stat (peelingActiveAt (catalystActive ω) closure T)} =
      law (X := X) p {ω | stat (peelingActiveAt
        (fun C => catalystActive ω (finiteInitialSegment X C.card)) closure T)} := by
  let f₁ (ω : R → X → Prop) (t : Fin (T + 1)) := peelingActiveAt (catalystActive ω) closure t
  let f₂ (ω : R → X → Prop) (t : Fin (T + 1)) :=
    peelingActiveAt (fun C => catalystActive ω (finiteInitialSegment X C.card)) closure t
  have hmap : (law (X := X) p).map f₁ = (law (X := X) p).map f₂ := by
    apply Measure.ext_of_singleton; intro H
    rw [Measure.map_apply (measurable_of_finite _) (.singleton H),
      Measure.map_apply (measurable_of_finite _) (.singleton H)]
    let history t := if ht : t ≤ T then H ⟨t, Nat.lt_succ_of_le ht⟩ else ∅
    have he (A : ℕ → Finset R) : ((fun t : Fin (T + 1) => A t) = H) ↔ ∀ t ≤ T, A t = history t :=
      ⟨fun h t ht => by simpa [history, ht] using congrFun h ⟨t, Nat.lt_succ_of_le ht⟩,
       fun h => funext fun ⟨t, ht⟩ => by simpa [history, Nat.le_of_lt_succ ht] using h t (Nat.le_of_lt_succ ht)⟩
    simp only [f₁, f₂, Set.preimage, Set.mem_singleton_iff, he]
    by_cases hg : Antitone history
    · choose death hbound hpattern using fun r : R =>
        exists_history_death (fun t => r ∈ history t) T fun _ _ hab hr => hg hab hr
      have hc := prescribedPoolAt_antitone closure hclosure history hg
      rw [peeling_event_eq_column_histories (fun C => C) closure history T death hpattern,
        peeling_event_eq_column_histories (fun C => finiteInitialSegment X C.card) closure history T death hpattern,
        measure_catalystHistories p _ hc T death hbound,
        measure_catalystHistories p _ (fun _ _ h => finiteInitialSegment_mono X (Finset.card_le_card (hc h))) T death hbound]
      simp_rw [card_finiteInitialSegment X _ (Finset.card_le_univ _)]
    · have h0 (resp : (R → X → Prop) → Finset X → Finset R) (hm : ∀ ω, Monotone (resp ω)) :
          {ω : R → X → Prop | ∀ t ≤ T, peelingActiveAt (resp ω) closure t = history t} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun ω h => hg fun a b hab => by
          by_cases hb : b ≤ T
          · rw [← h b hb, ← h a (hab.trans hb)]
            exact peelingActiveAt_antitone _ closure (hm ω) hclosure hab
          · simp [history, hb]
      rw [h0 _ catalystActive_mono, h0 _ fun ω _ _ h =>
        catalystActive_mono ω (finiteInitialSegment_mono X (Finset.card_le_card h))]
  have he := congrArg (fun μ => μ {H : Fin (T + 1) → Finset R | stat (H ⟨T, Nat.lt_succ_self T⟩)}) hmap
  rwa [Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at he

end RAFEmergenceApprox.Generic
