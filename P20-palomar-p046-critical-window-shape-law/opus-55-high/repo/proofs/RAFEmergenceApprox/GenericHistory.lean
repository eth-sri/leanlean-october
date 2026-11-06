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
  Measure.pi $ fun r => colLaw X $ p r

instance law_probability (p : R → I) : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance

theorem probability_prop_eq_of_false {α : Type*} [MeasurableSpace α] (μ : Measure α) (ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → Prop} (hf : Measurable f)
    (h : μ {a | ¬ f a} = ν {False}) : μ.map f = ν := by
  have e : f ⁻¹' {False} = {a | ¬ f a} := by simp_all
  refine Measure.ext_of_singleton fun q => ?_
  rw [Measure.map_apply hf $ MeasurableSet.singleton _]
  by_cases hq : q
  · rw [eq_true hq, show ({True} : Set Prop) = {False}ᶜ by simp_all, Set.preimage_compl,
      prob_compl_eq_one_sub $ hf $ MeasurableSet.singleton _, prob_compl_eq_one_sub $ MeasurableSet.singleton _, e, h]
  simp_all

variable (ω : R → X → Prop)

def catalystPoolOpen  (C : Finset X) (r : R) : Prop :=
  ∃ x ∈ C, ω r x

def catalystColumnHistory  (C : ℕ → Finset X)
    (r : R) (T d : ℕ) : Prop :=
  decreasingHistory (fun t => catalystPoolOpen ω (C t) r) T d

variable (p : I)

theorem closed_probability  (C : Finset X) :
    colLaw X p {v | ¬ ∃ x ∈ C, v x} = (toNNReal (σ p) : ENNReal)^C.card := by
  rw [show {v : X → Prop | ¬ ∃ x ∈ C, v x} = Set.univ.pi fun x => if x ∈ C then {False} else Set.univ by
    ext; simp, colLaw]
  simp [apply_ite, ambientCoordLaw]

theorem column_history_probability  (C : ℕ → Finset X) (hC : Antitone C)
    (T d : ℕ) (hd : d ≤ T+1) :
    colLaw X p {v | decreasingHistory (∃ x ∈ C ·, v x) T d} =
      columnHistoryWeight (toNNReal $ σ p) (fun t => (C t).card) T d := by
  have hm (v : X → Prop) (a b) (h : a ≤ b) : (∃ x ∈ C b, v x) → ∃ x ∈ C a, v x := by
    aesop
  unfold columnHistoryWeight
  split_ifs with hz hs
  · simp only [hz, fun v => decreasingHistory_zero_iff _ T $ hm v, closed_probability]
  · obtain rfl : d = T+1 := by omega
    rw [← closed_probability, ← prob_compl_eq_one_sub (Set.toFinite _).measurableSet]
    simp [fun v => decreasingHistory_survives_iff _ T $ hm v, Set.compl_ofPred]
  · rw [← closed_probability, ← closed_probability, ← measure_sdiff (s₁ := {v | ¬ ∃ x ∈ C d, v x}) (s₂ := {v | ¬ ∃ x ∈ C $ d-1, v x})
      (fun v hv hp => hv $ hm v (d-1) d (by omega) hp) (Set.toFinite _).measurableSet.nullMeasurableSet $ measure_ne_top _ _]
    congr 1; ext; simp [decreasingHistory_dies_iff _ T d (by omega) (by omega) $ hm _]


theorem measure_catalystHistories (p : R → I) (C : ℕ → Finset X) (hC : Antitone C)
    (S : Finset R) (T : ℕ) (death : R → ℕ) (hd : ∀ r ∈ S, death r ≤ T+1) :
    law (X := X) p {ω | ∀ r ∈ S, catalystColumnHistory ω C r T $ death r} =
      ∏ r ∈ S, columnHistoryWeight (toNNReal $ σ $ p r) (fun t => (C t).card) T (death r) := by
  rw [show {ω | ∀ r ∈ S, catalystColumnHistory ω C r T $ death r} = Set.univ.pi fun r => if r ∈ S then
    {v | decreasingHistory (∃ x ∈ C ·, v x) T $ death r} else Set.univ by
      ext; simp [catalystColumnHistory, catalystPoolOpen], law, Measure.pi_pi]
  simp only [apply_ite, measure_univ, Finset.prod_ite_mem, Finset.univ_inter]
  exact Finset.prod_congr rfl fun r hr => column_history_probability (p r) C hC T (death r) $ hd r hr

noncomputable def catalystActive  (C : Finset X) : Finset R :=
  Finset.univ.filter $ catalystPoolOpen ω C


omit [Fintype X] in
@[simp] theorem mem_catalystActive (ω : R → X → Prop) (C : Finset X) (r : R) :
    r ∈ catalystActive ω C ↔ catalystPoolOpen ω C r := by simp [catalystActive]

omit [Fintype X] in
theorem catalystActive_mono (ω : R → X → Prop) : Monotone (catalystActive ω) :=
  fun _ _ h _ => by simp; exact fun ⟨x, hx, hω⟩ => ⟨x, h hx, hω⟩

/-- Convert a prescribed process history into fixed column constraints.
The transform can be identity (source) or cardinality-indexed prefixes. -/
theorem peeling_event_eq_column_histories
    (transform : Finset X → Finset X)
    (closure : Finset R → Finset X)
    (history : ℕ → Finset R) (T : ℕ) (death : R → ℕ)
    (hdeath : ∀ r t, t ≤ T → (r ∈ history t ↔ t < death r)) :
    {ω : R → X → Prop | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω $ transform ·) closure t = history t} =
    {ω | ∀ r ∈ (Finset.univ : Finset R),
      catalystColumnHistory ω (transform $ prescribedPoolAt closure history ·)
        r T $ death r} := by
  simp only [peeling_history_iff]
  simp only [Finset.ext_iff, mem_catalystActive]
  grind [catalystColumnHistory, decreasingHistory]

variable (p : R → I) (closure : Finset R → Finset X)

/-- The source process and its ordered-initialSegment replacement give exactly the
same probability to every prescribed active-set history. Nondecreasing histories on
the finite horizon have probability zero for both processes. -/
theorem peeling_history_probability_eq_prefix_any  (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset X) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card X, (initialSegment k).card = k)
    (history : ℕ → Finset R) (T : ℕ) :
    law (X := X) p {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    law (X := X) p {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω $ initialSegment C.card) closure t = history t} := by
  have key (f : (R → X → Prop) → Finset X → Finset R) (hf : ∀ ω, Monotone $ f ω) :
      {ω | ∀ t ≤ T, peelingActiveAt (f ω) closure t = history t} =
      if Antitone fun t => history (min t T) then
        {ω | ∀ t ≤ T, peelingActiveAt (f ω) closure t = history (min t T)} else ∅ := by
    split_ifs with hg
    · simp_all
    refine Set.eq_empty_iff_forall_notMem.mpr fun ω h => hg fun a b hab => ?_
    dsimp only; rw [← h _ $ min_le_right _ _, ← h _ $ min_le_right _ _]
    exact peelingActiveAt_antitone _ closure (hf ω) hclosure $ min_le_min_right T hab
  rw [key _ catalystActive_mono, key _ fun ω C D h => catalystActive_mono ω $ hprefix $ Finset.card_le_card h]
  split_ifs with hg
  · choose death hbound hpattern using fun r =>
      exists_history_death (fun t => r ∈ history (min t T)) T fun _ _ hab hr => hg hab hr
    have hc := prescribedPoolAt_antitone closure hclosure _ hg
    erw [peeling_event_eq_column_histories id closure _ T death hpattern,
      peeling_event_eq_column_histories (fun C => initialSegment C.card) closure _ T death hpattern,
      measure_catalystHistories p _ hc _ T death fun r _ => hbound r,
      measure_catalystHistories p _ (fun a b hab => hprefix $ Finset.card_le_card $ hc hab) _ T death
        fun r _ => hbound r]
    simp [hcard _ $ Finset.card_le_univ _]
  rfl

theorem activeTrace_map_eq_scalar
    (hclosure : Monotone closure) (T : ℕ) :
    (law (X := X) p).map (fun ω => activeTrace (catalystActive ω) closure T) =
      (law (X := X) p).map (fun ω => activeTrace
        (fun C => catalystActive ω $ finiteInitialSegment X C.card) closure T) := by
  refine Measure.ext_of_singleton fun H => ?_
  simp only [Measure.map_apply (measurable_of_finite _) $ MeasurableSet.singleton H, Set.preimage,
    Set.mem_singleton_iff, activeTrace_eq_iff]
  exact peeling_history_probability_eq_prefix_any p closure hclosure _ (finiteInitialSegment_mono X)
    (card_finiteInitialSegment X) _ T

end RAFEmergenceApprox.Generic
