module

public import NearlyMinimax.HistoryShapes

@[expose] public section

/-!
# Dependent-pair projections determine a history shape

The projections of a word onto each dependent pair of labels are invariant
under consecutive independent exchanges. Conversely, equality of these
projections produces such exchanges, by moving the first letter through its
independent predecessors. This is the concrete injective encoding used for
the finite reference-law normalizer in `lower_heaps`.
-/

noncomputable section
namespace NearlyMinimax

abbrev DependenceHeap {J : Type*} (r : J → J → Prop) := HistoryShape (fun a b => ¬ r a b)

variable {J : Type*} [DecidableEq J]

def historyPairProjection (i j : J) (word : List J) : List J :=
  word.filter (fun x => decide (x = i ∨ x = j))

section
variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {i j : J}
    (hij : dependent i j) {u v : List J}
include hij

theorem historyPairProjection_exchange
    (h : IndependentHistoryExchange (fun a b => ¬ dependent a b) u v) :
    historyPairProjection i j u = historyPairProjection i j v := by
  cases h with
  | swap before after x y hxy =>
    by_cases hx : x = i ∨ x = j
    · have hy : ¬ (y = i ∨ y = j) := fun hy => hxy (by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | exact hij | exact symm hij | exact Std.Refl.refl _)
      simp [historyPairProjection, List.filter_append, hx, hy]
    · by_cases hy : y = i ∨ y = j <;> simp [historyPairProjection, List.filter_append, hx, hy]

theorem historyPairProjection_shape_invariant
    (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    historyPairProjection i j u = historyPairProjection i j v := by
  induction h with
  | rel _ _ h => exact historyPairProjection_exchange hij h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end

theorem history_first_decomposition {a : J} {word : List J} (ha : a ∈ word) :
    ∃ before after, word = before ++ a :: after ∧ a ∉ before := by
  induction word with
  | nil => simp at ha
  | cons b word ih =>
    by_cases hba : b = a
    · subst b; exact ⟨[], word, rfl, by simp⟩
    · grind

theorem historyPairProjection_prefix_head {a b : J} {before after : List J}
    (ha : a ∉ before) (hb : b ∈ before) :
    (historyPairProjection a b (before ++ a :: after)).head? = some b := by
  induction before with
  | nil => simp at hb
  | cons c before ih =>
    have hca : c ≠ a := fun h => ha (List.mem_cons.2 (Or.inl h.symm))
    have habefore  := fun h => ha (List.mem_cons.2 (Or.inr h))
    by_cases hcb : c = b
    · subst c; simp [historyPairProjection]
    · simpa [historyPairProjection, hca, hcb] using ih habefore ((List.mem_cons.1 hb).resolve_left (Ne.symm hcb))

omit [DecidableEq J] in
theorem historyShapeRelation_cons {independent : J → J → Prop} (a : J) {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: u) (a :: v) := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy =>
      exact .rel _ _ (IndependentHistoryExchange.swap (a :: before) after x y hxy)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

omit [DecidableEq J] in
theorem historyShapeRelation_move_first {independent : J → J → Prop} (a : J) (before after : List J)
    (hbefore : ∀ b ∈ before, independent b a) :
    Relation.EqvGen (IndependentHistoryExchange independent) (before ++ a :: after) (a :: (before ++ after)) := by
  induction before with
  | nil => exact .refl _
  | cons b before ih =>
    exact .trans _ _ _ (historyShapeRelation_cons b (ih (fun c hc => hbefore c (List.mem_cons_of_mem _ hc))))
      (.rel _ _ (IndependentHistoryExchange.swap [] _ b a (hbefore b List.mem_cons_self)))

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent]

/-- Equality of the actual dependent pair chains determines the history shape. -/
theorem historyShapeRelation_of_pair_projections
    {u v : List J} (hproj : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j v) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact .refl _
    | cons b v =>
      have hh := congrArg List.head? (hproj b b (Std.Refl.refl b))
      simp [historyPairProjection] at hh
  | cons a u ih =>
    have hamem : a ∈ v := by
      have hm : a ∈ historyPairProjection a a (a :: u) := by simp [historyPairProjection]
      rw [hproj a a (Std.Refl.refl a)] at hm
      exact (List.mem_filter.1 hm).1
    obtain ⟨before, after, hv, ha⟩ := history_first_decomposition hamem
    have hind : ∀ b ∈ before, ¬ dependent b a := by
      intro b hb hba
      have hh := congrArg List.head? (hproj a b (symm hba))
      rw [hv, historyPairProjection_prefix_head ha hb] at hh
      have hab : a = b := by simpa [historyPairProjection] using hh
      aesop
    have hmove := historyShapeRelation_move_first (independent := fun b c => ¬ dependent b c) a before after hind
    have hrest : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j (before ++ after) := by
      intro i j hij
      have hm : historyPairProjection i j v = historyPairProjection i j (a :: (before ++ after)) := by
        rw [hv]
        exact historyPairProjection_shape_invariant hij hmove
      have hh := (hproj i j hij).trans hm
      by_cases hai : a = i ∨ a = j <;> simpa [historyPairProjection, hai] using hh
    rw [hv]
    exact .trans _ _ _ (historyShapeRelation_cons a (ih hrest)) (.symm _ _ hmove)

def historyShapePairCode :
    DependenceHeap dependent → ({p : J × J // dependent p.1 p.2} → List J) :=
  Quotient.lift (fun word p => historyPairProjection p.val.1 p.val.2 word)
    (fun _ _ h => funext (fun p => historyPairProjection_shape_invariant p.prop h))

end NearlyMinimax
