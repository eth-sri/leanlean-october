module

public import NearlyMinimax.HistoryMarkedExchange


@[expose] public section

/-!
# Concrete coordinate transport for independent word exchanges
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*}

/-- The actual word obtained by swapping the two distinguished adjacent positions. -/
theorem historyWord_swap_tuple (before after : List J) (a b : J) :
    let word := before ++ a :: b :: after
    let i : Fin word.length := ⟨before.length, by grind⟩
    let j : Fin word.length := ⟨before.length + 1, by grind⟩
    List.ofFn (word.get ∘ Equiv.swap i j) = before ++ b :: a :: after := by
  let word := before ++ a :: b :: after
  let i : Fin word.length := ⟨before.length, by grind⟩
  let j : Fin word.length := ⟨before.length + 1, by grind⟩
  have hi : word.get i = a := by
    grind
  have hj : word.get j = b := by
    grind
  have hc := historyTuple_adjacent_decomposition (word.get ∘ Equiv.swap i j) i j rfl
  rw [historyTuple_swap_take word.get i j rfl,
    historyTuple_swap_drop word.get i j rfl] at hc
  simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right, hi, hj,
    List.ofFn_get] at hc
  have ht : word.take i.val = before := List.take_left
  have hd : word.drop (j.val + 1) = after := by
    rw [List.drop_append]
    have hb : before.drop (before.length + 1 + 1) = [] := by
      rw [List.drop_eq_nil_iff]
      omega
    rw [hb, List.nil_append, show before.length + 1 + 1 - before.length = 2 by omega]
    rfl
  rw [ht, hd] at hc
  exact hc

variable {dependent : J → J → Prop} [Std.Symm dependent] {u v : List J}

/-- Every independent word exchange has a genuine label-preserving heap isomorphism. -/
theorem historyWord_exchange_heapIso (h : IndependentHistoryExchange (fun a b => ¬ dependent a b) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  cases h with
  | swap before after a b hind =>
    let word := before ++ a :: b :: after
    let i : Fin word.length := ⟨before.length, by grind⟩
    let j : Fin word.length := ⟨before.length + 1, by grind⟩
    have hi : word.get i = a := by
      grind
    have hj : word.get j = b := by
      grind
    have hind' : ¬ dependent (word.get i) (word.get j) := by simp_all
    have he : ∃ e : WordHeapPiece (List.ofFn word.get) dependent ≃o
        WordHeapPiece (List.ofFn (word.get ∘ Equiv.swap i j)) dependent,
        ∀ x, wordHeapLabel (e x) = wordHeapLabel x :=
      ⟨historyTupleSwapHeapIso rfl hind',
        (by simp [wordHeapLabel, historyTupleSwapHeapIso, wordHeapOrderIsoPosition, historyTupleSwapPositions, historyTuplePositionEquiv, finCongr])⟩
    have hw  :=
      historyWord_swap_tuple before after a b
    rw [(List.ofFn_get word), hw] at he
    exact he

/-- Actual equivalent words carry the same labelled dependency heap. -/
theorem historyShapeRelation_heapIso (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  induction h with
  | rel u v h => exact historyWord_exchange_heapIso h
  | refl u => exact ⟨OrderIso.refl _, fun _ => rfl⟩
  | symm u v h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.symm, ?_⟩
    intro x
    simpa using (he (e.symm x)).symm
  | trans u v w h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁
    obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun x => (he₂ (e₁ x)).trans (he₁ x)⟩

end NearlyMinimax
