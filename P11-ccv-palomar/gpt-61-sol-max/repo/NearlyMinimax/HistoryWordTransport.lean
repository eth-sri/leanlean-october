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
theorem historyWord_swap_tuple before after (a b : J) :
    let word := before ++ a :: b :: after
    let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    let j : Fin word.length := ⟨before.length + 1, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    List.ofFn (word.get ∘ Equiv.swap i j) = before ++ b :: a :: after := by
  dsimp only
  let word := before ++ a :: b :: after
  let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
  let j : Fin word.length := ⟨before.length + 1, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
  have hi : word.get i = a := by
    rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [i]; omega)]
    simp [i]
  have hj : word.get j = b := by
    rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [j]; omega)]
    simp [j]
  have hc := historyTuple_adjacent_decomposition (word.get ∘ Equiv.swap i j) i j (rfl)
  rw [historyTuple_swap_take word.get i j (rfl),
    historyTuple_swap_drop word.get i j (rfl)] at hc
  simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right, hi, hj,
    List.ofFn_get] at hc
  have ht : word.take i.val = before := List.take_left
  have hd : word.drop (j.val + 1) = after := by
    change (before ++ a :: b :: after).drop (before.length + 1 + 1) = after
    rw [List.drop_append]
    have hb : before.drop (before.length + 1 + 1) = [] := by
      rw [List.drop_eq_nil_iff]
      omega
    rw [hb, List.nil_append, show before.length + 1 + 1 - before.length = 2 by omega]
    rfl
  rw [ht, hd] at hc
  exact hc

section
variable (dependent : J → J → Prop) (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
include hsymm

/-- The tuple exchange carries each piece's label with its occurrence. -/
theorem historyTupleSwapHeapIso_label 
    {n } labels (i j : Fin n) hij
    hind
    x :
    wordHeapLabel (historyTupleSwapHeapIso labels dependent hsymm i j hij hind x) = wordHeapLabel x := by
  simp [wordHeapLabel, historyTupleSwapHeapIso, wordHeapOrderIsoPosition,
    historyTupleSwapPositions, historyTuplePositionEquiv, finCongr,
    Function.comp_def]
  congr 1

section
variable {u v : List J}

/-- Every independent word exchange has a genuine label-preserving heap isomorphism. -/
theorem historyWord_exchange_heapIso 
     (h : IndependentHistoryExchange (fun a b => ¬ dependent a b) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  cases h with
  | swap before after a b hind =>
    let word := before ++ a :: b :: after
    let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    let j : Fin word.length := ⟨before.length + 1, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    have hi : word.get i = a := by
      rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [i]; omega)]
      simp [i]
    have hj : word.get j = b := by
      rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [j]; omega)]
      simp [j]
    have hind' : ¬ dependent (word.get i) (word.get j) := by simpa only [hi, hj] using hind
    have he : ∃ e : WordHeapPiece (List.ofFn word.get) dependent ≃o
        WordHeapPiece (List.ofFn (word.get ∘ Equiv.swap i j)) dependent,
        ∀ x, wordHeapLabel (e x) = wordHeapLabel x :=
      ⟨historyTupleSwapHeapIso word.get dependent hsymm i j (rfl) hind',
        historyTupleSwapHeapIso_label dependent hsymm word.get i j (rfl) hind'⟩
    have hw  :=
      historyWord_swap_tuple before after a b
    have hold  := List.ofFn_get word
    rw [hold, hw] at he
    exact he

/-- Actual equivalent words carry the same labelled dependency heap. -/
theorem historyShapeRelation_heapIso 
     (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  induction h with
  | rel u v h => exact historyWord_exchange_heapIso dependent hsymm h
  | refl u => exact ⟨OrderIso.refl _, fun _ => rfl⟩
  | symm u v h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.symm, ?_⟩
    intro x
    have hh := he (e.symm x)
    simpa only [e.apply_symm_apply] using hh.symm
  | trans u v w h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁
    obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun x => (he₂ (e₁ x)).trans (he₁ x)⟩
end

end


end NearlyMinimax
