module

public import NearlyMinimax.HistoryMarkedExchange
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Concrete coordinate transport for independent word exchanges
-/

𝚨

𝛜

𝗇 𝔅 before ++ a :: b :: after
𝗇 𝔇 word.get ∘ Equiv.swap i j
𝗇 𝔊 before.length + 1
/-- The actual word obtained by swapping the two distinguished adjacent positions. -/
theorem historyWord_swap_tuple before after (a b : J) :
    let word := 𝔅
    let i := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    let j := ⟨𝔊, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    List.ofFn 𝔇 = before ++ b :: a :: after := by
  let word := 𝔅
  let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
  let j : Fin word.length := ⟨𝔊, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
  have hi : word.get i = a := by
    rw [List.get_eq_getElem, List.getElem_append_right $ by dsimp [i]; omega ]
    simp [i]
  have hj : word.get j = b := by
    rw [List.get_eq_getElem, List.getElem_append_right $ by dsimp [j]; omega ]
    simp [j]
  have hc := historyTuple_adjacent_decomposition 𝔇 i j 𝖦₄
  rw [historyTuple_swap_take word.get i j 𝖦₄ ,
    historyTuple_swap_drop word.get i j 𝖦₄ ] at hc
  simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right, hi, hj,
    List.ofFn_get] at hc
  have ht : word.take i.val = before := List.take_left
  have hd : word.drop 𝘩₂ = after := by
    rw [List.drop_append]
    have hb : before.drop (𝔊 + 1) = [] := by
      rw [List.drop_eq_nil_iff]
      omega
    rw [hb, List.nil_append, show 𝔊 + 1 - before.length = 2 by omega]
    rfl
  rw [ht, hd] at hc
  exact hc

/-- The tuple exchange carries each piece's label with its occurrence. -/
theorem historyTupleSwapHeapIso_label dependent
    hsymm
    (labels : Fin n → J) i j hij
    hind
    x :
    wordHeapLabel (historyTupleSwapHeapIso labels dependent hsymm i j hij hind x) = wordHeapLabel x := by
  simp [wordHeapLabel, historyTupleSwapHeapIso, wordHeapOrderIsoPosition,
    historyTupleSwapPositions, historyTuplePositionEquiv]
  congr 1

𝗇 𝔍 𝚠₁
𝗇 𝔄 ∃ e : 𝚀, 𝔍
𝗇 𝔈 𝘆₁
𝗇 𝔉 IndependentHistoryExchange 𝖴
section

variable (dependent : 𝙁)
    (hsymm : 𝔈)

include dependent hsymm

/-- Every independent word exchange has a genuine label-preserving heap isomorphism. -/
theorem historyWord_exchange_heapIso (h : 𝔉 u v) :
    𝔄 := by
  cases h with
  | swap before after a b hind =>
    let word := 𝔅
    let i : Fin word.length := ⟨before.length, 𝖤₃⟩
    let j : Fin word.length := ⟨𝔊, 𝖤₃⟩
    have hi : word.get i = a := by
      grind
    have hj : word.get j = b := by
      grind
    have hind' : ¬ dependent (word.get i) (word.get j) := 𝖤₄
    have he : ∃ e : WordHeapPiece (List.ofFn word.get) dependent ≃o
        WordHeapPiece (List.ofFn 𝔇) dependent,
        𝔍 :=
      ⟨historyTupleSwapHeapIso word.get dependent hsymm i j  𝖦₄  hind',
        historyTupleSwapHeapIso_label dependent hsymm word.get i j  𝖦₄  hind'⟩
    rw [ List.ofFn_get word , historyWord_swap_tuple before after a b ] at he
    exact he

/-- Actual equivalent words carry the same labelled dependency heap. -/
theorem historyShapeRelation_heapIso (h : Relation.EqvGen 𝔉 u v) :
    𝔄 := by
  induction h with
  | rel u v h => exact historyWord_exchange_heapIso dependent hsymm h
  | refl u => exact ⟨OrderIso.refl _, 𝘦⟩
  | symm u v h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.symm, ?_⟩
    intro x
    have hh := he $ e.symm x
    simpa only [e.apply_symm_apply] using hh.symm
  | trans u v w h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁
    obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun x => (he₂ $ e₁ x ).trans $ he₁ x ⟩
