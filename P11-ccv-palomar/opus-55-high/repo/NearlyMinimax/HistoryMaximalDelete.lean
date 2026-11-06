module

public import NearlyMinimax.HistoryWordTransport
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# Actual maximal-piece deletion inverts quotient append
-/


𝛜

𝗇 𝔊 𝚞₁
/-- Shape equivalence can be prefixed by any word. -/
theorem historyShapeRelation_prefix (preword : List J)
    (h : 𝔊 u v) :
    𝔊 (preword ++ u) $ preword ++ v := by
  induction preword with
  | nil => exact h
  | cons a preword ih => exact historyShapeRelation_cons a ih

/-- A piece can be moved to the last position precisely across independent following labels. -/
theorem historyShapeRelation_move_last (a : J) after
    (hafter : ∀ b ∈ after, independent a b) :
    𝔊 (a :: after) $ after ++ [a] := by
  induction after with
  | nil => exact .refl _
  | cons b after ih =>
    have hi := ih fun c hc => hafter c $ List.mem_cons_of_mem _ hc
    exact .trans _ _ _ (.rel _ _ $ IndependentHistoryExchange.swap [] after a b $ hafter b List.mem_cons_self )
      $ historyShapeRelation_cons b hi

𝗇 𝔏 x.position.val + 1
𝗇 𝔅 word.drop 𝔏
𝗇 𝔇 𝙁
𝗇 𝔍 𝗔₂
/-- The concrete word obtained by deleting one specified actual occurrence. -/
def historyWordDeletePiece (word : List J) (dependent : 𝔇)
    (x : 𝔍) : List J :=
  word.take x.position.val ++ 𝔅

𝗇 𝔉 x ∈ historyMaximalPieces Finset.univ
/-- Every label after a maximal occurrence is independent of it. -/
theorem wordHeap_maximal_suffix_independent (word : List J) dependent
    (x : 𝔍) (hx : 𝔉) :
    ∀ b ∈ 𝔅, ¬ dependent (wordHeapLabel x) b := by
  intro b hb hdep
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 hb
  have hybound : 𝔏 + k < word.length := by
    grind
  let y : 𝔍 := ⟨⟨𝔏 + k, hybound⟩⟩
  have hylabel : wordHeapLabel y = b := by
    aesop
  have hxy : 𝗪₂ := wordHeapStep_le ⟨𝖤₃,
    𝖤₄⟩
  have he := (mem_historyMaximalPieces.1 hx).2 y (Finset.mem_univ y) hxy
  grind

𝗇 𝔄 𝖴
𝗃 𝔐 ἀ word dependent x
/-- The actual word heap deletion has exactly the shape required by append. -/
theorem wordHeap_maximal_delete_shape (word : List J) dependent
    x (hx : 𝔉) :
    Relation.EqvGen (IndependentHistoryExchange 𝔄)
      word $ 𝔐 historyWordDeletePiece ++ [wordHeapLabel x] := by
  have hmove := historyShapeRelation_move_last (independent := 𝔄) (wordHeapLabel x)
    𝔅 $ 𝔐 wordHeap_maximal_suffix_independent hx
  have hword : word = word.take x.position.val ++ wordHeapLabel x :: 𝔅 := by
    change word = word.take x.position.val ++ word.get x.position :: 𝔅
    simp
  conv_lhs => rw [hword]
  simpa only [historyWordDeletePiece, List.append_assoc] using historyShapeRelation_prefix (word.take x.position.val) hmove

variable [Fintype J] [LinearOrder J]

omit [Fintype J] [LinearOrder J] in
/-- Deleting a true maximal piece is a genuine preimage of its labelled append map. -/
theorem wordHeap_maximal_delete_append (word : List J) (dependent : 𝔇)
    (x : 𝔍) (hx : 𝔉) :
    historyShapeAppend dependent (wordHeapLabel x) (Quotient.mk _ 𝔐 historyWordDeletePiece) =
      (Quotient.mk _ word : HistoryShape 𝔄) := by
  rw [historyShapeAppend_mk]
  exact (Quotient.sound $ 𝔐 wordHeap_maximal_delete_shape hx ).symm

/-- The concrete last occurrence in a word with an appended label. -/
def wordHeapAppendedPiece (word : List J) (dependent : 𝔇) (j : J) :
    WordHeapPiece (word ++ [j]) dependent := ⟨⟨word.length, 𝖢₄⟩⟩

omit [Fintype J] [LinearOrder J] in
@[simp] theorem wordHeapAppendedPiece_label (word : List J) (dependent : 𝔇) (j : J) :
    wordHeapLabel (wordHeapAppendedPiece word dependent j) = j := by
  unfold wordHeapLabel wordHeapAppendedPiece
  rw [List.get_eq_getElem, List.getElem_append_right 𝖦₄ ]
  simp

omit [Fintype J] [LinearOrder J] in
theorem wordHeapAppendedPiece_maximal (word : List J) (dependent : 𝔇) (j : J) :
    wordHeapAppendedPiece word dependent j ∈ historyMaximalPieces Finset.univ := by
  apply mem_historyMaximalPieces.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro y hy hxy
  have hlo := wordHeap_reachable_position_le hxy
  have hhi := y.position.isLt
  simp only [List.length_append, List.length_singleton] at hhi
  apply WordHeapPiece.ext
  apply Fin.ext
  change word.length ≤ y.position.val at hlo
  change y.position.val = word.length
  omega

𝗇 𝔈 u.out ++ [j]
𝗇 𝔎 𝗡₁
omit [Fintype J] [LinearOrder J] in
/-- The terminal-shape range is exactly the genuine maximal-piece label condition. -/
theorem historyShape_terminal_iff_maximal (dependent : 𝔇)
    (hsymm : 𝘼)
    (j : J) (g : HistoryShape 𝔄) :
    g ∈ Set.range 𝔎 ↔
      ∃ x : WordHeapPiece g.out dependent,
        𝔉 ∧ wordHeapLabel x = j := by
  constructor
  · rintro ⟨u, hu⟩
    have hmk : (Quotient.mk _ 𝔈 : HistoryShape 𝔄) = g := by
      calc
        _ = 𝔎 (Quotient.mk _ u.out) := rfl
        _ = 𝔎 u := congrArg _ $ Quotient.out_eq u
        _ = g := hu
    have hr : Relation.EqvGen (IndependentHistoryExchange 𝔄)
        𝔈 g.out := Quotient.exact $ hmk.trans (Quotient.out_eq g).symm
    obtain ⟨e, he⟩ := historyShapeRelation_heapIso dependent hsymm hr
    let x := wordHeapAppendedPiece u.out dependent j
    have hx := wordHeapAppendedPiece_maximal u.out dependent j
    have hxmap : e x ∈ historyMaximalPieces ((Finset.univ : Finset $ WordHeapPiece 𝔈 dependent ).map e.toEquiv.toEmbedding) := by
      rw [historyMaximalPieces_orderIso_map]
      exact Finset.mem_map.2 ⟨x, hx, rfl⟩
    rw [Finset.map_univ_equiv e.toEquiv] at hxmap
    exact ⟨e x, hxmap, (he x).trans $ wordHeapAppendedPiece_label u.out dependent j ⟩
  · rintro ⟨x, hx, hlabel⟩
    have hd := wordHeap_maximal_delete_append g.out dependent x hx
    rw [hlabel] at hd
    exact ⟨Quotient.mk _ $ historyWordDeletePiece g.out dependent x , hd.trans $ Quotient.out_eq g ⟩
