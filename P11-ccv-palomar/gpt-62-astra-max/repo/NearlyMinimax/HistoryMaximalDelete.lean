module

public import NearlyMinimax.HistoryWordTransport


@[expose] public section

/-!
# Actual maximal-piece deletion inverts quotient append
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*}

section
variable {independent : J → J → Prop}

/-- Shape equivalence can be prefixed by any word. -/
theorem historyShapeRelation_prefix (preword : List J)
    {u v : List J} (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (preword ++ u) (preword ++ v) := by
  induction preword with
  | nil => exact h
  | cons a preword ih => exact historyShapeRelation_cons a ih

/-- A piece can be moved to the last position precisely across independent following labels. -/
theorem historyShapeRelation_move_last {a : J} {after : List J}
    (hafter : ∀ b ∈ after, independent a b) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: after) (after ++ [a]) := by
  induction after with
  | nil => exact .refl _
  | cons b after ih =>
    exact .trans _ _ _ (.rel _ _ (IndependentHistoryExchange.swap [] after a b (hafter b List.mem_cons_self)))
      (historyShapeRelation_cons b (ih (fun c hc => hafter c (List.mem_cons_of_mem _ hc))))

end

section
variable {word : List J} {dependent : J → J → Prop} {x : WordHeapPiece word dependent}

/-- The concrete word obtained by deleting one specified actual occurrence. -/
def historyWordDeletePiece
    (x : WordHeapPiece word dependent) : List J :=
  word.take x.position.val ++ word.drop (x.position.val + 1)

/-- Every label after a maximal occurrence is independent of it. -/
theorem wordHeap_maximal_suffix_independent (hx : x ∈ historyMaximalPieces Finset.univ) :
    ∀ b ∈ word.drop (x.position.val + 1), ¬ dependent (wordHeapLabel x) b := by
  intro b hb hdep
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 hb
  have hybound : x.position.val + 1 + k < word.length := by
    simp at hk
    omega
  let y : WordHeapPiece word dependent := ⟨⟨x.position.val + 1 + k, hybound⟩⟩
  have hylabel : wordHeapLabel y = b := by
    change word.get _ = b
    simpa using hkb
  have hxy : x ≤ y := wordHeapStep_le ⟨by grind,
    by simp_all⟩
  have he := (mem_historyMaximalPieces.1 hx).2 y (Finset.mem_univ y) hxy
  grind

/-- The actual word heap deletion has exactly the shape required by append. -/
theorem wordHeap_maximal_delete_shape (hx : x ∈ historyMaximalPieces Finset.univ) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b))
      word (historyWordDeletePiece x ++ [wordHeapLabel x]) := by
  have hmove := historyShapeRelation_move_last (independent := fun a b => ¬ dependent a b) (wordHeap_maximal_suffix_independent hx)
  have hword : word = word.take x.position.val ++ wordHeapLabel x :: word.drop (x.position.val + 1) := by
    change word = word.take x.position.val ++ word.get x.position :: word.drop (x.position.val + 1)
    simp
  conv_lhs => rw [hword]
  simpa only [historyWordDeletePiece, List.append_assoc] using historyShapeRelation_prefix (word.take x.position.val) hmove

end

variable [Fintype J] [LinearOrder J]

/-- The concrete last occurrence in a word with an appended label. -/
def wordHeapAppendedPiece (word : List J) (dependent : J → J → Prop) (j : J) :
    WordHeapPiece (word ++ [j]) dependent := ⟨⟨word.length, by simp⟩⟩

omit [Fintype J] [LinearOrder J] in
@[simp] theorem wordHeapAppendedPiece_label (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapLabel (wordHeapAppendedPiece word dependent j) = j := by
  unfold wordHeapLabel wordHeapAppendedPiece
  simp

omit [Fintype J] [LinearOrder J] in
theorem wordHeapAppendedPiece_maximal (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapAppendedPiece word dependent j ∈ historyMaximalPieces Finset.univ := by
  apply mem_historyMaximalPieces.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro y hy hxy
  have hlo := wordHeap_reachable_position_le hxy
  have hhi := y.position.isLt
  simp at hhi
  apply WordHeapPiece.ext
  apply Fin.ext
  change word.length ≤ y.position.val at hlo
  change y.position.val = word.length
  omega

omit [Fintype J] [LinearOrder J] in
/-- The terminal-shape range is exactly the genuine maximal-piece label condition. -/
theorem historyShape_terminal_iff_maximal (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent) :
    g ∈ Set.range (historyShapeAppend j) ↔
      ∃ x : WordHeapPiece g.out dependent,
        x ∈ historyMaximalPieces Finset.univ ∧ wordHeapLabel x = j := by
  constructor
  · rintro ⟨u, hu⟩
    have hmk : (Quotient.mk _ (u.out ++ [j])) = g := by
      calc
        _ = _ := rfl
        _ = _ := congrArg _ (Quotient.out_eq u)
        _ = g := hu
    obtain ⟨e, he⟩ := historyShapeRelation_heapIso (Quotient.exact (hmk.trans (Quotient.out_eq g).symm))
    let x := wordHeapAppendedPiece u.out dependent j
    have hxmap : e x ∈ historyMaximalPieces (Finset.univ.map e.toEquiv.toEmbedding) := by
      rw [historyMaximalPieces_orderIso_map]
      exact Finset.mem_map.2 ⟨x, (wordHeapAppendedPiece_maximal u.out dependent j), rfl⟩
    rw [Finset.map_univ_equiv e.toEquiv] at hxmap
    exact ⟨e x, hxmap, (he x).trans (wordHeapAppendedPiece_label ..)⟩
  · rintro ⟨x, hx, hlabel⟩
    have hd := ((Quotient.sound (wordHeap_maximal_delete_shape hx)).symm : historyShapeAppend (wordHeapLabel x) ⟦historyWordDeletePiece x⟧ = ⟦Quotient.out g⟧)
    rw [hlabel] at hd
    exact ⟨Quotient.mk _ (historyWordDeletePiece x), hd.trans (Quotient.out_eq g)⟩

end NearlyMinimax
