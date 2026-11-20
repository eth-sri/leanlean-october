module

public import NearlyMinimax.HistoryDensityEmbedding
public import NearlyMinimax.HistoryMarkedAppend


@[expose] public section

/-!
# Actual prefix heap and deletion of the appended maximal piece
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*}

section
variable (word : List J) (j : J)

/-- Actual old positions embedded in the word with one appended occurrence. -/
def historyPrefixPosition : Fin word.length ↪ Fin (word ++ [j]).length where
  toFun x := ⟨x.val, by have := x.isLt; simp only [List.length_append, List.length_singleton]; omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    exact congrArg (fun z => z.val) h

/-- All existing labels retain their actual evaluation. -/
theorem historyPrefixPosition_get (x : Fin word.length) :
    (word ++ [j]).get (historyPrefixPosition word j x) = word.get x := by
  change (word ++ [j]).get ⟨x.val, _⟩ = _
  simp

end

section
variable {word : List J} {dependent : J → J → Prop} {j : J} {x p q : Fin (word ++ [j]).length}

/-- An appended word position lying inside the old word has the same label. -/
theorem historyPrefixPosition_get_of_lt (hx : x.val < word.length) :
    (word ++ [j]).get x = word.get ⟨x.val, hx⟩ := by
  simp_all

/-- A path whose endpoint is in the prefix cannot have passed through the appended occurrence. -/
theorem historyPrefixPosition_reachable_reflect (hp : p.val < word.length) (hq : q.val < word.length)
    (h : Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get) p q) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) ⟨p.val, hp⟩ ⟨q.val, hq⟩ := by
  induction h with
  | refl => exact .refl
  | @tail r q hreach hstep ih =>
    have hlt : r.val < q.val := hstep.1
    have hr  := hlt.trans hq
    apply (ih hr).tail
    refine ⟨hstep.1, ?_⟩
    simpa only [historyPrefixPosition_get_of_lt hr, historyPrefixPosition_get_of_lt hq] using hstep.2

/-- Exact reflection of the full actual heap relation in prefix positions. -/
theorem historyPrefixPosition_reachable_iff (dependent : J → J → Prop) (j : J)
    (x y : Fin word.length) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) x y ↔
      Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get)
        (historyPrefixPosition word j x) (historyPrefixPosition word j y) := by
  constructor
  · exact Relation.ReflTransGen.lift _ (fun a b h => by refine ⟨h.1, ?_⟩; simpa only [historyPrefixPosition_get] using h.2) x y
  · apply historyPrefixPosition_reachable_reflect

end

variable (word : List J) (dependent : J → J → Prop) (j : J)

/-- The actual prefix dependency heap is an order embedding in the appended heap. -/
def historyPrefixHeapEmbedding :
    WordHeapPiece word dependent ↪o WordHeapPiece (word ++ [j]) dependent where
  toFun x := ⟨historyPrefixPosition word j x.position⟩
  inj' := by intro x y h; apply WordHeapPiece.ext; exact (historyPrefixPosition word j).injective (congrArg WordHeapPiece.position h)
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (historyPrefixPosition_reachable_iff dependent j x.position y.position).symm

/-- Deleting the appended maximal occurrence leaves exactly the image of the actual prefix heap. -/
theorem historyPrefixHeapEmbedding_univ :
    Finset.univ.map (historyPrefixHeapEmbedding word dependent j).toEmbedding =
      Finset.univ.erase (wordHeapAppendedPiece word dependent j) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    apply Finset.mem_erase.2
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    have hv := congrArg (fun z => z.position.val) he
    change x.position.val = word.length at hv
    omega
  · intro hy
    have hne := (Finset.mem_erase.1 hy).1
    have hbound : y.position.val < word.length := by
      have hlt := y.position.isLt
      simp at hlt
      have hval : y.position.val ≠ word.length := by
        bound
      omega
    refine Finset.mem_map.2 ⟨(⟨⟨y.position.val, hbound⟩⟩), Finset.mem_univ _, ?_⟩
    rfl

/-- Exact density deletion formula for the actual appended occurrence. -/
theorem historyPrefixHeap_density_delete (weight : WordHeapPiece (word ++ [j]) dependent → ℝ) (ρ t : ℝ) :
    historyScaledUpperDensity weight ρ (Finset.univ.erase (wordHeapAppendedPiece word dependent j)) t =
      historyScaledUpperDensity (weight ∘ historyPrefixHeapEmbedding word dependent j) ρ Finset.univ t := by
  rw [← historyPrefixHeapEmbedding_univ]
  exact historyUpperDensity_orderEmbedding_map ..

end NearlyMinimax
