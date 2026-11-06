module

public import NearlyMinimax.HistoryDensityEmbedding
public import NearlyMinimax.HistoryMarkedAppend
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Actual prefix heap and deletion of the appended maximal piece
-/


𝛜

𝗇 𝔄 word ++ [j]
/-- Actual old positions embedded in the word with one appended occurrence. -/
def historyPrefixPosition (word : List J) (j : J) : Fin word.length ↪ Fin (𝔄).length where
  toFun x := ⟨x.val, by have := x.isLt; simp only [List.length_append, List.length_singleton]; omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    exact congrArg (fun z : Fin (𝔄).length => z.val) h

𝗇 𝔅 historyPrefixPosition word j
𝗇 𝔊 (𝔄).get
section

variable (word)
    (j : J)
    (x)

include word j

@[simp] theorem historyPrefixPosition_val :
    (𝔅 x).val = x.val := rfl

/-- All existing labels retain their actual evaluation. -/
theorem historyPrefixPosition_get :
    𝔊 (𝔅 x) = word.get x := by
  simp

/-- An appended word position lying inside the old word has the same label. -/
theorem historyPrefixPosition_get_of_lt hx :
    𝔊 x = word.get ⟨x.val, hx⟩ := by
  simp_all

end

𝗇 𝔇 historyPositionStep dependent 𝔊
𝗃 𝔈 ἀ word dependent j
section

variable (word)
    (dependent)
    (j : J)

include j

𝗇 𝔉 historyPositionStep dependent word.get
/-- Existing generating edges embed into the genuinely appended dependency word. -/
theorem historyPrefixPosition_step {x y } (hxy : 𝔉 x y) :
    𝔇
      (𝔅 x) $ 𝔅 y := by
  refine ⟨hxy.1, ?_⟩
  simpa only [historyPrefixPosition_get] using hxy.2

/-- A path whose endpoint is in the prefix cannot have passed through the appended occurrence. -/
theorem historyPrefixPosition_reachable_reflect {p q } hp hq
    (h : Relation.ReflTransGen 𝔇 p q) :
    Relation.ReflTransGen 𝔉 ⟨p.val, hp⟩ ⟨q.val, hq⟩ := by
  induction h with
  | refl => exact .refl
  | @tail r q hreach hstep ih =>
    have hlt : r.val < q.val := hstep.1
    have hr := hlt.trans hq
    have hi := ih hr
    apply hi.tail
    refine ⟨hstep.1, ?_⟩
    simpa only [historyPrefixPosition_get_of_lt word j r hr, historyPrefixPosition_get_of_lt word j q hq] using hstep.2

/-- Exact reflection of the full actual heap relation in prefix positions. -/
theorem historyPrefixPosition_reachable_iff x y :
    Relation.ReflTransGen 𝔉 x y ↔
      Relation.ReflTransGen 𝔇
        (𝔅 x) (𝔅 y) := by
  constructor
  · exact Relation.ReflTransGen.lift 𝔅
      (fun a b h => 𝔈 historyPrefixPosition_step h) x y
  · intro h
    have hh := 𝔈 historyPrefixPosition_reachable_reflect x.isLt y.isLt h
    assumption

end

/-- The actual prefix dependency heap is an order embedding in the appended heap. -/
def historyPrefixHeapEmbedding (word : List J) (dependent : 𝙁) (j : J) :
    𝗔₂ ↪o WordHeapPiece 𝔄 dependent where
  toFun x := ⟨𝔅 x.position⟩
  inj' := by intro x y h; apply WordHeapPiece.ext; exact (𝔅).injective $ congrArg WordHeapPiece.position h
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (𝔈 historyPrefixPosition_reachable_iff x.position y.position).symm

section

variable (word)
    (dependent)
    (j : J)

@[simp] theorem historyPrefixHeapEmbedding_label x :
    wordHeapLabel (𝔈 historyPrefixHeapEmbedding x) = wordHeapLabel x :=
  historyPrefixPosition_get word j x.position

/-- Deleting the appended maximal occurrence leaves exactly the image of the actual prefix heap. -/
theorem historyPrefixHeapEmbedding_univ :
    Finset.univ.map (𝔈 historyPrefixHeapEmbedding).toEmbedding =
      Finset.univ.erase 𝔈 wordHeapAppendedPiece := by
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
    let x : 𝗔₂ := ⟨⟨y.position.val, hbound⟩⟩
    refine Finset.mem_map.2 ⟨x, Finset.mem_univ _, ?_⟩
    rfl

/-- Exact density deletion formula for the actual appended occurrence. -/
theorem historyPrefixHeap_density_delete weight ρ t :
    historyScaledUpperDensity weight ρ (Finset.univ.erase 𝔈 wordHeapAppendedPiece) t =
      historyScaledUpperDensity (weight ∘ 𝔈 historyPrefixHeapEmbedding) ρ Finset.univ t := by
  rw [← historyPrefixHeapEmbedding_univ]
  exact historyScaledUpperDensity_orderEmbedding_map _ _ ρ _ t
