module

public import NearlyMinimax.HistoryAppend
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Actual order transport under an adjacent independent exchange

Finite word positions generate heap order by earlier dependent labels. Swapping
two adjacent independent positions preserves every generating relation and its
transitive closure. This supplies the order component of marked-coordinate
transport without assuming representative invariance of a density.
-/


variable {J : Type*} {n : ℕ}

𝗇 𝔅 Fin n → J
𝗇 𝔍 𝙁
def historyPositionStep (dependent : 𝔍) (labels : 𝔅)
    (x y : Fin n) : Prop := x < y ∧ dependent (labels x) (labels y)

𝗇 𝔉 ¬ dependent (labels i) (labels j)
𝗇 𝔊 Equiv.swap i j
theorem historyAdjacent_swap_lt (labels : 𝔅) dependent
    i j x y (hij : 𝘧₂)
    (hind : 𝔉)
    (hxy : historyPositionStep dependent labels x y) :
    𝔊 x < 𝔊 y := by
  have hlt := hxy.1
  by_cases hxi : x = i
  · subst x
    by_cases hyj : y = j
    · subst y; exact (hind hxy.2).elim
    grind
  grind

𝗇 𝔎 historyPositionStep dependent word.get
/-- The actual word heap relation is its dependency relation on positions. -/
theorem wordHeap_le_iff_position_reachable (word : List J) dependent
    (x y : 𝗔₂) :
    𝗪₂ ↔ Relation.ReflTransGen 𝔎 x.position y.position := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail hreach hstep ih => exact ih.tail hstep
  · have hlift : ∀ {p q },
        Relation.ReflTransGen 𝔎 p q →
          Relation.ReflTransGen wordHeapStep (⟨p⟩ : 𝗔₂) ⟨q⟩ := by
      intro p q hpq
      induction hpq with
      | refl => exact .refl
      | tail hreach hstep ih => exact ih.tail hstep
    bound

theorem historyEquiv_reachable_iff (e : A ≃ B)
    r (s : B → B → Prop)
    (hstep : ∀ x y, r x y ↔ s (e x) (e y)) x y :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · exact Relation.ReflTransGen.lift e (fun a b h => (hstep a b).1 h) x y
  · intro h
    have hlift := Relation.ReflTransGen.lift e.symm
       (p := r) fun a b h => by
        simp_all (e x) (e y) h
    grind

/-- Actual dependency heaps are isomorphic when their generating positions are. -/
def wordHeapOrderIsoPosition (word word' : List J) (dependent : 𝔍)
    (e : Fin word.length ≃ Fin word'.length)
    (hstep : ∀ x y, 𝔎 x y ↔
      historyPositionStep dependent word'.get (e x) (e y)) :
    𝗔₂ ≃o WordHeapPiece word' dependent where
  toFun x := ⟨e x.position⟩
  invFun x := ⟨e.symm x.position⟩
  left_inv x := WordHeapPiece.ext $ e.symm_apply_apply x.position
  right_inv x := WordHeapPiece.ext $ e.apply_symm_apply x.position
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (historyEquiv_reachable_iff e _ _ hstep x.position y.position).symm

𝗃 𝔐 Fin (List.ofFn ἀ).length
/-- Tuple positions and their actual finite word positions are canonically identical. -/
def historyTuplePositionEquiv (labels : 𝔅) : 𝔐 labels ≃ Fin n :=
  finCongr List.length_ofFn

theorem historyTuplePositionEquiv_get (labels : 𝔅) i :
    (List.ofFn labels).get i = labels (historyTuplePositionEquiv labels i) := by
  aesop

𝗇 𝔄 labels ∘ Equiv.swap i j
/-- The actual word-position permutation of an adjacent tuple exchange. -/
def historyTupleSwapPositions (labels : 𝔅) (i j : Fin n) :
    𝔐 labels ≃ 𝔐 𝔄 :=
  (historyTuplePositionEquiv labels).trans
    $ (𝔊).trans (historyTuplePositionEquiv 𝔄).symm

𝗇 𝔇 historyTuplePositionEquiv labels x
𝗇 𝔈 historyTuplePositionEquiv labels y
𝗇 𝔏 historyTupleSwapPositions labels i j
/-- Swapping adjacent independent updates constructs an actual dependency-heap order isomorphism. -/
def historyTupleSwapHeapIso (labels : 𝔅) (dependent : 𝔍)
    (hsymm : 𝘆₁)
    (i j : Fin n) (hij : 𝘧₂) (hind : 𝔉) :
    WordHeapPiece (List.ofFn labels) dependent ≃o
      WordHeapPiece (List.ofFn 𝔄) dependent :=
  wordHeapOrderIsoPosition _ _ dependent 𝔏 (by
    intro x y
    unfold historyPositionStep
    simp only [historyTuplePositionEquiv_get]
    have hx : (historyTuplePositionEquiv 𝔄)
        (𝔏 x) = 𝔊 𝔇 := by
      simp [historyTupleSwapPositions]
    have hy : (historyTuplePositionEquiv 𝔄)
        (𝔏 y) = 𝔊 𝔈 := by
      simp [historyTupleSwapPositions]
    rw [hx, hy]
    simp only [Function.comp_def, Equiv.swap_apply_self]
    constructor
    · intro h
      have hpos : historyPositionStep dependent labels 𝔇
          𝔈 := by
        refine ⟨?_, h.2⟩
        simpa [historyTuplePositionEquiv, finCongr] using h.1
      have he := historyAdjacent_swap_lt labels dependent i j _ _ hij hind hpos
      exact ⟨by simpa [historyTupleSwapPositions, historyTuplePositionEquiv, finCongr] using he, h.2⟩
    · intro h
      have hnew : historyPositionStep dependent 𝔄
          (𝔊 𝔇)
          $ 𝔊 𝔈 := by
        refine ⟨?_, ?_⟩
        · simpa [historyTupleSwapPositions, historyTuplePositionEquiv, finCongr] using h.1
        · simpa only [Function.comp_def, Equiv.swap_apply_self] using h.2
      have hind' : ¬ dependent (𝔄 i) (𝔄 j) := by
        simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact fun hd => hind $ hsymm hd
      have he := historyAdjacent_swap_lt 𝔄 dependent i j _ _ hij hind' hnew
      exact ⟨by simpa [historyTuplePositionEquiv, finCongr] using he, h.2⟩)
