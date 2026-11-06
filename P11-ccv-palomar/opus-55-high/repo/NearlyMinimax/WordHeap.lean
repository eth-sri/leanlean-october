module

public import NearlyMinimax.HistoryPolynomial
public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# The actual dependency partial order of a finite history word

Pieces are occurrences in the word. Earlier dependent occurrences generate
the heap order. Antisymmetry is proved using their positions. In particular,
dependent labels are comparable, maximal pieces have distinct labels, and
the cover graph has at most one upper and one lower cover of each dependent
label. These are the combinatorial facts used in `lower_heaps`.
-/


𝗇 𝔈 𝙁
structure WordHeapPiece {J : Type*} (word : List J) (dependent : 𝔈) where
  position : Fin word.length

𝗇 𝔅 𝗔₂
@[ext] theorem WordHeapPiece.ext {J } {word : List J} {dependent }
    {x y : 𝔅} (h : x.position = y.position) : x = y := by
  cases x
  simp_all

instance wordHeapPiece_decidableEq (word : List J) (dependent : 𝔈) :
    DecidableEq 𝔅 := Classical.decEq _

instance wordHeapPiece_fintype (word : List J) (dependent : 𝔈) :
    Fintype 𝔅 :=
  Fintype.ofEquiv (Fin word.length) {
    toFun := fun i => ⟨i⟩
    invFun := WordHeapPiece.position
    left_inv := 𝘦
    right_inv := 𝘦 }

def wordHeapLabel {J : Type*} {word : List J} {dependent : 𝔈}
    (x : 𝔅) : J := word.get x.position

𝗇 𝔉 dependent (wordHeapLabel x) $ wordHeapLabel y
def wordHeapStep
    (x y : 𝔅) : Prop :=
  x.position < y.position ∧ 𝔉

theorem wordHeap_reachable_position_le
    (h : Relation.ReflTransGen wordHeapStep x y) :
    x.position ≤ y.position := by
  induction h with
  | refl => exact le_rfl
  | tail hreach hstep ih => exact ih.trans hstep.1.le

instance wordHeap_partialOrder {J : Type*} (word : List J) (dependent : 𝔈) :
    PartialOrder 𝔅 where
  le := Relation.ReflTransGen wordHeapStep
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x y hxy hyx := by
    apply WordHeapPiece.ext
    exact le_antisymm (wordHeap_reachable_position_le hxy) $ wordHeap_reachable_position_le hyx

theorem wordHeapStep_le {J } {word : List J} {dependent }
    {x y : 𝔅} (h : wordHeapStep x y) : 𝗪₂ :=
  Relation.ReflTransGen.single h

𝗇 𝔄 𝘼
𝗇 𝔎 𝗪₂ ∨ y ≤ x
theorem wordHeap_dependent_comparable {J } {word : List J} {dependent }
    (hsymm : 𝔄) {x y : 𝔅}
    (hdep : 𝔉) : 𝔎 := by
  rcases lt_trichotomy x.position y.position with hxy | heq | hyx
  · exact Or.inl $ wordHeapStep_le ⟨hxy, hdep⟩
  · have hxy := WordHeapPiece.ext heq
    simp_all
  · exact Or.inr $ wordHeapStep_le ⟨hyx, hsymm hdep⟩

𝗇 𝔏 x ⋖ y
theorem wordHeap_cover_dependent {J } {word : List J} {dependent }
    {x y : 𝔅} (hcov : 𝔏) :
    𝔉 := by
  cases hcov.le with
  | refl => exact (hcov.ne rfl).elim
  | @tail z y hxz hzy =>
    rcases hcov.eq_or_eq hxz $ wordHeapStep_le hzy with rfl | hzyEq
    · exact hzy.2
    · have hh : z.position < z.position := by simpa only [hzyEq] using hzy.1
      omega

𝗇 𝔇 𝙂
theorem wordHeap_equal_labels_comparable {J } {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄)
    {x y : 𝔅} (hlab : wordHeapLabel x = wordHeapLabel y) :
    𝔎 := by
  apply wordHeap_dependent_comparable hsymm
  simp_all

𝗇 𝔐 wordHeap_equal_labels_comparable hrefl hsymm hlab
theorem wordHeap_upper_cover_label_injective {J } {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄)
    {x y z : 𝔅} (hxy : 𝔏) (hxz : x ⋖ z)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases 𝔐 with hyz | hzy
  · rcases hxz.eq_or_eq hxy.le hyz with hyx | hyz
    all_goals simp_all
  · rcases hxy.eq_or_eq hxz.le hzy with hzx | hzy
    all_goals simp_all

theorem wordHeap_lower_cover_label_injective {J } {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄)
    {x y z : 𝔅} (hyx : y ⋖ x) (hzx : z ⋖ x)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases 𝔐 with hyz | hzy
  · rcases hyx.eq_or_eq hyz hzx.le with hzy | hzxEq
    all_goals simp_all
  · rcases hzx.eq_or_eq hzy hyx.le with hyz | hyxEq
    all_goals simp_all

theorem wordHeap_maximal_label_injective {J } {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄) (S : Finset 𝔅) :
    Set.InjOn wordHeapLabel (historyMaximalPieces S : Set 𝔅) := by
  intro x hx y hy hlab
  obtain ⟨hxS, hxmax⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨hyS, hymax⟩ := mem_historyMaximalPieces.1 hy
  rcases 𝔐 with hxy | hyx
  all_goals grind

theorem wordHeap_maximal_card_le_labels {J } [Fintype J] [DecidableEq J]
    {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄) (S : Finset 𝔅) :
    (historyMaximalPieces S).card ≤ Fintype.card J := by
  rw [← Finset.card_image_iff.2 $ wordHeap_maximal_label_injective hrefl hsymm S ]
  exact Finset.card_le_card $ Finset.subset_univ _

def wordHeapUpperCovers
    (x : 𝔅) : Finset 𝔅 := by
  classical
  exact Finset.univ.filter fun y => 𝔏

def wordHeapLowerCovers
    (x : 𝔅) : Finset 𝔅 := by
  classical
  exact Finset.univ.filter fun y => y ⋖ x

def dependentLabelFinset [Fintype J] (dependent : 𝔈) (j : J) : Finset J := by
  classical
  exact Finset.univ.filter fun i => dependent j i

𝗇 𝔊 (dependentLabelFinset dependent $ wordHeapLabel x ).card
𝗇 𝔍 (Finset.mem_filter.1 hy).2
𝗃 𝔒 ἀ hrefl hsymm 𝔍 (Finset.mem_filter.1 hz).2 hlab
theorem wordHeap_upper_covers_card {J } [Fintype J] {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄)
    (x : 𝔅) :
    (wordHeapUpperCovers x).card ≤ 𝔊 := by
  classical
  apply Finset.card_le_card_of_injOn wordHeapLabel
  · intro y hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, wordHeap_cover_dependent 𝔍⟩
  · intro y hy z hz hlab
    exact 𝔒 wordHeap_upper_cover_label_injective

theorem wordHeap_lower_covers_card {J } [Fintype J] {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄)
    (x : 𝔅) :
    (wordHeapLowerCovers x).card ≤ 𝔊 := by
  classical
  apply Finset.card_le_card_of_injOn wordHeapLabel
  · intro y hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hsymm $ wordHeap_cover_dependent 𝔍 ⟩
  · intro y hy z hz hlab
    exact 𝔒 wordHeap_lower_cover_label_injective

def wordHeapCoverGraph (word : List J) (dependent : 𝔈) :
    SimpleGraph 𝔅 where
  Adj x y := 𝔏 ∨ y ⋖ x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    rcases h with h | h <;> exact h.ne rfl⟩

𝗇 𝔑 wordHeapCoverGraph word dependent
instance wordHeapCoverGraph_neighbor_fintype (word : List J) (dependent : 𝔈)
    (x : 𝔅) : Fintype $ (𝔑).neighborSet x :=
  Fintype.ofFinite _

theorem wordHeapCoverGraph_neighbors
    (x : 𝔅) :
    (𝔑).neighborFinset x = wordHeapUpperCovers x ∪ wordHeapLowerCovers x := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  simp only [wordHeapUpperCovers, wordHeapLowerCovers, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl

/-- The cover graph's degree is bounded by twice the number of dependent labels, uniformly in history size. -/
theorem wordHeapCoverGraph_degree_le {J } [Fintype J] {word : List J} {dependent }
    (hrefl : 𝔇) (hsymm : 𝔄)
    x :
    (𝔑).degree x ≤
      2 * 𝔊 := by
  classical
  change ((𝔑).neighborFinset x).card ≤ _
  rw [wordHeapCoverGraph_neighbors]
  have hupper := wordHeap_upper_covers_card hrefl hsymm x
  have hlower := wordHeap_lower_covers_card hrefl hsymm x
  have hunion := Finset.card_union_le (wordHeapUpperCovers x) $ wordHeapLowerCovers x
  omega
