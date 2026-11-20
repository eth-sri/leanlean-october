module

public import NearlyMinimax.HistoryPolynomial
public import Mathlib


@[expose] public section

/-!
# The actual dependency partial order of a finite history word

Pieces are occurrences in the word. Earlier dependent occurrences generate
the heap order. Antisymmetry is proved using their positions. In particular,
dependent labels are comparable, maximal pieces have distinct labels, and
the cover graph has at most one upper and one lower cover of each dependent
label. These are the combinatorial facts used in `lower_heaps`.
-/

noncomputable section
namespace NearlyMinimax

structure WordHeapPiece {J : Type*} (word : List J) (dependent : J → J → Prop) where
  position : Fin word.length

section
variable {J : Type*} {word : List J} {dependent : J → J → Prop}

@[ext] theorem WordHeapPiece.ext
    {x y : WordHeapPiece word dependent} (h : x.position = y.position) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance wordHeapPiece_decidableEq (word : List J) (dependent : J → J → Prop) :
    DecidableEq (WordHeapPiece word dependent) := Classical.decEq _

instance wordHeapPiece_fintype (word : List J) (dependent : J → J → Prop) :
    Fintype (WordHeapPiece word dependent) :=
  Fintype.ofEquiv (Fin word.length) {
    toFun := fun i => ⟨i⟩
    invFun := WordHeapPiece.position
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

def wordHeapLabel
    (x : WordHeapPiece word dependent) : J := word.get x.position

def wordHeapStep
    (x y : WordHeapPiece word dependent) : Prop :=
  x.position < y.position ∧ dependent (wordHeapLabel x) (wordHeapLabel y)

theorem wordHeap_reachable_position_le
    {x y : WordHeapPiece word dependent} (h : Relation.ReflTransGen wordHeapStep x y) :
    x.position ≤ y.position := by
  induction h with
  | refl => exact le_rfl
  | tail hreach hstep ih => exact ih.trans hstep.1.le

instance wordHeap_partialOrder (word : List J) (dependent : J → J → Prop) :
    PartialOrder (WordHeapPiece word dependent) where
  le := Relation.ReflTransGen wordHeapStep
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm x y hxy hyx := by
    apply WordHeapPiece.ext
    exact le_antisymm (wordHeap_reachable_position_le hxy) (wordHeap_reachable_position_le hyx)

theorem wordHeapStep_le
    {x y : WordHeapPiece word dependent} (h : wordHeapStep x y) : x ≤ y :=
  Relation.ReflTransGen.single h

theorem wordHeap_dependent_comparable
    [Std.Symm dependent] {x y : WordHeapPiece word dependent}
    (hdep : dependent (wordHeapLabel x) (wordHeapLabel y)) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy x.position y.position with hxy | heq | hyx
  · solve_by_elim [wordHeapStep_le]
  · have hxy  := WordHeapPiece.ext heq
    subst y
    exact Or.inl le_rfl
  · exact Or.inr (wordHeapStep_le ⟨hyx, symm hdep⟩)

theorem wordHeap_cover_dependent
    {x y : WordHeapPiece word dependent} (hcov : x ⋖ y) :
    dependent (wordHeapLabel x) (wordHeapLabel y) := by
  cases hcov.le with
  | refl => aesop
  | @tail z y hxz hzy =>
    rcases (hcov.eq_or_eq hxz (wordHeapStep_le hzy)) with rfl | hzyEq
    · exact hzy.2
    · exact (lt_irrefl _ (by simpa only [hzyEq] using hzy.1)).elim

theorem wordHeap_equal_labels_comparable
    [Std.Refl dependent] [Std.Symm dependent]
    {x y : WordHeapPiece word dependent} (hlab : wordHeapLabel x = wordHeapLabel y) :
    x ≤ y ∨ y ≤ x := by
  apply wordHeap_dependent_comparable
  rw [hlab]
  exact Std.Refl.refl _

theorem wordHeap_upper_cover_label_injective
    [Std.Refl dependent] [Std.Symm dependent]
    {x y z : WordHeapPiece word dependent} (hxy : x ⋖ y) (hxz : x ⋖ z)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases wordHeap_equal_labels_comparable hlab with hyz | hzy
  · rcases hxz.eq_or_eq hxy.le hyz with hyx | hyz <;> aesop
  · rcases hxy.eq_or_eq hxz.le hzy with hzx | hzy <;> aesop

theorem wordHeap_lower_cover_label_injective
    [Std.Refl dependent] [Std.Symm dependent]
    {x y z : WordHeapPiece word dependent} (hyx : y ⋖ x) (hzx : z ⋖ x)
    (hlab : wordHeapLabel y = wordHeapLabel z) : y = z := by
  rcases wordHeap_equal_labels_comparable hlab with hyz | hzy
  · rcases hyx.eq_or_eq hyz hzx.le with hzy | hzxEq <;> simp_all
  · rcases hzx.eq_or_eq hzy hyx.le with hyz | hyxEq <;> aesop

theorem wordHeap_maximal_label_injective
    [Std.Refl dependent] [Std.Symm dependent] (S : Finset (WordHeapPiece word dependent)) :
    Set.InjOn wordHeapLabel (historyMaximalPieces S : Set (WordHeapPiece word dependent)) := by
  intro x hx y hy hlab
  obtain ⟨hxS, hxmax⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨hyS, hymax⟩ := mem_historyMaximalPieces.1 hy
  rcases wordHeap_equal_labels_comparable hlab with hxy | hyx
  · exact (hxmax y hyS hxy).symm
  · exact hymax x hxS hyx

theorem wordHeap_maximal_card_le_labels [Fintype J] [DecidableEq J]
    {word : List J} {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent] (S : Finset (WordHeapPiece word dependent)) :
    (historyMaximalPieces S).card ≤ Fintype.card J := by
  rw [← Finset.card_image_iff.2 (wordHeap_maximal_label_injective S)]
  exact Finset.card_le_card (Finset.subset_univ _)

def wordHeapUpperCovers
    (x : WordHeapPiece word dependent) : Finset (WordHeapPiece word dependent) := by
  classical
  exact Finset.univ.filter (fun y => x ⋖ y)

def wordHeapLowerCovers
    (x : WordHeapPiece word dependent) : Finset (WordHeapPiece word dependent) := by
  classical
  exact Finset.univ.filter (fun y => y ⋖ x)

def dependentLabelFinset [Fintype J] (dependent : J → J → Prop) (j : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun i => dependent j i)

/-- A uniform degree bound in the label-dependence graph. -/
abbrev DegreeAtMost [Fintype J] (r : J → J → Prop) (Δ : ℕ) :=
  ∀ j, (dependentLabelFinset r j).card ≤ Δ

end

section
variable {J : Type*} [Fintype J] {word : List J} {dependent : J → J → Prop} [Std.Refl dependent]
    [Std.Symm dependent] (x : WordHeapPiece word dependent)

theorem wordHeap_upper_covers_card :
    (wordHeapUpperCovers x).card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  apply Finset.card_le_card_of_injOn wordHeapLabel
  · intro y hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, wordHeap_cover_dependent ((Finset.mem_filter.1 hy).2)⟩
  · exact fun y hy z hz => wordHeap_upper_cover_label_injective
      (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2

theorem wordHeap_lower_covers_card :
    (wordHeapLowerCovers x).card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  apply Finset.card_le_card_of_injOn wordHeapLabel
  · intro y hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, symm (wordHeap_cover_dependent ((Finset.mem_filter.1 hy).2))⟩
  · exact fun y hy z hz => wordHeap_lower_cover_label_injective
      (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hz).2

end

variable {J : Type*} (word : List J) (dependent : J → J → Prop)

def wordHeapCoverGraph :
    SimpleGraph (WordHeapPiece word dependent) where
  Adj x y := x ⋖ y ∨ y ⋖ x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    rcases h with h | h <;> exact h.ne rfl⟩

instance wordHeapCoverGraph_neighbor_fintype
    (x : WordHeapPiece word dependent) : Fintype ((wordHeapCoverGraph word dependent).neighborSet x) :=
  Fintype.ofFinite _

theorem wordHeapCoverGraph_neighbors {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) :
    (wordHeapCoverGraph word dependent).neighborFinset x = wordHeapUpperCovers x ∪ wordHeapLowerCovers x := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  simp [wordHeapUpperCovers, wordHeapLowerCovers]
  rfl

/-- The cover graph's degree is bounded by twice the number of dependent labels, uniformly in history size. -/
theorem wordHeapCoverGraph_degree_le [Fintype J] {word : List J} {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    (x : WordHeapPiece word dependent) :
    (wordHeapCoverGraph word dependent).degree x ≤
      2 * (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  change ((wordHeapCoverGraph word dependent).neighborFinset x).card ≤ _
  rw [wordHeapCoverGraph_neighbors]
  bound [wordHeap_upper_covers_card x, wordHeap_lower_covers_card x, Finset.card_union_le (wordHeapUpperCovers x) (wordHeapLowerCovers x)]

end NearlyMinimax
