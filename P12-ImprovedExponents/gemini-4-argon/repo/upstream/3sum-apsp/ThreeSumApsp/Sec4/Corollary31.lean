module

public import ThreeSumApsp.Sec4.Boxes
public import ThreeSumApsp.Sec2.Tiling
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.GeomSum
public import ThreeSumApsp.Sec4.ChoosingParameters
public import ThreeSumApsp.Util.Asymptotics.Dominated

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}

/-! ### The sets `Z`, `V` and `F_V` (Section 4.2) -/

/-- Section 4.2: "Z := {ℓ ∈ Q : τ_ℓ = P₀} (the levels at which τ chooses P₀)". -/
def Zof (Q : Finset (Fin L)) (τ : Leaf L) : Finset (Fin L) :=
  Q.filter fun ℓ => τ ℓ = Term.P0

/-- Section 2.4.3: a leaf contributes to `η` exactly if it agrees with the private leaf of `η`
outside the inner set. -/
lemma contributes_iff_eq_privateLeaf (η : OutStr L) (τ : Leaf L) :
    Leaf.Contributes τ η ↔ ∀ ℓ, ℓ ∉ innerSetO η → τ ℓ = privateLeaf η ℓ := by
  refine forall_congr' fun ℓ => ?_
  rw [Term.contributes_iff, mem_innerSetO]
  exact or_iff_not_imp_left

/-- Outside the inner set the private leaf does not choose `P₀`. -/
lemma privateLeaf_ne_P0 {η : OutStr L} {ℓ : Fin L} (hℓ : ℓ ∉ innerSetO η) :
    privateLeaf η ℓ ≠ Term.P0 :=
  fun h => hℓ (mem_innerSetO.2 ((OutVar.privateTerm_eq_P0_iff _).1 h))

/-- `Z` is a set of levels of `Q`. -/
lemma Zof_subset (Q : Finset (Fin L)) (τ : Leaf L) : Zof Q τ ⊆ Q :=
  filter_subset _ _

/-- A leaf contributing to `η` chooses `P₀` exactly at the levels of `Z`. -/
lemma P0Levels_eq_Zof (η : OutStr L) (τ : Leaf L) (hτ : Leaf.Contributes τ η) :
    P0Levels τ = Zof (innerSetO η) τ := by
  ext ℓ
  rw [Zof, mem_filter, mem_P0Levels]
  exact ⟨fun h => ⟨P0Levels_subset hτ (mem_P0Levels.2 h), h⟩, fun h => h.2⟩

/-- Section 4.2: "the order of τ is m - |Z|", for a leaf `τ` contributing to an output string `η`
with inner set `Q`. -/
theorem order_eq_sub_card_Zof (m : ℕ) (η : OutStr L) (τ : Leaf L)
    (hτ : Leaf.Contributes τ η) :
    order m τ = (m : ℤ) - ((Zof (innerSetO η) τ).card : ℤ) := by
  rw [order, P0Levels_eq_Zof η τ hτ]

/-- A leaf of order at least `t` contributing to `η` chooses `P₀` at most `m - t` times. -/
lemma card_Zof_le {m t : ℕ} {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) : (Zof (innerSetO η) τ).card ≤ m - t := by
  have := order_eq_sub_card_Zof m η τ hτ
  omega

/-- `V` is a set of levels of `Q`. -/
theorem Vof_subset (m t : ℕ) {Q Z : Finset (Fin L)} (hZ : Z ⊆ Q) : Vof m t Q Z ⊆ Q :=
  union_subset hZ ((lowest_subset _ _).trans sdiff_subset)

/-- Section 4.2: "the set V has exactly m - t levels". -/
theorem card_Vof {m t : ℕ} (ht : t ≤ m) {Q Z : Finset (Fin L)} (hQ : Q.card = m) (hZ : Z ⊆ Q)
    (hZc : Z.card ≤ m - t) : (Vof m t Q Z).card = m - t := by
  have hdisj : Disjoint Z (lowest (m - t - Z.card) (Q \ Z)) :=
    disjoint_of_subset_right (lowest_subset _ _) disjoint_sdiff
  rw [Vof, card_union_of_disjoint hdisj, card_lowest, card_sdiff_of_subset hZ, hQ]
  -- `|Z| + min (m - t - |Z|) (m - |Z|) = m - t`, because `|Z| ≤ m - t ≤ m`
  omega

/-- `V` is `Z` "padded from the bottom" (Section 4.2): the levels added to `Z` are below the levels
of `Q` that are left out. -/
lemma Vof_sdiff_lt (m t : ℕ) (Q Z : Finset (Fin L)) :
    ∀ ℓ ∈ Vof m t Q Z \ Z, ∀ ℓ' ∈ Q \ Vof m t Q Z, ℓ < ℓ' := by
  intro ℓ hℓ ℓ' hℓ'
  obtain ⟨hV, hZ⟩ := mem_sdiff.1 hℓ
  obtain ⟨hQ', hV'⟩ := mem_sdiff.1 hℓ'
  obtain ⟨hZ', hlow'⟩ := not_or.1 (mt mem_union.2 hV')
  -- `ℓ` is one of the lowest levels of `Q ∖ Z`, and `ℓ'` is another level of `Q ∖ Z`
  exact lowest_lt ((mem_union.1 hV).resolve_left hZ)
    (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hQ', hZ'⟩, hlow'⟩)

/-- Section 4.2: `F_V` "is the longest initial segment of Q contained in V". Here: it is contained
in `V`. -/
theorem FV_subset (Q V : Finset (Fin L)) : FV Q V ⊆ V := by
  intro ℓ hℓ
  by_contra hV
  exact lt_irrefl ℓ ((mem_filter.1 hℓ).2 ℓ (mem_sdiff.2 ⟨(mem_filter.1 hℓ).1, hV⟩))

/-- Section 4.2: `F_V` "is the longest initial segment of Q contained in V". Here: it is an initial
segment of `Q`. -/
lemma mem_FV_of_le {Q V : Finset (Fin L)} {ℓ ℓ' : Fin L} (hℓ : ℓ ∈ FV Q V)
    (hℓ' : ℓ' ∈ Q) (hle : ℓ' ≤ ℓ) : ℓ' ∈ FV Q V :=
  mem_filter.2 ⟨hℓ', fun x hx => hle.trans_lt ((mem_filter.1 hℓ).2 x hx)⟩

/-- The core of the proof of Lemma 27: "V ∖ F_V ⊆ Z says that every level of V ∖ Z is below" the
lowest level, that is every level, of `Q ∖ V`. The paper's case `V = Q` needs no separate treatment:
then `Q ∖ V` is empty. -/
lemma sdiff_FV_subset_iff {Q V Z : Finset (Fin L)} (hV : V ⊆ Q) :
    V \ FV Q V ⊆ Z ↔ ∀ ℓ ∈ V \ Z, ∀ ℓ' ∈ Q \ V, ℓ < ℓ' := by
  constructor
  · intro h ℓ hℓ ℓ' hℓ'
    obtain ⟨hℓV, hℓZ⟩ := mem_sdiff.1 hℓ
    have hℓF : ℓ ∈ FV Q V := by
      by_contra hF
      exact hℓZ (h (mem_sdiff.2 ⟨hℓV, hF⟩))
    exact (mem_filter.1 hℓF).2 ℓ' hℓ'
  · intro h ℓ hℓ
    obtain ⟨hℓV, hℓF⟩ := mem_sdiff.1 hℓ
    by_contra hZ
    exact hℓF (mem_filter.2 ⟨hV hℓV, h ℓ (mem_sdiff.2 ⟨hℓV, hZ⟩)⟩)

/-! ### The sets `𝓑_V` (Section 4.2) -/

section BV

variable {η : OutStr L} {V : Finset (Fin L)} {π : Cube L} {ℓ : Fin L}

/-- A cube of `𝓑_V` has a star at each level of `F_V`. -/
lemma BV_star (hπ : π ∈ BV η V) (hℓ : ℓ ∈ FV (innerSetO η) V) : π ℓ = CubeSymbol.star :=
  ((mem_filter.1 hπ).2 ℓ).1 hℓ

/-- A cube of `𝓑_V` has `P₀` at each level of `V ∖ F_V`. -/
lemma BV_P0 (hπ : π ∈ BV η V) (hℓ : ℓ ∈ V \ FV (innerSetO η) V) :
    π ℓ = CubeSymbol.term Term.P0 :=
  ((mem_filter.1 hπ).2 ℓ).2.1 hℓ

/-- A cube of `𝓑_V` has one of the nine terms `P_ij` at each level of `Q ∖ V`. -/
lemma BV_nine (hπ : π ∈ BV η V) (hℓ : ℓ ∈ innerSetO η \ V) :
    ∃ i j, π ℓ = CubeSymbol.term (Term.P i j) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.1 hℓ

/-- A cube of `𝓑_V` has the term of the private leaf of `η` at each level outside `Q`. -/
lemma BV_outside (hπ : π ∈ BV η V) (hℓ : ℓ ∉ innerSetO η) :
    π ℓ = CubeSymbol.term (privateLeaf η ℓ) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.2 hℓ

/-- Every level is of one of the four kinds in the definition of `𝓑_V`. -/
lemma level_cases (Q V : Finset (Fin L)) (ℓ : Fin L) :
    ℓ ∈ FV Q V ∨ ℓ ∈ V \ FV Q V ∨ ℓ ∈ Q \ V ∨ ℓ ∉ Q := by
  simp only [mem_sdiff]
  tauto

/-- The stars of a cube of `𝓑_V` are at the levels of `F_V`. -/
theorem BV_starLevels (hπ : π ∈ BV η V) : Cube.starLevels π = FV (innerSetO η) V := by
  ext ℓ
  rw [Cube.mem_starLevels]
  refine ⟨fun h => ?_, BV_star hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · exact hℓ
  · simp [BV_P0 hπ hℓ] at h
  · obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
    simp [hij] at h
  · simp [BV_outside hπ hℓ] at h

/-- The symbols `P₀` of a cube of `𝓑_V` are at the levels of `V ∖ F_V`. -/
theorem BV_P0Levels (hπ : π ∈ BV η V) : Cube.P0Levels π = V \ FV (innerSetO η) V := by
  ext ℓ
  rw [Cube.mem_P0Levels]
  refine ⟨fun h => ?_, BV_P0 hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · simp [BV_star hπ hℓ] at h
  · exact hℓ
  · obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
    simp [hij] at h
  · rw [BV_outside hπ hℓ] at h
    exact absurd (CubeSymbol.term.inj h) (privateLeaf_ne_P0 hℓ)

/-- The levels at which a cube of `𝓑_V` has a star or `P₀` are those of `V`. -/
theorem BV_starLevels_union_P0Levels (hπ : π ∈ BV η V) :
    Cube.starLevels π ∪ Cube.P0Levels π = V := by
  rw [BV_starLevels hπ, BV_P0Levels hπ, union_sdiff_of_subset (FV_subset _ _)]

/-- Two cubes of `𝓑_V` with the same symbols at the levels of `Q ∖ V` are equal. -/
lemma BV_ext {π' : Cube L} (hπ : π ∈ BV η V) (hπ' : π' ∈ BV η V)
    (h : ∀ ℓ ∈ innerSetO η \ V, π ℓ = π' ℓ) : π = π' := by
  funext ℓ
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · rw [BV_star hπ hℓ, BV_star hπ' hℓ]
  · rw [BV_P0 hπ hℓ, BV_P0 hπ' hℓ]
  · exact h ℓ hℓ
  · rw [BV_outside hπ hℓ, BV_outside hπ' hℓ]

/-- At a level of `Q ∖ V`, a cube of `𝓑_V` has the term of each of its leaves. -/
lemma BV_eq_term_of_leaf (hπ : π ∈ BV η V) {τ : Leaf L} (hτ : τ ∈ Cube.leaves π)
    (hℓ : ℓ ∈ innerSetO η \ V) : π ℓ = CubeSymbol.term (τ ℓ) := by
  obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
  rw [hij, Cube.eq_of_mem_leaves hτ hij]

end BV

/-- The symbols allowed at level `ℓ` in a cube of `𝓑_V`. -/
def allowed (η : OutStr L) (V : Finset (Fin L)) (ℓ : Fin L) : Finset CubeSymbol :=
  univ.filter fun s =>
    (ℓ ∈ FV (innerSetO η) V → s = CubeSymbol.star) ∧
    (ℓ ∈ V \ FV (innerSetO η) V → s = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, s = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → s = CubeSymbol.term (privateLeaf η ℓ))

/-- `𝓑_V` is the set of all cubes with an allowed symbol at every level. -/
lemma BV_eq_piFinset (η : OutStr L) (V : Finset (Fin L)) :
    BV η V = Fintype.piFinset (allowed η V) := by
  ext π
  simp [BV, allowed, Fintype.mem_piFinset]

/-- Nine symbols are allowed at a level of `Q ∖ V`, and one at every other level. -/
lemma card_allowed (η : OutStr L) (V : Finset (Fin L)) (hV : V ⊆ innerSetO η)
    (ℓ : Fin L) : (allowed η V ℓ).card = if ℓ ∈ innerSetO η \ V then 9 else 1 := by
  have hnine :
      (univ.filter fun s : CubeSymbol => ∃ i j, s = CubeSymbol.term (Term.P i j)).card = 9 := by
    decide
  have hFV := @FV_subset L (innerSetO η) V ℓ
  have hVQ := @hV ℓ
  unfold allowed
  by_cases hF : ℓ ∈ FV (innerSetO η) V
  · simp [hF, hFV hF, hVQ (hFV hF), filter_eq']
  by_cases hℓV : ℓ ∈ V
  · simp [hF, hℓV, hVQ hℓV, filter_eq']
  by_cases hℓQ : ℓ ∈ innerSetO η
  · simp [hF, hℓV, hℓQ, hnine]
  · simp [hF, hℓV, hℓQ, filter_eq']

/-- Section 4.2: `𝓑_V` is "the set of the 9^t cubes π with" the symbols above. -/
theorem card_BV (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (V : Finset (Fin L)) (hV : V ∈ Vsets m t η) : (BV η V).card = 9 ^ t := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [BV_eq_piFinset η V, Fintype.card_piFinset]
  simp only [card_allowed η V hVQ]
  rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset hVQ, hη, hVc,
    Nat.sub_sub_self ht]

/-- Section 4.2: "Every cube in 𝓑_V is a box: it satisfies condition (i) of the definition because
it has |V| = m - t symbols P₀ or stars, and condition (ii) because its stars are below its symbols
P₀, since F_V is an initial segment of Q." -/
theorem BV_isBox {m t : ℕ} {η : OutStr L} {V : Finset (Fin L)} (hV : V ∈ Vsets m t η) {π : Cube L}
    (hπ : π ∈ BV η V) : IsBox m t π := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [IsBox, BV_starLevels hπ, BV_P0Levels hπ, add_comm,
    card_sdiff_add_card_eq_card (FV_subset _ _)]
  refine ⟨hVc.le, fun ℓ hℓ ℓ' hℓ' => ?_⟩
  -- otherwise `ℓ' ≤ ℓ` would be a level of the initial segment `F_V`
  obtain ⟨hℓ'V, hℓ'F⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hℓ'F (mem_FV_of_le hℓ (hVQ hℓ'V) (not_lt.1 hlt))

/-- The sets `𝓑_V` for different `V` are disjoint, so that the double sum `∑_V ∑_{π ∈ 𝓑_V}` of Lemma
28 runs over each box of `⋃_V 𝓑_V` once. -/
theorem BV_pairwiseDisjoint (η : OutStr L) (s : Set (Finset (Fin L))) :
    s.PairwiseDisjoint (BV η) :=
  -- a cube of `𝓑_V` determines `V`
  fun _ _ _ _ hne => disjoint_left.2 fun _ hπ hπ' =>
    hne ((BV_starLevels_union_P0Levels hπ).symm.trans (BV_starLevels_union_P0Levels hπ'))

/-- If `τ` contributes to `η` and `V ∖ F_V ⊆ Z ⊆ V`, then `τ` with stars at the levels of `F_V` is a
cube of `𝓑_V`. -/
lemma starAt_mem_BV {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L}
    (hτ : Leaf.Contributes τ η) (hVZ : V \ FV (innerSetO η) V ⊆ Zof (innerSetO η) τ)
    (hZV : Zof (innerSetO η) τ ⊆ V) : Cube.starAt (FV (innerSetO η) V) τ ∈ BV η V := by
  refine mem_filter.2
    ⟨mem_univ _, fun ℓ => ⟨fun hF => if_pos hF, fun hVF => ?_, fun hQV => ?_, fun hQ => ?_⟩⟩
  · -- at a level of `V ∖ F_V`, which is a level of `Z`, the leaf chooses `P₀`
    rw [Cube.starAt, if_neg (mem_sdiff.1 hVF).2, (mem_filter.1 (hVZ hVF)).2]
  · -- at a level of `Q ∖ V`, which is not a level of `Z`, the leaf chooses another term
    obtain ⟨hQ, hV⟩ := mem_sdiff.1 hQV
    rw [Cube.starAt, if_neg fun hF => hV (FV_subset _ _ hF)]
    cases hterm : τ ℓ with
    | P i j => exact ⟨i, j, rfl⟩
    | P0 => exact absurd (hZV (mem_filter.2 ⟨hQ, hterm⟩)) hV
  · -- outside `Q` the leaf agrees with the private leaf
    rw [Cube.starAt, if_neg fun hF : ℓ ∈ FV (innerSetO η) V => hQ (mem_filter.1 hF).1,
      (contributes_iff_eq_privateLeaf η τ).1 hτ ℓ hQ]

/-- Section 4.2: the box of a leaf `τ` of order at least `t` contributing to `η`: "The box of τ then
agrees with τ everywhere, except that it has a star at every level of Q below the level where we
stopped", these levels being those of `F_V` for the `V` of `τ`. -/
def boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Vof m t (innerSetO η) (Zof (innerSetO η) τ))) τ

/-- A leaf is a leaf of its box. -/
theorem mem_leaves_boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) :
    τ ∈ Cube.leaves (boxOfLeaf m t η τ) :=
  Cube.mem_leaves_starAt _ τ

/-- Section 4.2: "When V is the set defined above from a leaf τ, the box of τ is the one in 𝓑_V with
the terms of τ at the levels of Q ∖ V": it is a cube of `𝓑_V`, for the set `V` of `τ`. -/
theorem boxOfLeaf_mem_BV (m t : ℕ) {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    boxOfLeaf m t η τ ∈ BV η (Vof m t (innerSetO η) (Zof (innerSetO η) τ)) :=
  starAt_mem_BV hτ
    ((sdiff_FV_subset_iff (Vof_subset m t (Zof_subset _ τ))).2 (Vof_sdiff_lt m t _ _))
    subset_union_left

/-- Section 4.2: "A leaf contributing to w that chooses P₀ at the set Z of levels is a leaf of a box
of 𝓑_V if and only if it chooses P₀ at every level of V ∖ F_V and at no level of Q ∖ V, that is, V ∖
F_V ⊆ Z ⊆ V". -/
theorem exists_mem_BV_leaf_iff {η : OutStr L} {V : Finset (Fin L)} (hV : V ⊆ innerSetO η)
    {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    (∃ π ∈ BV η V, τ ∈ Cube.leaves π) ↔
      V \ FV (innerSetO η) V ⊆ Zof (innerSetO η) τ ∧ Zof (innerSetO η) τ ⊆ V := by
  constructor
  · rintro ⟨π, hπ, hτπ⟩
    refine ⟨fun ℓ hℓ => mem_filter.2 ⟨hV (mem_sdiff.1 hℓ).1, ?_⟩, fun ℓ hℓ => ?_⟩
    · exact Cube.eq_of_mem_leaves hτπ (BV_P0 hπ hℓ)
    · by_contra hℓV
      obtain ⟨hℓQ, hterm⟩ := mem_filter.1 hℓ
      obtain ⟨i, j, hij⟩ := BV_nine hπ (mem_sdiff.2 ⟨hℓQ, hℓV⟩)
      simp [Cube.eq_of_mem_leaves hτπ hij] at hterm
  · exact fun ⟨hVZ, hZV⟩ => ⟨_, starAt_mem_BV hτ hVZ hZV, Cube.mem_leaves_starAt _ τ⟩

/-- Section 4.2: "Furthermore, it is a leaf of exactly one of these boxes, namely, the one with its
terms at the levels of Q ∖ V." -/
theorem BV_leaf_unique {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L} {π π' : Cube L}
    (hπ : π ∈ BV η V) (hτπ : τ ∈ Cube.leaves π) (hπ' : π' ∈ BV η V) (hτπ' : τ ∈ Cube.leaves π') :
    π = π' :=
  BV_ext hπ hπ' fun _ hℓ =>
    (BV_eq_term_of_leaf hπ hτπ hℓ).trans (BV_eq_term_of_leaf hπ' hτπ' hℓ).symm

/-! ### Figure 10 -/

/-! ### Lemma 27 -/

/-- **Lemma 27**. "Let Q be a set of m levels, and let 0 ≤ t ≤ m. For every Z ⊆ Q
with |Z| ≤ m - t, there is exactly one set V ⊆ Q with |V| = m - t and V ∖ F_V ⊆ Z ⊆ V, namely Z
together with the m - t - |Z| lowest levels of Q ∖ Z." This set is `Vof m t Q Z`. -/
theorem lemma_27 {L : ℕ} (m t : ℕ) (ht : t ≤ m) (Q Z : Finset (Fin L)) (hQ : Q.card = m)
    (hZ : Z ⊆ Q) (hZc : Z.card ≤ m - t) (V : Finset (Fin L)) :
    (V ⊆ Q ∧ V.card = m - t ∧ V \ FV Q V ⊆ Z ∧ Z ⊆ V) ↔ V = Vof m t Q Z := by
  constructor
  · rintro ⟨hVQ, hVc, hVZ, hZV⟩
    -- "Q ∖ Z is the disjoint union of V ∖ Z and Q ∖ V", and `V ∖ Z` lies below `Q ∖ V`,
    -- so "V ∖ Z consists of the lowest levels of Q ∖ Z".
    have hrest : (Q \ Z) \ (V \ Z) = Q \ V := sdiff_sdiff_sdiff_cancel_right hZV
    have hlow := eq_lowest_of_lt (sdiff_subset_sdiff hVQ (le_refl Z))
      (hrest ▸ (sdiff_FV_subset_iff hVQ).1 hVZ)
    rw [card_sdiff_of_subset hZV, hVc] at hlow
    rw [Vof, ← hlow, union_sdiff_of_subset hZV]
  · rintro rfl
    have hVQ := Vof_subset m t hZ
    exact ⟨hVQ, card_Vof ht hQ hZ hZc, (sdiff_FV_subset_iff hVQ).2 (Vof_sdiff_lt m t Q Z),
      subset_union_left⟩

/-! ### Lemma 28 -/

/-- **Lemma 28**, first sentence, first half. "Let w be an output string, with inner set
Q. The leaves of order at least t contributing to w are exactly the leaves of the boxes in ⋃_V 𝓑_V,
the union over all V ⊆ Q with |V| = m - t". -/
theorem lemma_28_leaves {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) :
    (Leaf.Contributes τ η ∧ (t : ℤ) ≤ order m τ) ↔
      ∃ π ∈ (Vsets m t η).biUnion (BV η), τ ∈ Cube.leaves π := by
  constructor
  · -- "Conversely, a leaf τ contributing to w, of order at least t," is a leaf of its box.
    rintro ⟨hτ, hord⟩
    refine ⟨boxOfLeaf m t η τ, mem_biUnion.2 ⟨_, mem_powersetCard.2 ?_, boxOfLeaf_mem_BV m t hτ⟩,
      mem_leaves_boxOfLeaf m t η τ⟩
    exact ⟨Vof_subset m t (Zof_subset _ τ),
      card_Vof ht hη (Zof_subset _ τ) (card_Zof_le hτ hord)⟩
  · -- "Every leaf of a box of 𝓑_V agrees with the private leaf of w outside Q, so it contributes
    -- to w", and a box only contains leaves of order at least `t`.
    rintro ⟨π, hπ, hτπ⟩
    obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
    exact ⟨(contributes_iff_eq_privateLeaf η τ).2 fun ℓ hℓ =>
        Cube.eq_of_mem_leaves hτπ (BV_outside hπV hℓ),
      le_order_of_mem_leaves ht (BV_isBox hV hπV) hτπ⟩

/-- Proof of Lemma 28: "By Lemma 27, exactly one V satisfies this condition": if a leaf of order at
least `t` contributing to `η` is a leaf of a box of `𝓑_V`, then `V` is the set of the leaf. -/
lemma eq_Vof_of_mem_leaves {m t : ℕ} (ht : t ≤ m) {η : OutStr L}
    (hη : (innerSetO η).card = m) {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) {V : Finset (Fin L)} (hV : V ∈ Vsets m t η) {π : Cube L}
    (hπ : π ∈ BV η V) (hτπ : τ ∈ Cube.leaves π) :
    V = Vof m t (innerSetO η) (Zof (innerSetO η) τ) := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  obtain ⟨hVZ, hZV⟩ := (exists_mem_BV_leaf_iff hVQ hτ).1 ⟨π, hπ, hτπ⟩
  exact (lemma_27 m t ht _ _ hη (Zof_subset _ τ) (card_Zof_le hτ hord) V).1 ⟨hVQ, hVc, hVZ, hZV⟩

/-- **Lemma 28**, first sentence, second half: "and each of them is a leaf of exactly one
of these boxes." -/
theorem lemma_28_unique {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) (hτ : Leaf.Contributes τ η) (hord : (t : ℤ) ≤ order m τ) :
    ∃! π : Cube L, π ∈ (Vsets m t η).biUnion (BV η) ∧ τ ∈ Cube.leaves π := by
  obtain ⟨π, hπ, hτπ⟩ := (lemma_28_leaves m t ht η hη τ).1 ⟨hτ, hord⟩
  refine ⟨π, ⟨hπ, hτπ⟩, ?_⟩
  rintro π' ⟨hπ', hτπ'⟩
  -- the two boxes belong to the same `V`, and `𝓑_V` has only one box with the leaf `τ`
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  obtain ⟨V', hV', hπV'⟩ := mem_biUnion.1 hπ'
  obtain rfl : V' = V := (eq_Vof_of_mem_leaves ht hη hτ hord hV' hπV' hτπ').trans
    (eq_Vof_of_mem_leaves ht hη hτ hord hV hπV hτπ).symm
  exact BV_leaf_unique hπV' hτπ' hπV hτπ

/-- The equation of Lemma 28 for an arbitrary function `g` of the leaves in the place of the
products: the sum of `g` over the leaves contributing to `η` is the sum over the leaves of order
below `t` plus the sum over the leaves of the boxes. -/
theorem Lemma28.sum_contributing {G : Type*} [AddCommMonoid G] (m t : ℕ) (ht : t ≤ m)
    (η : OutStr L) (hη : (innerSetO η).card = m) (g : Leaf L → G) :
    ∑ τ : Leaf L with Leaf.Contributes τ η, g τ =
      ∑ τ ∈ lowLeaves m t η, g τ + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, ∑ τ ∈ Cube.leaves π, g τ := by
  have hdisjoint :
      (((Vsets m t η).biUnion (BV η) : Finset (Cube L)) : Set (Cube L)).PairwiseDisjoint
        Cube.leaves := by
    intro π hπ π' hπ' hne
    rw [Function.onFun, disjoint_left]
    intro τ hτ hτ'
    obtain ⟨hc, hord⟩ := (lemma_28_leaves m t ht η hη τ).2 ⟨π, hπ, hτ⟩
    exact hne ((lemma_28_unique m t ht η hη τ hc hord).unique ⟨hπ, hτ⟩ ⟨hπ', hτ'⟩)
  have hhigh : ((Vsets m t η).biUnion (BV η)).biUnion Cube.leaves =
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ ¬ order m τ < (t : ℤ) := by
    ext τ
    rw [mem_biUnion, mem_filter, not_lt, ← lemma_28_leaves m t ht η hη τ]
    simp
  -- The sums over the sets `V`, the boxes and their leaves are one sum over the contributing leaves
  -- of order at least `t`; the contributing leaves split into those of order below `t` and these.
  rw [← sum_biUnion (BV_pairwiseDisjoint η _), ← sum_biUnion hdisjoint, hhigh, lowLeaves,
    ← filter_filter, ← filter_filter, sum_filter_add_sum_filter_not]

/-- **Lemma 28**, the displayed equation, for arbitrary input arrays: the sum of the products at the
leaves contributing to `η`, which is `Mult(a, b)[η]`, equals the sum over the leaves of order below
`t` plus the sum of the values of the boxes. See `lemma_28` for the form with `(X_Q Y_Q)[η]` on the
left. -/
theorem Lemma28.Mult_eq_querySum (m t : ℕ) (ht : t ≤ m) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (η : OutStr L) (hη : (innerSetO η).card = m) : Mult a b η = querySum m t a b η :=
  Lemma28.sum_contributing m t ht η hη fun τ => Phi τ a * Psi τ b

/-- The terms of the sum of Lemma 28 stand for the `10^m` leaves contributing to `η`, each of them
once: one leaf for each product, and its leaves for each box. The bound on the partial sums of a
query (word size, the proof of Theorem 30) rests on this count. -/
theorem Lemma28.card_leaves (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card + ∑ π ∈ (Vsets m t η).biUnion (BV η), (Cube.leaves π).card = 10 ^ m := by
  have hsplit := Lemma28.sum_contributing m t ht η hη fun _ => 1
  rw [← card_eq_sum_ones, card_filter_contributes η hη] at hsplit
  rw [hsplit, sum_biUnion (BV_pairwiseDisjoint η _)]
  simp

/-- The leaves of order below `t` contributing to `η`, sorted by their order, which is at least 0.
-/
lemma lowLeaves_eq_biUnion (m t : ℕ) (η : OutStr L) (hη : (innerSetO η).card = m) :
    lowLeaves m t η = (range t).biUnion fun d =>
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ order m τ = d := by
  ext τ
  simp only [lowLeaves, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
  constructor
  · rintro ⟨hτ, hlt⟩
    have hnonneg := order_nonneg hη hτ
    exact ⟨(order m τ).toNat, by omega, hτ, (Int.toNat_of_nonneg hnonneg).symm⟩
  · rintro ⟨d, hd, hτ, heq⟩
    exact ⟨hτ, by omega⟩

/-- **Lemma 28**, last line: "a sum of ∑_{d=0}^{t-1} α_d products and α_t values of
boxes."  The third clause says that these α_t cubes are different, that is, that the sets 𝓑_V are
disjoint; Section 4.2 has it in the words "w has exactly α_t boxes". -/
theorem lemma_28_counts {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card = ∑ d ∈ range t, alpha m d ∧
      ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t ∧
      ((Vsets m t η).biUnion (BV η)).card = alpha m t := by
  -- "there are binom(m, m-t) sets V with 9^t boxes each"
  have hsum : ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t := by
    rw [sum_congr rfl fun V hV => card_BV m t ht η hη V hV, sum_const, Vsets,
      card_powersetCard, hη, Nat.choose_symm ht, smul_eq_mul, alpha]
  refine ⟨?_, hsum, ?_⟩
  · -- "α_d leaves of order d contribute to w"
    rw [lowLeaves_eq_biUnion m t η hη, card_biUnion]
    · exact sum_congr rfl fun d _ => sec2_card_contributing_of_order η hη d
    · intro d _ d' _ hne
      rw [Function.onFun, disjoint_left]
      intro τ hd hd'
      exact hne (by exact_mod_cast (mem_filter.1 hd).2.2.symm.trans (mem_filter.1 hd').2.2)
  · rw [card_biUnion (BV_pairwiseDisjoint η _), hsum]




/-- Membership in the set of all boxes. -/
@[simp]
theorem mem_boxes {L m t : ℕ} {π : Cube L} : π ∈ boxes L m t ↔ IsBox m t π := by
  simp [boxes]

/-- Membership in the set of the boxes with `e` stars. -/
@[simp]
theorem mem_boxesWithStars {L m t e : ℕ} {π : Cube L} :
    π ∈ boxesWithStars L m t e ↔ IsBox m t π ∧ (Cube.starLevels π).card = e := by
  simp [boxesWithStars, boxes]

/-! ### The count -/

/-- For `f ≤ m ≤ L`, the number of leaves that choose `P₀` at exactly `f` levels is `β_{m-f}`
(Section 2.4.3). -/
lemma card_leaves_P0 {L m f : ℕ} (hmL : m ≤ L) (hf : f ≤ m) :
    (univ.filter fun τ : Leaf L => (P0Levels τ).card = f).card = beta L m (m - f) := by
  rw [← card_filter_order_eq hmL (m - f) (Nat.sub_le _ _)]
  congr 1
  ext τ
  rw [mem_filter, mem_filter, order]
  simp only [mem_univ, true_and]
  omega

/-- Proof of Lemma 29, "The count": "There are hence (f+1) binom(L, f) 9^{L-f} = (f+1) β_{m-f} such
boxes", namely boxes with `f` symbols `P₀` or stars, for `f ≤ m - t`. -/
theorem Lemma29.card_filter (L m t f : ℕ) (hmL : m ≤ L) (hf : f ≤ m - t) :
    ((boxes L m t).filter fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card
      = (f + 1) * beta L m (m - f) := by
  -- The pairs of a leaf with `f` symbols `P₀` and a number `e ≤ f`.
  have hpairs : ((univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1)).card
      = (f + 1) * beta L m (m - f) := by
    rw [card_product, card_leaves_P0 hmL (by omega), card_range, mul_comm]
  have hpair : ∀ p ∈ (univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1),
      (P0Levels p.1).card = f ∧ p.2 < f + 1 := fun p hp =>
    ⟨(mem_filter.1 (mem_product.1 hp).1).2, mem_range.1 (mem_product.1 hp).2⟩
  -- A box goes to "the leaf we get by replacing its stars with P₀" and the number of its stars;
  -- a pair goes to the cube obtained "by turning the e lowest symbols P₀ of that leaf into stars".
  rw [← hpairs]
  refine card_bij' (fun π _ => (Cube.starsToP0 π, (Cube.starLevels π).card))
    (fun p _ => starLowest p.2 p.1) (fun π hπ => ?_) (fun p hp => ?_) (fun π hπ => ?_)
    fun p hp => ?_
  · -- the pair of such a box is such a pair
    have := (mem_filter.1 hπ).2
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_range,
      card_P0Levels_starsToP0]
    omega
  · -- the cube of such a pair is such a box: its leaf is the leaf of the pair
    obtain ⟨hτ, -⟩ := hpair p hp
    rw [mem_filter, mem_boxes, ← card_P0Levels_starsToP0, starsToP0_starLowest]
    exact ⟨isBox_starLowest m t p.2 p.1 (by omega), hτ⟩
  · -- from a box to its pair and back
    exact (eq_starLowest_starsToP0 π (mem_boxes.1 (mem_filter.1 hπ).1).2).symm
  · -- from a pair `(τ, e)` to its cube and back: the cube has `min e f = e` stars
    obtain ⟨hτ, he⟩ := hpair p hp
    rw [starsToP0_starLowest, starLevels_starLowest, card_lowest, hτ,
      min_eq_left (by omega)]

/-- **Lemma 29**, first sentence.  "There are at most (m+1) ∑_{d=t}^{m} β_d boxes." -/
theorem lemma_29_count (L m t : ℕ) (hL : 10 * m ≤ L) (ht : t ≤ m) :
    (boxes L m t).card ≤ (m + 1) * ∑ d ∈ Finset.Icc t m, beta L m d := by
  -- Sort the boxes by the number `f ≤ m - t` of their symbols `P₀` or stars.
  have hsort : (boxes L m t).card = ∑ f ∈ range (m - t + 1),
      ((boxes L m t).filter
        fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card := by
    refine card_eq_sum_card_fiberwise fun π hπ => ?_
    have := (mem_boxes.1 (mem_coe.1 hπ)).1
    simp only [coe_range, Set.mem_Iio]
    omega
  -- The order `d = m - f` runs from `t` to `m`.
  have hreflect : ∑ f ∈ range (m - t + 1), beta L m (m - f) = ∑ d ∈ Finset.Icc t m, beta L m d := by
    rw [range_eq_Ico, sum_Ico_reflect _ _ (by omega)]
    congr 1
    ext d
    simp only [mem_Ico, mem_Icc]
    omega
  -- "summing over f ≤ m - t gives the upper bound on the number of boxes", since `f + 1 ≤ m + 1`
  rw [hsort, ← hreflect, mul_sum]
  refine sum_le_sum fun f hf => ?_
  have : f < m - t + 1 := mem_range.1 hf
  rw [Lemma29.card_filter L m t f (by omega) (by omega)]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### The values -/

/-- Proof of Lemma 29, "The values": "The boxes without stars are the leaves with at most m - t
symbols P₀". -/
theorem Lemma29.no_stars {L : ℕ} (m t : ℕ) (π : Cube L) :
    π ∈ boxesWithStars L m t 0 ↔ ∃ τ : Leaf L, (P0Levels τ).card ≤ m - t ∧ π = Cube.ofLeaf τ := by
  rw [mem_boxesWithStars]
  constructor
  · rintro ⟨hbox, hstar⟩
    refine ⟨Cube.starsToP0 π, ?_,
      Cube.eq_ofLeaf_of_starLevels_eq_empty π (card_eq_zero.1 hstar)⟩
    rw [card_P0Levels_starsToP0]
    exact hbox.1
  · rintro ⟨τ, hτ, rfl⟩
    rw [IsBox, Cube.starLevels_ofLeaf, Cube.P0Levels_ofLeaf]
    simpa using hτ

/-- Proof of Lemma 29, "The values": "the value of each of them is the product of its two numbers in
the encodings." -/
theorem Lemma29.val_ofLeaf {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) :
    Cube.val a b (Cube.ofLeaf τ) = Phi τ a * Psi τ b := by
  rw [Cube.val, Cube.leaves_ofLeaf, sum_singleton, productAt]

/-- Proof of **Lemma 29**, "The values": "For a box π with e ≥ 1 stars, let ℓ be the highest
level at which π has a star. [...] each of these strings is again a box, with e - 1 stars."  The
strings are the `π[ℓ ← λ]`, and `e + 1` stands for the paper's `e`. -/
theorem lemma_29_split {L m t e : ℕ} {π : Cube L} (hπ : π ∈ boxesWithStars L m t (e + 1))
    (hne : (Cube.starLevels π).Nonempty) (lam : Term) :
    Cube.replace π ((Cube.starLevels π).max' hne) lam ∈ boxesWithStars L m t e := by
  obtain ⟨⟨hcount, hbelow⟩, hcard⟩ := mem_boxesWithStars.1 hπ
  have hstar : (Cube.starLevels (Cube.replace π ((Cube.starLevels π).max' hne) lam)).card = e := by
    rw [Cube.starLevels_replace, card_erase_of_mem (max'_mem _ hne), hcard,
      Nat.add_sub_cancel]
  have hP0 := Cube.P0Levels_replace_subset π ((Cube.starLevels π).max' hne) lam
  refine mem_boxesWithStars.2 ⟨⟨?_, fun k hk k' hk' => ?_⟩, hstar⟩
  · -- One star fewer (`hstar`, `hcard`) and at most one symbol `P₀` more (`hmore`), so (i) stays.
    have := (card_le_card hP0).trans (card_insert_le _ _)
    omega
  · -- The new symbol is above the remaining stars, and so are the old symbols `P₀`, by (ii).
    rw [Cube.starLevels_replace, mem_erase] at hk
    rcases mem_insert.1 (hP0 hk') with hnew | hold
    · exact hnew ▸ lt_of_le_of_ne (le_max' _ k hk.2) hk.1
    · exact hbelow k hk.2 k' hold

/-- Proof of Lemma 29, "The values", the displayed recurrence: "val(π) = ∑_λ val(π[ℓ ← λ])", because
"The leaves of π are the leaves of the ten strings π[ℓ ← λ]". It holds for a star at any level `ℓ`
of any cube `π`. -/
theorem Lemma29.recurrence {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (ℓ : Fin L) (hℓ : π ℓ = CubeSymbol.star) :
    Cube.val a b π = ∑ lam : Term, Cube.val a b (Cube.replace π ℓ lam) := by
  unfold Cube.val
  rw [← sum_fiberwise (Cube.leaves π) (fun τ => τ ℓ)]
  refine sum_congr rfl fun lam _ => sum_congr ?_ fun _ _ => rfl
  ext τ
  rw [mem_filter, Cube.mem_leaves_replace hℓ]

/-- **Lemma 29**, second sentence, correctness: "Given the two encodings of a tile, we can compute
the values of all these boxes". The recurrence of the dynamic program of the proof (`dpValue`), run
on the two encodings, returns `val(π)` for every box `π` with `e` stars. That the ten strings π[ℓ ←
λ] are boxes with `e - 1` stars, so that their values can be looked up, is `lemma_29_split`. (For
the time and space bound see `docs/REMARKS.md`, "Section 4: running times".) -/
theorem lemma_29_values (L m t e : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L)
    (hπ : π ∈ boxesWithStars L m t e) :
    dpValue (encodingL a) (encodingR b) e π = Cube.val a b π := by
  induction e generalizing π with
  | zero =>
    obtain ⟨τ, -, rfl⟩ := (Lemma29.no_stars m t π).1 hπ
    rw [Lemma29.val_ofLeaf]
    -- by definition, the leaf of the cube `Cube.ofLeaf τ` is `τ`, and the encodings hold `Φ_τ(a)`
    -- and `Ψ_τ(b)`
    rfl
  | succ e ih =>
    have hne : (Cube.starLevels π).Nonempty :=
      card_pos.1 ((mem_boxesWithStars.1 hπ).2 ▸ Nat.succ_pos e)
    rw [dpValue, dif_pos hne,
      Lemma29.recurrence a b π _ (Cube.mem_starLevels.1 (max'_mem _ hne))]
    exact sum_congr rfl fun lam _ => ih _ (lemma_29_split hπ hne lam)




/-! ### The decay rate `ρ` and equation (7) -/

/-- Section 4.3: `ρ = 9m/(L-m+1)` "is less than 1 since L ≥ 10m". -/
theorem sec4_rho_lt_one (L m : ℕ) (hL : 10 * m ≤ L) : rho L m < 1 := by
  have : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [rho, div_lt_one (by linarith)]
  linarith

/-- The decay rate `ρ` is not negative when `L ≥ 10m`. -/
theorem rho_nonneg {L m : ℕ} (hL : 10 * m ≤ L) : 0 ≤ rho L m := by
  have : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact div_nonneg (by positivity) (by linarith)

/-! ### Theorem 30, "Preprocessing": the count behind (8) -/

/-- The number `√K N₀` of the hypothesis "N ≥ √K N₀" of Theorem 30 and of the last term of (8). -/
noncomputable def sqrtKN0 (L m : ℕ) : ℝ := Real.sqrt (K L m : ℝ) * (N0 L m : ℝ)

/-- `√K N₀` is positive when `m ≤ L`. -/
theorem sqrtKN0_pos {L m : ℕ} (hmL : m ≤ L) : 0 < sqrtKN0 L m := by
  have hK : (0 : ℝ) < (K L m : ℝ) := by exact_mod_cast Nat.choose_pos hmL
  have hN0 : (0 : ℝ) < (N0 L m : ℝ) := by exact_mod_cast N0_pos L m
  exact mul_pos (Real.sqrt_pos.mpr hK) hN0

/-- `(√K N₀)² = K N₀² = M`. -/
theorem sqrtKN0_sq (L m : ℕ) : sqrtKN0 L m ^ 2 = (M L m : ℝ) := by
  rw [sqrtKN0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp [M]

/-- Proof of Theorem 30, "Preprocessing": "we store the K₀² subsets, in O(KL) ≤ O(10^L) operations".
Read as the inequality `K L ≤ 10^L` (constant 1). -/
theorem Theorem30.subsets (L m : ℕ) : K L m * L ≤ 10 ^ L := by
  calc K L m * L ≤ 2 ^ L * 2 ^ L :=
        Nat.mul_le_mul (Nat.choose_le_two_pow L m) Nat.lt_two_pow_self.le
    _ = 4 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 10 ^ L := Nat.pow_le_pow_left (by norm_num) L

/-- `binom(L, r) ≥ L` for `1 ≤ r ≤ L/2`: up to the middle the binomial coefficients increase. -/
lemma le_choose_of_le_half (L : ℕ) : ∀ r, 1 ≤ r → r ≤ L / 2 → L ≤ L.choose r := by
  intro r h1
  induction r, h1 using Nat.le_induction with
  | base => intro _; simp
  | succ r hr ih =>
    intro h
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `K₀ ≥ 3` in the range of Theorem 30, because `K = binom(L, m) ≥ L ≥ 10`. -/
lemma three_le_K0 (L m : ℕ) (hm : 1 ≤ m) (hL : 10 * m ≤ L) : 3 ≤ K0 L m := by
  have hK : L ≤ K L m := le_choose_of_le_half L m hm (by omega)
  exact Nat.le_sqrt.2 (by omega)

/-- The number `b` of row bands, `N/(K₀ N₀)` rounded up, satisfies `b √K N₀ ≤ 2N`. The two bounds of
the paper's proof on the numbers of bands and of tiles rest on this. If `b ≤ 2` it is the hypothesis
`N ≥ √K N₀`. If `b ≥ 3` then `(b - 1) K₀ N₀ < N`, `b ≤ 3(b - 1)/2`, and `√K ≤ K₀ + 1 ≤ 4K₀/3`. -/
theorem Theorem30.numBands_mul_le {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ N) :
    (numBands L m N : ℝ) * sqrtKN0 L m ≤ 2 * (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N0 L m : ℝ) := by exact_mod_cast N0_pos L m
  have hK0 : (3 : ℝ) ≤ (K0 L m : ℝ) := by exact_mod_cast three_le_K0 L m hm hL
  have hsqrt : Real.sqrt (K L m : ℝ) ≤ (K0 L m : ℝ) + 1 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by exact_mod_cast (Nat.lt_succ_sqrt' (K L m)).le⟩
  have hband : 0 < (K0 L m : ℝ) * (N0 L m : ℝ) := by positivity
  -- `b` is `N/(K₀ N₀)` rounded up
  have hceil : (numBands L m N : ℝ) * ((K0 L m : ℝ) * (N0 L m : ℝ))
      ≤ (N : ℝ) + (K0 L m : ℝ) * (N0 L m : ℝ) := by
    have h : numBands L m N * bandSize L m ≤ N + bandSize L m - 1 := Nat.div_mul_le_self _ _
    have : numBands L m N * (K0 L m * N0 L m) ≤ N + K0 L m * N0 L m := by
      unfold bandSize at h
      omega
    exact_mod_cast this
  rcases Nat.lt_or_ge (numBands L m N) 3 with hb | hb
  · have hb' : (numBands L m N : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ hb
    exact (mul_le_mul_of_nonneg_right hb' (sqrtKN0_pos (by omega)).le).trans
      (mul_le_mul_of_nonneg_left hN zero_le_two)
  · have hb' : (3 : ℝ) ≤ (numBands L m N : ℝ) := by exact_mod_cast hb
    have hwide : sqrtKN0 L m ≤ 4 / 3 * ((K0 L m : ℝ) * (N0 L m : ℝ)) := by
      unfold sqrtKN0
      nlinarith [hsqrt, hK0, hN0]
    -- `b √K N₀ ≤ (4b/3) K₀ N₀ ≤ 2 (b - 1) K₀ N₀ ≤ 2N`
    nlinarith [mul_le_mul_of_nonneg_left hwide (by linarith : (0 : ℝ) ≤ (numBands L m N : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (numBands L m N : ℝ) - 3) hband.le, hceil]

/-- Proof of Theorem 30, "Preprocessing": "all row bands and column bands, at most 4N/(√K N₀) of
them". There are `numBands L m N` row bands and as many column bands. Here `N` is the given size,
not the padded one, and the bound comes from `Theorem30.numBands_mul_le`. -/
theorem Theorem30.bands {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ N) :
    (2 * numBands L m N : ℝ) ≤ 4 * (N : ℝ) / sqrtKN0 L m := by
  rw [le_div_iff₀ (sqrtKN0_pos (by omega))]
  linarith [Theorem30.numBands_mul_le hm hL hN]

/-- Proof of Theorem 30, "Preprocessing": "K N₀ D ≤ 7^L". This bounds the number of nonzero entries
of the input array of a band, which is why forming it takes `O(L · 7^L)` operations. -/
theorem Theorem30.K_mul_N0_mul_D_le (L m : ℕ) : K L m * N0 L m * D m ≤ 7 ^ L := by
  -- one summand of the binomial expansion of `(4 + 3)^L`
  calc K L m * N0 L m * D m = L.choose m * 4 ^ m * 3 ^ (L - m) := by unfold K N0 D; ring
    _ ≤ 7 ^ L := Nat.choose_mul_pow_mul_pow_le 4 3 L m

/-- Proof of Theorem 30, "Preprocessing": forming the input array of a band takes "O(L · 7^L)
operations", which is within the "O(10^L) operations" of its encoding ("This is the last term of
(8)"). Read as the inequality `L · 7^L ≤ 2 · 10^L`; the constant 1 fails at `L = 3`. From `L = 3`
on, one more level multiplies the left-hand side by `7(L+1)/L ≤ 10`. -/
theorem Theorem30.form_array : ∀ L : ℕ, L * 7 ^ L ≤ 2 * 10 ^ L
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | L + 4 =>
    calc (L + 4) * 7 ^ (L + 4) = (7 * (L + 4)) * 7 ^ (L + 3) := by ring
      _ ≤ (10 * (L + 3)) * 7 ^ (L + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 * ((L + 3) * 7 ^ (L + 3)) := by ring
      _ ≤ 10 * (2 * 10 ^ (L + 3)) := Nat.mul_le_mul_left _ (Theorem30.form_array (L + 3))
      _ = 2 * 10 ^ (L + 4) := by ring

/-- Proof of Theorem 30, "Preprocessing": "the at most 4N²/M tiles, where M = K N₀² is the number of
output entries of a tile". There are `(numBands L m N)²` tiles. Here `N` is the given size, and the
bound comes from `Theorem30.numBands_mul_le`. -/
theorem Theorem30.tiles {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ N) :
    ((numBands L m N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) ^ 2 / (M L m : ℝ) := by
  have hpos := sqrtKN0_pos (L := L) (m := m) (by omega)
  rw [← sqrtKN0_sq, le_div_iff₀ (pow_pos hpos 2)]
  calc (numBands L m N : ℝ) ^ 2 * sqrtKN0 L m ^ 2
      = ((numBands L m N : ℝ) * sqrtKN0 L m) ^ 2 := (mul_pow _ _ 2).symm
    _ ≤ (2 * (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (Theorem30.numBands_mul_le hm hL hN) 2
    _ = 4 * (N : ℝ) ^ 2 := by ring

/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/

/-- Proof of Theorem 30, "Query". "Given (I, J), we find its tile from the bands of row I and column
J, the subset Q of its block product, and its output string w […]. We then compute (X_Q Y_Q)[w] as
the sum in Lemma 28 […]. By Section 2.4.4, the sum is (XY)[I, J]." Here `a` and `b` are the input
arrays of the row band of `I` and of the column band of `J`, and `lay` is any choice of the indexing
bijections and of the subsets of the block products; it carries `m ≤ L`. (The hypotheses `m ≥ 1`,
`L ≥ 10m` and `N ≥ √K N₀` of Theorem 30 are not needed for correctness.) -/
theorem Theorem30.query {L m N : ℕ} (t : ℕ) (ht : t ≤ m) (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    querySum m t (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J))
        (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Lemma28.Mult_eq_querySum m t ht _ _ _ (card_innerSetO_outStrOfPos lay I J)]
  exact Mult_bandArray_eq_mul lay X Y I J

/-- Proof of Theorem 30, "Query": "for every V ⊆ Q with |V| = m - t and every box of 𝓑_V, we look up
its value in the trie of the tile." It is there: it is a box. -/
theorem Theorem30.lookup {L m t : ℕ} {η : OutStr L} {V : Finset (Fin L)} (hV : V ∈ Vsets m t η)
    {π : Cube L} (hπ : π ∈ BV η V) : π ∈ boxes L m t :=
  mem_boxes.2 (BV_isBox hV hπ)

/-- What the dynamic program of Lemma 29 computes for a box, at the number of stars of the box, is
the value of the box. -/
theorem dpValue_card_starLevels {L m t : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) {π : Cube L}
    (hπ : π ∈ boxes L m t) :
    dpValue (encodingL a) (encodingR b) (Cube.starLevels π).card π = Cube.val a b π :=
  lemma_29_values L m t _ a b π
    (mem_boxesWithStars.2 ⟨mem_boxes.1 hπ, rfl⟩)

/-- A query, as in the proof of Theorem 30, for the output string `η` of the queried position,
reading only the two encodings of the tile and the stored values of its boxes: "for each such leaf τ
we look up its two numbers Φ_τ(a) and Ψ_τ(b) in the encodings of the tile and multiply them. The
second part is the sum of the values of the boxes of w: for every V ⊆ Q with |V| = m - t and every
box of 𝓑_V, we look up its value in the trie of the tile." The value stored for a box `π` with `e`
stars is the one that the dynamic program computed, `dpValue encA encB e π`. -/
def queryValue {L : ℕ} (m t : ℕ) (encA encB : Leaf L → ℤ) (η : OutStr L) : ℤ :=
  ∑ τ ∈ lowLeaves m t η, encA τ * encB τ
    + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, dpValue encA encB (Cube.starLevels π).card π

/-- **Theorem 30**, correctness of the data structure from end to end: the preprocessing computes
the encodings of the bands and, from them, the values of the boxes of every tile by the dynamic
program of Lemma 29; a query for `(I, J)` reads only the two encodings of its tile and the stored
values of boxes, and returns `(XY)[I, J]`. -/
theorem Theorem30.correct {L m N : ℕ} (t : ℕ) (ht : t ≤ m) (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    queryValue m t (encodingL (bandArrayL lay X (bandOf L m I)))
        (encodingR (bandArrayR lay Y (bandOf L m J))) (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Theorem30.query t ht lay X Y I J]
  unfold queryValue querySum
  -- the products at the leaves are read from the encodings, by definition; the stored values of the
  -- boxes are their values, by Lemma 29
  congr 1
  exact sum_congr rfl fun V hV => sum_congr rfl fun π hπ =>
    dpValue_card_starLevels _ _ (Theorem30.lookup hV hπ)

/-! ### Theorem 30, "Word size" -/

/-- Proof of Theorem 30, "Word size": "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}".
Stated after squaring, to stay in the natural numbers. -/
theorem Theorem30.ten_pow_le (L m N : ℕ) (hL : 10 * m ≤ L) (hN : N0 L m ≤ N) :
    (10 ^ L) ^ 2 ≤ N ^ 5 := by
  -- squared once more: `10^{4L} ≤ 3^{9L} ≤ 3^{10(L-m)}`
  have hsq : ((10 ^ L) ^ 2) ^ 2 ≤ ((3 ^ (L - m)) ^ 5) ^ 2 :=
    calc ((10 ^ L) ^ 2) ^ 2 = 10000 ^ L := by
          rw [← pow_mul, ← pow_mul, mul_comm L, pow_mul]; norm_num
      _ ≤ 19683 ^ L := Nat.pow_le_pow_left (by norm_num) L
      _ = 3 ^ (9 * L) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ ((L - m) * 5 * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = ((3 ^ (L - m)) ^ 5) ^ 2 := by rw [pow_mul, pow_mul]
  exact ((Nat.pow_le_pow_iff_left (by norm_num)).mp hsq).trans (Nat.pow_le_pow_left hN 5)




/-! ### Setting up -/

/-- Proof of Corollary 26, "Setting up": for "m := ⌈log_4 D⌉" and `D ≥ 2` the padded inner dimension
satisfies `D ≤ 4^m` and "4^m < 4D", and "the original D was larger than 4^{m-1}". -/
theorem Corollary26.setting_up (D₀ m : ℕ) (hD : 2 ≤ D₀) (hm : m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊) :
    D₀ ≤ D m ∧ D m < 4 * D₀ ∧ 4 ^ (m - 1) < D₀ := by
  obtain rfl : m = Nat.clog 4 D₀ := by
    rw [hm, ← Real.natCeil_logb_natCast]
    norm_num
  have hpos : 1 ≤ Nat.clog 4 D₀ := Nat.clog_pos (by norm_num) hD
  have hlt : 4 ^ (Nat.clog 4 D₀ - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have : 4 ^ Nat.clog 4 D₀ = 4 * 4 ^ (Nat.clog 4 D₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_, hlt⟩
  unfold D
  omega

/-- Proof of Corollary 26, "Setting up": "pad the inner dimension to 4^m < 4D with zero columns of X
and zero rows of Y. This changes no entry of XY". -/
theorem Corollary26.padding {N D₀ : ℕ} (D' : ℕ) (hD : D₀ ≤ D') (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) :
    padInnerCols D' X * padInnerRows D' Y = X * Y := by
  ext I J
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- The sum over the `D'` columns has the `D₀` terms of `XY`, and zeros at the added columns.
  refine (Fintype.sum_of_injective (Fin.castLE hD) (Fin.castLE_injective hD) _ _
    (fun k hk => ?_) fun k => ?_).symm
  · have hk' : ¬ (k : ℕ) < D₀ := fun h => hk ⟨⟨k, h⟩, rfl⟩
    simp only [padInnerCols, dif_neg hk', zero_mul]
  · simp only [padInnerCols, padInnerRows, Fin.val_castLE, k.isLt, dite_true, Fin.eta]

/-- The numbers in which the bounds of Section 4.4 are stated. -/
structure Sizes where
  /-- The given inner dimension, before the padding. -/
  D₀ : ℕ
  /-- The size of the product: the matrices are `N × D₀` and `D₀ × N`. -/
  N : ℕ
  /-- The padded inner dimension is `D = 4^m`. -/
  m : ℕ

/-- Proof of Corollary 26, "Setting up": "m := ⌈log_4 D⌉", for a given inner dimension `D₀ ≥ 2`. -/
structure Sizes.SetUp (p : Sizes) : Prop where
  two_le : 2 ≤ p.D₀
  m_eq : p.m = ⌈Real.logb 4 (p.D₀ : ℝ)⌉₊

/-- The padded inner dimension is at least the given one. -/
theorem Sizes.SetUp.le {p : Sizes} (h : p.SetUp) : p.D₀ ≤ D p.m :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).1

/-- "4^m < 4D". -/
theorem Sizes.SetUp.lt {p : Sizes} (h : p.SetUp) : D p.m < 4 * p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.1

/-- "the original D was larger than 4^{m-1}". -/
theorem Sizes.SetUp.gt {p : Sizes} (h : p.SetUp) : 4 ^ (p.m - 1) < p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.2

/-- `m ≥ 1`, because `2 ≤ D₀ ≤ 4^m`. -/
theorem Sizes.SetUp.m_pos {p : Sizes} (h : p.SetUp) : 1 ≤ p.m :=
  Nat.pos_of_ne_zero fun h0 => by
    have hle := h.le
    have := h.two_le
    rw [h0, D, pow_zero] at hle
    omega

/-- Proof of Corollary 26, "Setting up": padding "changes D by a factor less than 4, which only
affects the constants". A bound `D^a log^k D` in the padded `D = 4^m` is, up to a constant, the same
bound in the original inner dimension `D₀`. (Corollary 26 has `k = 0`; the bounds of Corollary 31
have logarithms.) -/
theorem padded_le (a : ℝ) (k : ℕ) :
    Dominated Sizes.SetUp (fun p => (D p.m : ℝ) ^ a * Real.log (D p.m) ^ k)
      fun p => (p.D₀ : ℝ) ^ a * Real.log p.D₀ ^ k := by
  refine .of_le_const_mul (C := 4 ^ |a| * 3 ^ k) (by positivity) fun ⟨D₀, _, m⟩ h => ?_
  have htwo : (2 : ℝ) ≤ D₀ := by exact_mod_cast h.two_le
  have hD₀ : (0 : ℝ) < D₀ := by linarith
  have : 1 ≤ (D m : ℝ) / D₀ := (one_le_div hD₀).2 (by exact_mod_cast h.le)
  have hle4 : (D m : ℝ) ≤ 4 * D₀ := by exact_mod_cast h.lt.le
  have hpow : (D m : ℝ) ^ a ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
    calc (D m : ℝ) ^ a = ((D m : ℝ) / D₀) ^ a * (D₀ : ℝ) ^ a := by
          rw [← Real.mul_rpow (by positivity) hD₀.le, div_mul_cancel₀ _ hD₀.ne']
      _ ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right
            ((Real.rpow_le_rpow_of_exponent_le this (le_abs_self a)).trans
              (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hD₀).2 hle4) (abs_nonneg a)))
            (by positivity)
  have hlog : Real.log (D m) ≤ 3 * Real.log D₀ :=
    calc Real.log (D m) ≤ Real.log (4 * D₀) := Real.log_le_log (cast_D_pos m) hle4
      _ = 2 * Real.log 2 + Real.log D₀ := by
          rw [Real.log_mul (by norm_num) hD₀.ne', Real.log_four]
      _ ≤ 3 * Real.log D₀ := by linarith [Real.log_le_log two_pos htwo]
  calc (D m : ℝ) ^ a * Real.log (D m) ^ k
      ≤ 4 ^ |a| * (D₀ : ℝ) ^ a * (3 * Real.log D₀) ^ k :=
        mul_le_mul hpow (pow_le_pow_left₀ (by positivity) hlog k) (by positivity) (by positivity)
    _ = 4 ^ |a| * 3 ^ k * ((D₀ : ℝ) ^ a * Real.log D₀ ^ k) := by
        rw [mul_pow]
        ring

/-- The switching order `t = ⌈θm⌉`: "t := ⌈m/9⌉" in the proof of Corollary 26, where `θ = 1/9`, and
"t := ⌈θm⌉" in the proof of Corollary 31. -/
noncomputable def switchOf (θ : ℝ) (m : ℕ) : ℕ := ⌈θ * (m : ℝ)⌉₊

/-- The hypothesis `t ≤ m` of Theorem 30 holds for `t = ⌈θm⌉` with `θ ≤ 1`. -/
theorem switchOf_le {θ : ℝ} (hθ : θ ≤ 1) (m : ℕ) : switchOf θ m ≤ m :=
  Nat.ceil_le.2 (mul_le_of_le_one_left (Nat.cast_nonneg m) hθ)

/-! ### Queries -/

/-- Proof of Corollary 26, "Queries": "A query reads ∑_{d≤t} α_d numbers, and we bound this sum as
in the proof of Lemma 11. Since 9^d = 72^d 8^{-d} ≤ 72^t 8^{-d} for d ≤ t", the sum `∑_{d ≤ t} α_d`
is at most `72^t ∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m`. Here any `x > 0` with `9x ≥ 1`
stands for 8, because the proof of Corollary 31 makes "the same calculation with x := (1-θ)/θ in
place of 8". -/
theorem sum_alpha_le {x : ℝ} (hx : 0 < x) (h9x : 1 ≤ 9 * x) {m t : ℕ} (htm : t ≤ m) :
    ∑ d ∈ range (t + 1), (alpha m d : ℝ) ≤ (9 * x) ^ t * (1 + 1 / x) ^ m := by
  -- `9^d = (9x)^d x^{-d} ≤ (9x)^t x^{-d}` for `d ≤ t`
  have hterm : ∀ d ∈ range (t + 1),
      (alpha m d : ℝ) ≤ (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
    intro d hd
    have hpow : (9 * x) ^ d ≤ (9 * x) ^ t :=
      pow_le_pow_right₀ h9x (by rw [mem_range] at hd; omega)
    calc (alpha m d : ℝ) = (9 * x) ^ d * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
          rw [alpha, one_pow, mul_one, ← mul_assoc, ← mul_pow,
            show 9 * x * (1 / x) = 9 by field_simp]
          push_cast
          ring
      _ ≤ (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by gcongr
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ ∑ d ∈ range (t + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum hterm
    _ ≤ ∑ d ∈ range (m + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          fun _ _ _ => by positivity
    _ = (9 * x) ^ t * (1 + 1 / x) ^ m := by rw [← mul_sum, ← add_pow, add_comm]

/-- `(9x)^{θm} (1+1/x)^m = D^q` for "x := (1-θ)/θ". -/
theorem rpow_mul_pow_eq_D_rpow_qOf {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (m : ℕ) :
    (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ)) * (1 + 1 / ((1 - θ) / θ)) ^ m = (D m : ℝ) ^ qOf θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  have hinv : 1 + 1 / ((1 - θ) / θ) = (1 - θ)⁻¹ := by
    field_simp
    ring
  rw [← exp_entropy_eq_D_rpow_qOf, hinv, Real.rpow_def_of_pos (by positivity),
    ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, Real.log_inv,
    Real.log_mul (by norm_num) (by positivity), Real.log_div h1θ.ne' hθ0.ne', entropy]
  congr 1
  ring

/-! ### Encodings -/

/-! ### Conclusion -/




/-! ### Setting up -/

/-- With "L := ⌈cm⌉" (proof of Corollary 31) the hypothesis `L ≥ 10m` of Theorem 30 holds. -/
theorem ten_mul_le_levelsOf {c : ℝ} (hc : 10 < c) (m : ℕ) : 10 * m ≤ levelsOf c m := by
  have h : ((10 * m : ℕ) : ℝ) ≤ c * m := by
    push_cast
    exact mul_le_mul_of_nonneg_right hc.le (Nat.cast_nonneg m)
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- `L = ⌈cm⌉ ≤ (c + 1) m` for `m ≥ 1`. -/
lemma levelsOf_le {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    (levelsOf c m : ℝ) ≤ (c + 1) * m := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

/-- `m = O(log D)` for `D = 4^m`. -/
lemma dominated_cast_log_D :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => (m : ℝ)) fun m => Real.log (D m) :=
  .of_le fun m _ => cast_le_log_cast_D m

/-- `L = ⌈cm⌉ = O(log D)` for `D = 4^m`. -/
lemma dominated_levelsOf_log_D {c : ℝ} (hc : 10 < c) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => (levelsOf c m : ℝ)) fun m => Real.log (D m) :=
  (Dominated.of_le_const_mul (C := c + 1) (by linarith) fun _ hm => levelsOf_le hc hm).trans
    dominated_cast_log_D

/-- Proof of Corollary 31: "After the padding, the assumption D ≤ N^ε now reads N ≥ 4^{(m-1)/ε}",
because `4^{m-1} < D ≤ N^ε` for the original `D`. -/
theorem Corollary31.hypothesis {m D₀ N : ℕ} {ε : ℝ} (hm : 1 ≤ m) (hε : 0 < ε)
    (hgt : 4 ^ (m - 1) < D₀) (hthin : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    (4 : ℝ) ^ (((m : ℝ) - 1) / ε) ≤ (N : ℝ) := by
  have hle : (4 : ℝ) ^ ((m : ℝ) - 1) ≤ (N : ℝ) ^ ε := by
    rw [← Nat.cast_one, ← Nat.cast_sub hm, Real.rpow_natCast]
    exact le_trans (by exact_mod_cast hgt.le) hthin
  calc (4 : ℝ) ^ (((m : ℝ) - 1) / ε) = ((4 : ℝ) ^ ((m : ℝ) - 1)) ^ (1 / ε) := by
        rw [← Real.rpow_mul (by norm_num), mul_one_div]
    _ ≤ ((N : ℝ) ^ ε) ^ (1 / ε) := Real.rpow_le_rpow (by positivity) hle (by positivity)
    _ = (N : ℝ) := by
        rw [← Real.rpow_mul N.cast_nonneg, mul_one_div_cancel hε.ne', Real.rpow_one]

/-! ### Boxes -/

/-- Proof of Corollary 31: "ρ < ρ_c", where `ρ = 9m/(L-m+1)` and `L = ⌈cm⌉ ≥ cm`. -/
theorem Corollary31.rho_lt {c : ℝ} (hc : 10 < c) (m : ℕ) : rho (levelsOf c m) m < rhoC c := by
  have : c * m ≤ levelsOf c m := Nat.le_ceil _
  have : (m : ℝ) ≤ c * m := le_mul_of_one_le_left (Nat.cast_nonneg m) (by linarith)
  unfold rho rhoC
  -- after clearing denominators: `9m (c - 1) < 9 (L - m + 1)`, from `cm ≤ L`
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

/-! ### Queries -/

/-- Proof of Corollary 31: "the same calculation with x := (1-θ)/θ in place of 8, where 9x > 1
because θ < 0.9, gives ∑_{d≤t} α_d ≤ (9x)^t (1+1/x)^m = O(D^q)". The constant is `9x`, because
`t = ⌈θm⌉ < θm + 1`. -/
theorem Corollary31.sum_alpha {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => ∑ d ∈ range (switchOf θ m + 1), (alpha m d : ℝ))
      fun m => (D m : ℝ) ^ qOf θ := by
  have hx : 0 < (1 - θ) / θ := div_pos (by linarith) hθ0
  have h9x : 1 < 9 * ((1 - θ) / θ) := by
    rw [← mul_div_assoc, lt_div_iff₀ hθ0]
    linarith
  refine .of_le_const_mul (C := 9 * ((1 - θ) / θ)) (by positivity) fun m _ => ?_
  have ht : ((switchOf θ m : ℕ) : ℝ) ≤ θ * m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  calc ∑ d ∈ range (switchOf θ m + 1), (alpha m d : ℝ)
      ≤ (9 * ((1 - θ) / θ)) ^ switchOf θ m * (1 + 1 / ((1 - θ) / θ)) ^ m :=
        sum_alpha_le hx h9x.le (switchOf_le (by linarith) m)
    _ ≤ (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ) + 1) * (1 + 1 / ((1 - θ) / θ)) ^ m := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h9x.le ht
    _ = 9 * ((1 - θ) / θ) * (D m : ℝ) ^ qOf θ := by
        rw [← rpow_mul_pow_eq_D_rpow_qOf hθ0 (by linarith) m, Real.rpow_add (by positivity),
          Real.rpow_one]
        ring

/-- The query cost `L ∑_{d ≤ t} α_d` of Theorem 30 is `O(L D^q) = O(D^q log D)`, for `D = 4^m`. (In
the proof of Corollary 26: "Hence a query takes O(L D^q) = O(m D^q) time".) -/
theorem Corollary31.query_cost {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => costQuery (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ qOf θ * Real.log (D m) :=
  ((dominated_levelsOf_log_D hc).mul (Corollary31.sum_alpha hθ0 hθ1) (fun _ _ => by positivity)
    fun _ _ => by positivity).congr (fun _ _ => rfl) fun m _ => by ring

/-! ### Encodings

As in the proof of Corollary 26, `m`-th powers are compared by comparing their bases. The paper's
sentences are one lemma each: the bound on the binomial coefficient (`Corollary31.le_K`, for which
`Corollary31.mul_entropy_monotoneOn` passes from `L` to `cm`), the bound `O(√m · Λ^m)` on the
left-hand side (`Corollary31.lhs10_le`), where `Λ` is `Real.exp (lnΛ c γ)` (`exp_lnΛ`), and
`Λ < 4^{1/ε}` (`eq_11_iff`); `eq_10` puts them together with `Corollary31.hypothesis`. Throughout,
`L = ⌈cm⌉`, and `D₀` is the inner dimension before padding. -/

/-! ### The corollary -/

/-- The instances of Corollary 31 from a threshold `m₀` on: `2 ≤ D ≤ N^ε` and `m = ⌈log_4 D⌉ ≥ m₀`.
-/
structure Sizes.Corollary31 (ε : ℝ) (m₀ : ℕ) (p : Sizes) : Prop where
  setUp : p.SetUp
  thin : (p.D₀ : ℝ) ≤ (p.N : ℝ) ^ ε
  large : m₀ ≤ p.m

end ThreeSumApsp
