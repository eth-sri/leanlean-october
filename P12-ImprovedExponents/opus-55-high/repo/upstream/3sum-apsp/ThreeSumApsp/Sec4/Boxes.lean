/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec2.Lemma9
import ThreeSumApsp.Sec2.Orders
import ThreeSumApsp.Util.Choose

/-!
# Cubes and boxes (Section 4.2)

A cube is a string of `L` symbols, each of them one of the ten terms or a star, and its leaves are
obtained by replacing each star by any term. A box is a cube with at most `m - t` symbols `P₀` or
stars whose stars are all below its symbols `P₀`. This file proves what the paper says about cubes
and boxes before it turns to the boxes of one output string, in this order:

* from "Notions from Section 2": `M ≤ 10^L` (`M_le_ten_pow`);
* a cube with `e` stars has `10^e` leaves (`Cube.card_leaves`);
* the leaves, the stars and the symbols `P₀` of three cubes: a leaf read as a cube (`Cube.ofLeaf`),
  a cube with a star replaced by a term (`Cube.replace`), and a leaf with stars put at a set of
  levels (`Cube.starAt`); every cube that Section 4.2 makes from a leaf is of this third form;
* the leaves contributing to an output string `η` (w in the paper) are the leaves of the cube of `η`
  (`mem_leaves_cubeOf`), so the entry `(X_Q Y_Q)[η]` is the value of that cube
  (`mul_apply_eq_val_cubeOf`); Section 4.2 starts from this remark, and nothing else rests on it;
* the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has `P₀`
  or a star (`P0Levels_starsToP0`);
* a box only contains leaves of order at least `t` (`le_order_of_mem_leaves`);
* the `k` lowest levels of a set `S` lie below the other levels of `S` (`lowest_lt`), this property
  characterizes them (`eq_lowest_of_lt`), and there are `min k |S|` of them (`card_lowest`);
* a box is a leaf with its lowest symbols `P₀` replaced by stars (`eq_starLowest_starsToP0`), and
  every cube obtained in this way from a leaf with at most `m - t` symbols `P₀` is a box
  (`isBox_starLowest`).
-/


open Finset

namespace ThreeSumApsp

variable {L : ℕ}

variable {π : Cube L} {τ : Leaf L}

/-! ### Cubes and their leaves (Section 4.2) -/

/-- Membership in the set of leaves of a cube, level by level. -/
@[simp]
theorem Cube.mem_leaves :
    τ ∈ Cube.leaves π ↔ ∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ) := by
  simp [Cube.leaves, mem_filter, mem_univ, true_and]
  rfl

variable {ℓ : Fin L}

/-- Where a cube has a term, its leaves have that term. -/
theorem Cube.eq_of_mem_leaves (hτ : τ ∈ Cube.leaves π)
    {lam : Term} (h : π ℓ = CubeSymbol.term lam) : τ ℓ = lam := by
  simpa [h, eq_comm] using Cube.mem_leaves.1 hτ ℓ

/-- Membership in the set of star levels of a cube. -/
@[simp]
theorem Cube.mem_starLevels :
    ℓ ∈ Cube.starLevels π ↔ π ℓ = CubeSymbol.star := by
  simp [Cube.starLevels]

/-- Membership in the set of levels at which a cube has `P₀`. -/
@[simp]
theorem Cube.mem_P0Levels :
    ℓ ∈ Cube.P0Levels π ↔ π ℓ = CubeSymbol.term Term.P0 := by
  simp [Cube.P0Levels]

/-- No level of a cube has both a star and `P₀`. -/
theorem Cube.disjoint_starLevels_P0Levels (π : Cube L) :
    Disjoint (Cube.starLevels π) (Cube.P0Levels π) := by
  simp_all [disjoint_left]

/-- The terms that a leaf of a cube may have at a level with the given symbol. -/
def symbolTerms : CubeSymbol → Finset Term
  | .term lam => {lam}
  | .star => univ

/-- The leaves of a cube form a product set: the choices at the levels are independent. -/
lemma leaves_eq_piFinset (π : Cube L) :
    Cube.leaves π = Fintype.piFinset fun ℓ => symbolTerms (π ℓ) := by
  ext τ
  rw [Cube.mem_leaves, Fintype.mem_piFinset]
  refine forall_congr' fun ℓ => ?_
  cases h : π ℓ <;> simp [symbolTerms, eq_comm]

/-- Section 4.2: "a cube with e stars has 10^e leaves". -/
theorem Cube.card_leaves (π : Cube L) :
    (Cube.leaves π).card = 10 ^ (Cube.starLevels π).card := by
  have hcard : ∀ ℓ, (symbolTerms (π ℓ)).card = if ℓ ∈ π.starLevels then 10 else 1 := by
    intro ℓ
    cases h : π ℓ <;> simp [symbolTerms, h, card_term]
  rw [leaves_eq_piFinset, Fintype.card_piFinset]
  simp only [hcard]
  rw [prod_ite_mem_const, one_pow, mul_one]

/-! ### A leaf as a cube without stars (Section 4.2) -/

/-- Section 4.2: "a cube without stars is a single leaf"; this is the cube without stars whose
single leaf is `τ`. -/
def Cube.ofLeaf (τ : Leaf L) : Cube L := fun ℓ => CubeSymbol.term (τ ℓ)

/-- The only leaf of the cube without stars made from `τ` is `τ`. -/
@[simp]
theorem Cube.leaves_ofLeaf (τ : Leaf L) : Cube.leaves (Cube.ofLeaf τ) = {τ} := by
  ext σ
  simp [Cube.ofLeaf, funext_iff, eq_comm]

/-- The cube made from a leaf has no stars. -/
@[simp]
theorem Cube.starLevels_ofLeaf (τ : Leaf L) : Cube.starLevels (Cube.ofLeaf τ) = ∅ := by
  ext ℓ
  simp [Cube.ofLeaf]

/-- The cube made from a leaf has `P₀` where the leaf chooses `P₀`. -/
@[simp]
theorem Cube.P0Levels_ofLeaf (τ : Leaf L) :
    Cube.P0Levels (Cube.ofLeaf τ) = ThreeSumApsp.P0Levels τ := by
  ext ℓ
  simp [Cube.ofLeaf]

/-! ### Replacing a star by a term (proof of Lemma 29) -/

/-- The leaves of `π[ℓ ← λ]`, for a star of `π` at level `ℓ`, are the leaves of `π` that choose `λ`
at level `ℓ`. -/
theorem Cube.mem_leaves_replace (hℓ : π ℓ = CubeSymbol.star)
    (lam : Term) (τ : Leaf L) :
    τ ∈ Cube.leaves (Cube.replace π ℓ lam) ↔ τ ∈ Cube.leaves π ∧ τ ℓ = lam := by
  rw [Cube.mem_leaves, Cube.mem_leaves, Cube.replace]
  grind

/-- Replacing a star by a term removes its level from the star levels. -/
theorem Cube.starLevels_replace (π : Cube L) (ℓ : Fin L) (lam : Term) :
    Cube.starLevels (Cube.replace π ℓ lam) = (Cube.starLevels π).erase ℓ := by
  ext k
  by_cases hk : k = ℓ <;> simp [Cube.replace, hk]

/-- After a star is replaced by a term, the symbols `P₀` are at the old levels and possibly at the
level of that star. -/
theorem Cube.P0Levels_replace_subset (π : Cube L) (ℓ : Fin L) (lam : Term) :
    Cube.P0Levels (Cube.replace π ℓ lam) ⊆ insert ℓ (Cube.P0Levels π) := by
  intro k hk
  by_cases hkl : k = ℓ
  · simp_all
  simp_all [Cube.replace]

/-! ### Putting stars into a leaf (Section 4.2) -/

/-- The cube that agrees with the leaf `τ` except for stars at the levels of `F`. -/
def Cube.starAt (F : Finset (Fin L)) (τ : Leaf L) : Cube L :=
  fun ℓ => if ℓ ∈ F then CubeSymbol.star else CubeSymbol.term (τ ℓ)

/-- `τ` is a leaf of the cube obtained from `τ` by putting stars at some levels. -/
theorem Cube.mem_leaves_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    τ ∈ Cube.leaves (Cube.starAt F τ) :=
  Cube.mem_leaves.2 fun ℓ => (em (ℓ ∈ F)).imp (if_pos ·) (if_neg ·)

/-- The stars of `Cube.starAt F τ` are at the levels of `F`. -/
@[simp]
theorem Cube.starLevels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    Cube.starLevels (Cube.starAt F τ) = F := by
  ext ℓ
  simp_all [Cube.starAt]

/-- The symbols `P₀` of `Cube.starAt F τ` are at the levels outside `F` at which `τ` chooses `P₀`.
-/
@[simp]
theorem Cube.P0Levels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    Cube.P0Levels (Cube.starAt F τ) = ThreeSumApsp.P0Levels τ \ F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- If `τ` chooses `P₀` at the levels of `F`, then replacing the stars of `Cube.starAt F τ` with
`P₀` gives back `τ`. -/
theorem Cube.starsToP0_starAt {F : Finset (Fin L)}
    (h : F ⊆ ThreeSumApsp.P0Levels τ) :
    Cube.starsToP0 (Cube.starAt F τ) = τ := by
  grind [Cube.starsToP0, Cube.starAt, ThreeSumApsp.mem_P0Levels]

/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/

/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/

/-- A cube is the leaf obtained by replacing its stars with `P₀`, with stars at the star levels of
the cube. -/
theorem Cube.starAt_starLevels_starsToP0 (π : Cube L) :
    Cube.starAt (Cube.starLevels π) (Cube.starsToP0 π) = π := by
  unfold Cube.starAt Cube.starsToP0
  aesop

/-- Section 4.2: "a cube without stars is a single leaf", namely the leaf `Cube.starsToP0 π`. -/
theorem Cube.eq_ofLeaf_of_starLevels_eq_empty (π : Cube L) (hπ : Cube.starLevels π = ∅) :
    π = Cube.ofLeaf (Cube.starsToP0 π) := by
  conv_lhs => rw [← π.starAt_starLevels_starsToP0, hπ]
  rfl

/-- The leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has a
star or `P₀`. -/
theorem P0Levels_starsToP0 (π : Cube L) :
    P0Levels (Cube.starsToP0 π) = Cube.starLevels π ∪ Cube.P0Levels π := by
  grind [mem_P0Levels, Cube.mem_starLevels, Cube.mem_P0Levels, Cube.starsToP0]

/-- Proof of Lemma 29: the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` at
as many levels as the cube has symbols `P₀` or stars. -/
theorem card_P0Levels_starsToP0 (π : Cube L) :
    (P0Levels (Cube.starsToP0 π)).card = (Cube.starLevels π).card + (Cube.P0Levels π).card := by
  grind [P0Levels_starsToP0, card_union_of_disjoint, Cube.disjoint_starLevels_P0Levels]

variable {m t : ℕ}

/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/

/-- Section 4.2: "the leaves of order at least t, i.e., the leaves that choose P₀ at most m - t
times". -/
theorem le_order_iff (ht : t ≤ m) (τ : Leaf L) :
    (t : ℤ) ≤ order m τ ↔ (P0Levels τ).card ≤ m - t := by
  unfold order
  omega

/-- Section 4.2: "A leaf of π chooses P₀ at the f - e levels where π has P₀ and possibly at some of
its e star levels", and nowhere else. -/
theorem P0Levels_subset_of_mem_leaves (hτ : τ ∈ Cube.leaves π) :
    P0Levels τ ⊆ Cube.P0Levels π ∪ Cube.starLevels π := by
  grind [mem_P0Levels, Cube.mem_P0Levels, Cube.mem_starLevels, Cube.mem_leaves]

/-- Section 4.2: "so a box only contains leaves of order at least t". -/
theorem le_order_of_mem_leaves (ht : t ≤ m) (hπ : IsBox m t π)
    (hτ : τ ∈ Cube.leaves π) : (t : ℤ) ≤ order m τ := by
  rw [le_order_iff ht]
  calc (P0Levels τ).card ≤ (Cube.P0Levels π ∪ Cube.starLevels π).card :=
        card_le_card (P0Levels_subset_of_mem_leaves hτ)
    _ ≤ (Cube.P0Levels π).card + (Cube.starLevels π).card := by grind
    _ ≤ m - t := (add_comm _ _).trans_le hπ.1

/-! ### The `k` lowest levels of a set (Section 4.2) -/

/-- The `k` lowest levels of `S` are levels of `S`. -/
theorem lowest_subset (k : ℕ) (S : Finset (Fin L)) : lowest k S ⊆ S :=
  filter_subset _ _

variable {k : ℕ} {S : Finset (Fin L)}

/-- Membership in the set of the `k` lowest levels of `S`. -/
lemma mem_lowest :
    ℓ ∈ lowest k S ↔ ℓ ∈ S ∧ (S.filter fun ℓ' => ℓ' < ℓ).card < k := by
  simp [lowest]

/-- The number of levels of `S` below a level of `S` grows strictly with the level. -/
lemma card_below_strictMonoOn (S : Finset (Fin L)) :
    StrictMonoOn (fun ℓ => (S.filter fun x => x < ℓ).card) S := by
  intro ℓ hℓ ℓ' _ hlt
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · grind
  · exact lt_irrefl ℓ (mem_filter.1 (hsub (by simp_all))).2

/-- Each of the `k` lowest levels of `S` is below every other level of `S`. -/
theorem lowest_lt {ℓ' : Fin L} (hℓ : ℓ ∈ lowest k S)
    (hℓ' : ℓ' ∈ S \ lowest k S) : ℓ < ℓ' := by
  obtain ⟨hS, hbelow⟩ := mem_lowest.1 hℓ
  obtain ⟨hS', hnot⟩ := mem_sdiff.1 hℓ'
  -- otherwise `ℓ' ≤ ℓ` would have at most as many levels of `S` below it as `ℓ`, fewer than `k`
  by_contra hlt
  exact hnot (mem_lowest.2
    ⟨hS', ((card_below_strictMonoOn S).monotoneOn hS' hS (not_lt.1 hlt)).trans_lt hbelow⟩)

/-- A subset `T` of `S` all of whose levels are below all the other levels of `S` consists of the
`|T|` lowest levels of `S`. -/
theorem eq_lowest_of_lt {T : Finset (Fin L)} (hT : T ⊆ S)
    (h : ∀ ℓ ∈ T, ∀ ℓ' ∈ S \ T, ℓ < ℓ') : T = lowest T.card S := by
  ext ℓ
  rw [mem_lowest]
  constructor
  · -- The levels of `S` below a level `ℓ` of `T` are levels of `T` other than `ℓ`.
    refine fun hℓ => ⟨hT hℓ, card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩⟩
    · grind [lt_asymm]
    grind
  · -- All of `T` is below a level of `S` outside `T`.
    rintro ⟨hℓS, hcard⟩
    by_contra hℓT
    refine absurd (card_le_card fun x hx => ?_) (not_le.2 hcard)
    grind

/-- The numbers of levels of `S` below the levels of `S` are `0, …, |S| - 1`. -/
lemma image_card_below (S : Finset (Fin L)) :
    (S.image fun ℓ => (S.filter fun x => x < ℓ).card) = range S.card := by
  refine eq_of_subset_of_card_le (fun n hn => ?_) ?_
  · grind [card_lt_card]
  · rw [card_image_of_injOn (card_below_strictMonoOn S).injOn, card_range]

/-- The set of the `k` lowest levels of `S` has `min k |S|` elements. -/
theorem card_lowest (k : ℕ) (S : Finset (Fin L)) : (lowest k S).card = min k S.card := by
  -- The map from a level to the number of levels of `S` below it is injective on `S`, its image is
  -- `{0, …, |S| - 1}`, and by definition `lowest k S` is the preimage of the numbers below `k`.
  have hrange : (range S.card).filter fun n => n < k = range (min k S.card) := by
    grind
  rw [← card_image_of_injOn ((card_below_strictMonoOn S).injOn.mono (coe_subset.2 (lowest_subset k S))), ← card_range (min k S.card), ← hrange, ← image_card_below,
    filter_image]
  rfl

/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/

/-- Section 4.2: the cube "obtained from a leaf […] by replacing its e lowest symbols P₀ […] by
stars". -/
def starLowest (e : ℕ) (τ : Leaf L) : Cube L := Cube.starAt (lowest e (P0Levels τ)) τ

variable (e : ℕ)

/-- The stars of `starLowest e τ` are at the `e` lowest levels at which `τ` chooses `P₀`. -/
theorem starLevels_starLowest (τ : Leaf L) :
    Cube.starLevels (starLowest e τ) = lowest e (P0Levels τ) :=
  Cube.starLevels_starAt _ τ

/-- The symbols `P₀` of `starLowest e τ` are at the other levels at which `τ` chooses `P₀`. -/
theorem P0Levels_starLowest (τ : Leaf L) :
    Cube.P0Levels (starLowest e τ) = P0Levels τ \ lowest e (P0Levels τ) :=
  Cube.P0Levels_starAt _ τ

/-- Replacing the stars of `starLowest e τ` with `P₀` gives back `τ`. -/
theorem starsToP0_starLowest (τ : Leaf L) : Cube.starsToP0 (starLowest e τ) = τ :=
  Cube.starsToP0_starAt (lowest_subset _ _)

/-- Section 4.2: "By (ii), a box is obtained from a leaf of order at least t by replacing its e
lowest symbols P₀ (rather than an arbitrary subset of them) by stars." The leaf is
`Cube.starsToP0 π`, and only condition (ii) is used. -/
theorem eq_starLowest_starsToP0 (π : Cube L)
    (h : ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ') :
    π = starLowest (Cube.starLevels π).card (Cube.starsToP0 π) := by
  grind [Cube.starLevels, lowest, P0Levels, Cube.starsToP0, eq_lowest_of_lt, P0Levels_starsToP0, starLowest, Cube.starAt_starLevels_starsToP0]

/-- The converse: replacing the `e` lowest symbols `P₀` of a leaf with at most `m - t` symbols `P₀`
by stars gives a box. -/
theorem isBox_starLowest (m t e : ℕ) (τ : Leaf L) (hτ : (P0Levels τ).card ≤ m - t) :
    IsBox m t (starLowest e τ) := by
  grind [IsBox, card_P0Levels_starsToP0, starsToP0_starLowest, starLevels_starLowest, P0Levels_starLowest, lowest_lt]
