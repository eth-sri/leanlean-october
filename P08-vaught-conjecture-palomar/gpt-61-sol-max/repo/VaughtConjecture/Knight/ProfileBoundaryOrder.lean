/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ProfileFaceGluing
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort

/-! # Simultaneous ordering of arbitrary finite face inventories

Two increasing embeddings of a common finite inventory admit a common
ordered union. Shared occurrences are identified exactly once, private
occurrences remain distinct, and both entire old orders are preserved.
No inventory size or initial prefix is fixed.
-/

namespace VaughtConjecture.Knight.ProfileBoundaryOrder

open ProfileFaceUnion

variable {c n m : ℕ}

def rank (f : Fin c ↪ Fin n) (x : Fin n) :=
  (Finset.univ.filter (fun i => f i ≤ x)).card

theorem rank_mono (f : Fin c ↪ Fin n) : Monotone (rank f) := by
  intro x y hxy
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp hi).2.trans hxy⟩

theorem rank_lt_at_shared (f : Fin c ↪ Fin n) {x y : Fin n}
    (hxy : x < y) (hy : y ∈ Set.range f) : rank f x < rank f y := by
  obtain ⟨i, rfl⟩ := hy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · grind
  · intro he
    have hi : i ∈ Finset.univ.filter (fun j => f j ≤ f i) := by simp
    rw [← he] at hi
    exact (not_le_of_gt hxy) (Finset.mem_filter.mp hi).2

theorem rank_shared (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (i : Fin c) :
    rank f (f i) = rank g (g i) := by
  unfold rank
  congr 1
  ext j
  simp  [   hf.le_iff_le, hg.le_iff_le]

noncomputable def faceKey (f : Fin c ↪ Fin n) (tag : ℕ) (x : Fin n) :=  toLex (rank f x, if x ∈ Set.range f then 0 else tag + x.val)

theorem faceKey_strict (f : Fin c ↪ Fin n) {tag : ℕ} (htag : 0 < tag) :
    StrictMono (faceKey f tag) := by
  
  intro x y hxy
  change toLex (_, _) < toLex (_, _)
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hr : rank f x < rank f y
  · exact Or.inl hr
  · have he : rank f x = rank f y := le_antisymm (rank_mono f hxy.le) (le_of_not_gt hr)
    refine Or.inr ⟨he, ?_⟩
    have hy  := fun hy => hr (rank_lt_at_shared f hxy hy)
    rw [ite_eq_right hy]
    by_cases hx : x ∈ Set.range f
    · rw [ite_eq_left hx]
      omega
    · simp_all

theorem faceKey_shared (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (i : Fin c) :
    faceKey f 1 (f i) = faceKey g (n + 1) (g i) := by grind [faceKey, rank_shared]

theorem faceKey_overlap (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (x : Fin n) (y : Fin m) :
    faceKey f 1 x = faceKey g (n + 1) y ↔ ∃ i, f i = x ∧ g i = y := by
  
  constructor
  · intro h
    have ho := congrArg (fun k => (ofLex k).2) h
    change (if x ∈ Set.range f then 0 else 1 + x.val) =
      (if y ∈ Set.range g then 0 else n + 1 + y.val) at ho
    by_cases hx : x ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hx
      have he := (faceKey_shared f g hf hg i).symm.trans h
      exact ⟨i, rfl, (faceKey_strict g (by omega : 0 < n + 1)).injective he⟩
    · grind
  · aesop (add safe apply [faceKey_shared])

noncomputable def key (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) :=
  ProfileFaceUnion.paste g (faceKey f 1) (faceKey g (n + 1))

theorem key_right (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) (y : Fin m) :
    key f g (right f g y) = faceKey g (n + 1) y :=
  paste_right (faceKey_shared f g hf hg) y

theorem key_injective (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) : Function.Injective (key f g) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl ((faceKey_strict f (by decide)).injective h)
  · obtain ⟨i, _, hi⟩ := (faceKey_overlap f g hf hg x y.val).mp h
    exact False.elim (y.property ⟨i, hi⟩)
  · obtain ⟨i, _, hi⟩ := (faceKey_overlap f g hf hg y x.val).mp h.symm
    exact False.elim (x.property ⟨i, hi⟩)
  · exact congrArg Sum.inr (Subtype.ext
      ((faceKey_strict g (by omega)).injective h))

noncomputable instance (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) :
    Fintype (Set.range (key f g)) := Fintype.ofFinite _

noncomputable def keyEquiv (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) :=
  Equiv.ofInjective (key f g) (key_injective f g hf hg)

noncomputable def enumeration {f : Fin c ↪ Fin n} {g : Fin c ↪ Fin m}
    (hf : StrictMono f) (hg : StrictMono g) :=
  (keyEquiv f g hf hg).trans
    (Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.toEquiv

theorem enumeration_left {f : Fin c ↪ Fin n} {g : Fin c ↪ Fin m}
    {hf : StrictMono f} {hg : StrictMono g} :
    StrictMono (fun x => enumeration hf hg (left x)) := by
  intro x y hxy
  apply (Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.strictMono
  exact faceKey_strict f (by decide) hxy

theorem enumeration_right {f : Fin c ↪ Fin n} {g : Fin c ↪ Fin m}
    {hf : StrictMono f} {hg : StrictMono g} :
    StrictMono (fun y => enumeration hf hg (right f g y)) := by
  intro x y hxy
  apply (Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.strictMono
  change key f g (right f g x) < key f g (right f g y)
  rw [key_right f g hf hg, key_right f g hf hg]
  exact faceKey_strict g (by omega) hxy

