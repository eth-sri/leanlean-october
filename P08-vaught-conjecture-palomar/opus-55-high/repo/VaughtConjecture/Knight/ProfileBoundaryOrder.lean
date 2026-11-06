/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProfileFaceGluing
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Finset.Sort

/-! # Simultaneous ordering of arbitrary finite face inventories

Two increasing embeddings of a common finite inventory admit a common
ordered union. Shared occurrences are identified exactly once, private
occurrences remain distinct, and both entire old orders are preserved.
No inventory size or initial prefix is fixed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ProfileBoundaryOrder

open ProfileFaceUnion

variable {c n m : ℕ}

def rank (f : Fin c ↪ Fin n) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => f i ≤ x)).card

section
variable (f : Fin c ↪ Fin n)

theorem rank_mono  : Monotone (rank f) := by
  intro x y hxy
  apply Finset.card_le_card
  grind

theorem rank_lt_at_shared {x y : Fin n}
    (hxy : x < y) (hy : y ∈ Set.range f) : rank f x < rank f y := by
  obtain ⟨i, rfl⟩ := hy
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · grind
  · intro he
    have hi : i ∈ Finset.univ.filter (fun j => f j ≤ f i) := by simp
    grind

theorem rank_shared (g : Fin c ↪ Fin m)
    (hf : StrictMono f) (hg : StrictMono g) i :
    rank f (f i) = rank g (g i) := by
  unfold rank
  congr 1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf.le_iff_le, hg.le_iff_le]

end

noncomputable def faceKey (f : Fin c ↪ Fin n) (tag : ℕ) (x : Fin n) : ℕ ×ₗ ℕ := by
  classical
  exact toLex (rank f x, if x ∈ Set.range f then 0 else tag + x.val)

section
variable (f : Fin c ↪ Fin n)

theorem faceKey_strict {tag : ℕ} (htag : 0 < tag) :
    StrictMono (faceKey f tag) := by
  classical
  intro x y hxy
  change toLex (_, _) < toLex (_, _)
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hr : rank f x < rank f y
  · exact Or.inl hr
  · have he : rank f x = rank f y := le_antisymm (rank_mono f hxy.le) (le_of_not_gt hr)
    refine Or.inr ⟨he, ?_⟩
    have hy : y ∉ Set.range f := fun hy => hr (rank_lt_at_shared f hxy hy)
    grind

section
variable (g : Fin c ↪ Fin m)

theorem faceKey_shared (hf : StrictMono f) (hg : StrictMono g) (i : Fin c) :
    faceKey f 1 (f i) = faceKey g (n + 1) (g i) := by
  simp only [faceKey, Set.mem_range_self, ite_true, rank_shared f g hf hg i]

theorem faceKey_overlap (hf : StrictMono f) (hg : StrictMono g) (x : Fin n) y :
    faceKey f 1 x = faceKey g (n + 1) y ↔ ∃ i, f i = x ∧ g i = y := by
  classical
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
  · rintro ⟨i, rfl, rfl⟩
    exact faceKey_shared f g hf hg i

end

end

noncomputable def key (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) :
    Carrier (X := Fin n) g → ℕ ×ₗ ℕ :=
  ProfileFaceUnion.paste g (faceKey f 1) (faceKey g (n + 1))

section
variable (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m)

theorem key_right (hf : StrictMono f) (hg : StrictMono g) (y : Fin m) :
    key f g (right f g y) = faceKey g (n + 1) y :=
  paste_right f g (faceKey_shared f g hf hg) y

theorem key_injective (hf : StrictMono f) (hg : StrictMono g) : Function.Injective (key f g) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl ((faceKey_strict f (by grind)).injective h)
  · obtain ⟨i, _, hi⟩ := (faceKey_overlap f g hf hg x y.val).mp h
    exact False.elim (y.property ⟨i, hi⟩)
  · obtain ⟨i, _, hi⟩ := (faceKey_overlap f g hf hg y x.val).mp h.symm
    exact False.elim (x.property ⟨i, hi⟩)
  · exact congrArg Sum.inr (Subtype.ext
      ((faceKey_strict g (by grind)).injective h))

end

noncomputable instance (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) :
    Fintype (Set.range (key f g)) := Fintype.ofFinite _

section
variable (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) (hf : StrictMono f) (hg : StrictMono g)

noncomputable def keyEquiv  :
    Carrier (X := Fin n) g ≃ Set.range (key f g) :=
  Equiv.ofInjective (key f g) (key_injective f g hf hg)

noncomputable def enumeration  :
    Carrier (X := Fin n) g ≃ Fin (Fintype.card (Carrier (X := Fin n) g)) :=
  (keyEquiv f g hf hg).trans
    (Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.toEquiv

end

section
variable (f : Fin c ↪ Fin n) (g : Fin c ↪ Fin m) (hf : StrictMono f) (hg : StrictMono g)

theorem enumeration_left  :
    StrictMono (fun x => enumeration f g hf hg (left g x)) := by
  intro x y hxy
  apply (Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.strictMono
  exact faceKey_strict f (by grind) hxy

theorem enumeration_right  :
    StrictMono (fun y => enumeration f g hf hg (right f g y)) := by
  intro x y hxy
  apply (Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (keyEquiv f g hf hg)).symm).symm.strictMono
  change key f g (right f g x) < key f g (right f g y)
  rw [key_right f g hf hg, key_right f g hf hg]
  exact faceKey_strict g (by grind) hxy

end

end VaughtConjecture.Knight.ProfileBoundaryOrder
