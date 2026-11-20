/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CountedRecoding

/-! # Agreement caps: the meet of two capped labellings in a coded alphabet

The full-scope families of the one-reference tower are labellings of a lower set together with a
cap; two members read one another at the **largest cap below which they agree**.  This module
supplies the value-level algebra:

* the **coded alphabet** `alph l I` at grade `l` with block bound `I` — `⊥` and the ordinals
  `ω·i + j` with `i < I`, `j ≤ l + 1` — a finite set of coded labels (`isCodedLabel_of_mem_alph`);
* **rounding down** `roundDown l I x`: the largest self-visible alphabet value below `x`; it is
  monotone, fixes self-visible alphabet values, and commutes with capping by a self-visible
  alphabet value (`roundDown_min_right`);
* the **agreement cap** `agreeCap F G` of two labellings of a finite index type: the largest `e`
  with `min (F z) e = min (G z) e` for every `z` (`le_agreeCap_iff`), `⊤` when `F = G`;
* the **ultrametric identity** `min_agreeCap_eq`: if `F` and `G` agree below `e`, then
  `agreeCap F H` and `agreeCap G H` agree below `e` for every `H`;
* the **level cap** `levelCap l I F γ G δ = roundDown l I (min (agreeCap F G) (min γ δ))` of
  two capped labellings — below both caps and below their agreement, self-visible, in the
  alphabet, equal to `γ` on the diagonal (`levelCap_self`), and satisfying the capped
  ultrametric identity `min_levelCap_eq`, which is the sibling locality of a family whose rows
  read one another by level caps.

Nothing here mentions cell schemes; the tower instantiates `Z` with a lower set.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd

/-! ## The coded alphabet -/

/-- The **coded alphabet** at grade `l` with block bound `I`: `⊥` and `ω·i + j`, `i < I`,
`j ≤ l + 1`. -/
noncomputable def alph (l I : ℕ) : Finset ExtOrd :=
  insert ⊥ ((Finset.univ : Finset (Fin I × Fin (l + 2))).image
    fun ij => ofOrd (Ordinal.omega0 * ((ij.1 : ℕ) : Ordinal) + ((ij.2 : ℕ) : Ordinal)))

theorem bot_mem_alph (l I : ℕ) : (⊥ : ExtOrd) ∈ alph l I := Finset.mem_insert_self _ _

theorem mem_alph_iff {l I : ℕ} {x : ExtOrd} :
    x ∈ alph l I ↔ x = ⊥ ∨ ∃ i j : ℕ, i < I ∧ j ≤ l + 1 ∧
      x = ofOrd (Ordinal.omega0 * (i : Ordinal) + (j : Ordinal)) := by
  simp only [alph, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro (h | ⟨i, j, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, j, i.2, Nat.lt_succ_iff.mp j.2, h.symm⟩
  · rintro (h | ⟨i, j, hi, hj, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨i, hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩, h.symm⟩

theorem ne_top_of_mem_alph {l I : ℕ} {x : ExtOrd} (h : x ∈ alph l I) : x ≠ ⊤ := by
  rcases mem_alph_iff.mp h with rfl | ⟨i, j, -, -, rfl⟩
  · exact bot_ne_top
  · exact ofOrd_ne_top _

/-! ## Rounding down to a self-visible alphabet value -/

open Classical in
/-- **Rounding down**: the largest self-visible value of the alphabet below `x` (`⊥` at worst). -/
noncomputable def roundDown (l I : ℕ) (x : ExtOrd) : ExtOrd :=
  ((alph l I).filter fun a => SelfVis l a ∧ a ≤ x).max'
    ⟨⊥, Finset.mem_filter.mpr ⟨bot_mem_alph l I, selfVis_bot l, bot_le⟩⟩

theorem roundDown_spec (l I : ℕ) (x : ExtOrd) :
    roundDown l I x ∈ alph l I ∧ SelfVis l (roundDown l I x) ∧ roundDown l I x ≤ x := by
  classical
  have h := Finset.max'_mem ((alph l I).filter fun a => SelfVis l a ∧ a ≤ x)
    ⟨⊥, Finset.mem_filter.mpr ⟨bot_mem_alph l I, selfVis_bot l, bot_le⟩⟩
  rw [Finset.mem_filter] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem roundDown_selfVis (l I : ℕ) (x : ExtOrd) : SelfVis l (roundDown l I x) :=
  (roundDown_spec l I x).2.1

/-! ## Agreement caps -/

section Agreement

variable {Z : Type*} [Fintype Z]

open Classical in
/-- The **agreement cap** of two labellings: the largest value below which they agree —
the infimum, over the cells where they differ, of the smaller of the two labels (`⊤` if they
agree everywhere). -/
noncomputable def agreeCap (F G : Z → ExtOrd) : ExtOrd :=
  (Finset.univ.filter fun z => F z ≠ G z).inf fun z => min (F z) (G z)

/-! ## Level caps -/

/-- The **level cap** between two capped labellings: the agreement cap, capped by both caps,
rounded down to a self-visible alphabet value at grade `l`. -/
noncomputable def levelCap (l I : ℕ) (F : Z → ExtOrd) (γ : ExtOrd) (G : Z → ExtOrd) (δ : ExtOrd) :
    ExtOrd :=
  roundDown l I (min (agreeCap F G) (min γ δ))

variable (l I : ℕ) (F : Z → ExtOrd) (γ : ExtOrd) (G : Z → ExtOrd) (δ : ExtOrd)

theorem levelCap_selfVis : SelfVis l (levelCap l I F γ G δ) := roundDown_selfVis _ _ _

end Agreement

end VaughtConjecture.Knight
