/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SupportLadderRows
import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # Exact decoding of the complete rung table

The numerical table is defined at every retained anchor and every rung, even
when the input profile has no chosen anchor in the catalogue. Prefix agreement
does not need catalogue coverage. Lawfulness is asserted only when an actual
anchor has the input's rank profile.

Decoding a normalized table recovers its entire ceiling-filled table, not just
the represented field values. This is the base identity used by the recursive
renderer; it does not assert exact restriction between construction grades.
-/

namespace VaughtConjecture.Knight.RungTableRendering
open    LadderScalarRendering

variable {X  : Type*} [Fintype X] 

/-- A monotone finite round trip transports every occupied and unused level. -/
theorem level_decode (p : X → ExtOrd) {f g : LabelMap}
    (hf : Monotone f) (hg : Monotone g) (hfbot : f ⊥ = ⊥) (hgbot : g ⊥ = ⊥)
    (hinv : ∀ d, g (f (p d)) = p d) (C : ExtOrd) (i : ℕ) :
    g (LadderScalarRendering.level (values (fun d => f (p d))) C i) =
      LadderScalarRendering.level (values p) (g C) i := by
  
  have hpos (d : X) : f (p d) ≠ ⊥ ↔ p d ≠ ⊥ := by
    grind
  have himage : values (fun d => f (p d)) = (values p).image f := by
    simp_all only [VaughtConjecture.Knight.LadderScalarRendering.values] <;> aesop
  have hcard : (values (fun d => f (p d))).card = (values p).card := by
    rw [himage]
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    obtain ⟨_, d, rfl⟩ := mem_values.mp hx
    obtain ⟨_, e, rfl⟩ := mem_values.mp hy
    simpa only [hinv] using congrArg g he
  have hr := ReceivingCatalogueRanks.fieldRank_of_leftInverse p hf hg hfbot hgbot hinv
  unfold LadderScalarRendering.level
  rw [hcard]
  split_ifs with hi
  · rfl
  · apply le_antisymm
    · by_cases hn : ((values (fun d => f (p d))).filter
          (fun x => rank (values (fun d => f (p d))) x ≤ i)).Nonempty
      · obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
        rw [← he]
        obtain ⟨hxv, hxi⟩ := Finset.mem_filter.mp hx
        obtain ⟨hx, d, rfl⟩ := mem_values.mp hxv
        simp only [id_eq, hinv]
        apply Finset.le_sup (f := id)
        refine Finset.mem_filter.mpr ⟨mem_values.mpr ⟨(hpos d).mp hx, d, rfl⟩, ?_⟩
        change fieldRank p d ≤ i
        change fieldRank (fun e => f (p e)) d ≤ i at hxi
        rwa [hr d] at hxi
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty, hgbot]
        exact bot_le
    · apply Finset.sup_le
      intro x hx
      obtain ⟨hxv, hxi⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx, d, rfl⟩ := mem_values.mp hxv
      rw [← hinv d]
      apply hg
      apply Finset.le_sup (f := id)
      refine Finset.mem_filter.mpr ⟨mem_values.mpr ⟨(hpos d).mpr hx, d, rfl⟩, ?_⟩
      change fieldRank (fun e => f (p e)) d ≤ i
      rw [hr d]
      exact hxi


