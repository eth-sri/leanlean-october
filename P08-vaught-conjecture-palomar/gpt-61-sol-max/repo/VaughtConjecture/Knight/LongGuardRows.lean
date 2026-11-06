/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.VisibleOrderInterpolation
import VaughtConjecture.Knight.SlotControllerFamily

/-! # Explicit grade-one long guards

At cut `i`, retain the separated short sources through rank `i` and collapse
all higher ranks to the long endpoint `ω * i + 2`. A monotone visible table
is a faithful target precisely when its two readings at this mixed source
block have the same bottom flag (provided both endpoints actually occur).

The sufficiency proof constructs a faithful witness at every threshold, not
just a bounded numerical map. This is the local guard used by the proposed
support compiler in `simplification-notes6/zero_implications.md`, Section 2.
It does not by itself install a support plan or prove lifting.
-/

namespace VaughtConjecture.Knight.LongGuardRows

open Transform Value ExtOrd SharpWitnessComposition FullRowLifting

/-- A finite visible table with the exact source-block zero condition has a
faithful witness. Repeated source occurrences remain literal. -/
theorem transforms_of_visible_table {Y} [Finite Y] {E t}
    (hE : ∀ d, SelfVis 1 (E d)) (ht : ∀ d, SelfVis 1 (t d))
    (hord : ∀ d e, E d ≤ E e → t d ≤ t e)
    (hbot : ∀ d, E d = ⊥ → t d = ⊥)
    (hblock : ∀ d e, blockFloor (E d) = blockFloor (E e) → t d = ⊥ → t e = ⊥) :
    TransformsTo (fun _ : Y => 1) E t := by
  
  let _ := Fintype.ofFinite Y
  let s := Finset.univ.image E
  have hf := orderInterpolate_bounded hE ht
  have hb : BlockBottom s (orderInterpolate E t) := by
    intro x hx y hy hxy hz
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hy
    rw [orderInterpolate_read hord hbot] at hz ⊢
    exact hblock d e hxy hz
  obtain ⟨τ, hτ, hread⟩ := (hf.interpolate_iff_source_blocks s).mpr hb
  apply hτ.transformsTo
  intro d
  rw [gTop_of_le le_rfl, min_top_right,
    hread _ (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩),
    orderInterpolate_read hord hbot]

/-- Actual faithful locality, even with a nontrivial suppressor, prohibits
different bottom flags in one source block at a common grade. -/
theorem bottom_of_same_block {Y} {E t}
    (h : TransformsTo (fun _ : Y => 1) E t) {d e}
    (hb : blockFloor (E d) = blockFloor (E e)) (hd : t d = ⊥) : t e = ⊥ := by
  obtain ⟨g, σ, hg, hgv, h0, hm, h5, hr⟩ := h
  have hz  := (hr d).symm.trans hd
  rcases min_eq_bot.mp hz with hz | hz
  · have he := witness_bot_of_same_block
      ((⟨hg, hgv, h0, hm, h5⟩)) hb hz
    rw [hr e, he, min_bot_left]
  · rw [hr e, hz, min_bot_right]

noncomputable def endpoint (i : ℕ) :=
  ofOrd (Ordinal.omega0 * i + (2 : ℕ))

noncomputable def source (i k : ℕ) :=
  if k ≤ i then SlotControllerFamily.value k else endpoint i

theorem endpoint_visible i : SelfVis 1 (endpoint i) := by
  rw [endpoint, selfVis_ofOrd_iff, finitePart_code]
  omega

theorem source_visible i k : SelfVis 1 (source i k) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_visible k
  · exact endpoint_visible i

theorem source_coded i k : IsCodedLabel 1 (source i k) := by
  unfold source
  split_ifs
  · exact SlotControllerFamily.value_coded k
  · exact Or.inr ⟨i, 2, le_rfl, rfl⟩

@[simp] theorem source_zero i : source i 0 = ⊥ := by
  simp [source, SlotControllerFamily.value]

theorem value_lt_endpoint {i k} (hk : k ≤ i) :
    SlotControllerFamily.value k < endpoint i := by
  by_cases h0 : k = 0
  · simp_all [SlotControllerFamily.value, endpoint]
  · rw [SlotControllerFamily.value, ite_eq_right h0, SeparatedGradeOne.band, endpoint,
      ofOrd_lt_ofOrd]
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact code_lt_code_of_lt (Nat.cast_lt.mpr hk) 1 2
    · simp_all

theorem source_le_iff i k l :
    source i k ≤ source i l ↔ min k (i + 1) ≤ min l (i + 1) := by
  by_cases hk : k ≤ i <;> by_cases hl : l ≤ i
  · simp only [source, ite_eq_left hk, ite_eq_left hl,
      SlotControllerFamily.value_le_iff, min_eq_left (by omega : k ≤ i + 1),
      min_eq_left (by omega : l ≤ i + 1)]
  · have hv := (value_lt_endpoint hk).le
    simp only [source, ite_eq_left hk, ite_eq_right hl]
    constructor
    · intro _; omega
    · intro _; exact hv
  · have hv := not_le_of_gt (value_lt_endpoint hl)
    simp only [source, ite_eq_right hk, ite_eq_left hl]
    constructor
    · intro h; exact (hv h).elim
    · intro h; omega
  · grind [source]


