/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Transform

/-! # Scalar visibility algebra

General visibility, order, and suppressor facts, independent of semantic
schemes, recoding inventories, model acquisition, and controller examples.
Extracted with the original names and proofs (up to lint-only edits) from
`Repair`, `CountedRecoding`, `CountedEncoding`, `RowCorrectness`, and
`WitnessSplice`, and `CoupledGradeTwoRetune`; those modules retain their
compatibility import surfaces.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- Self-visibility of a label at threshold `k`, spelled with `extVisibilityReplace`. -/
abbrev SelfVis (k : ℕ) (x : ExtOrd) : Prop := extVisibilityReplace x k k = x

theorem selfVis_mono {k k'} {x} (h : SelfVis k x) (hk : k' ≤ k) :
    SelfVis k' x :=
  extVisReplace_self_of_le h hk

theorem selfVis_min {k} {x y} (hx : SelfVis k x) (hy : SelfVis k y) :
    SelfVis k (min x y) := by grind

theorem selfVis_bot k : SelfVis k ⊥ := rfl

theorem SelfVis.mono {k k'} {x} (h : SelfVis k x) (hle : k' ≤ k) : SelfVis k' x :=
  selfVis_mono h hle

theorem evr_eq_self_of_selfVis {k} {x} (h : SelfVis k x) i :
    extVisibilityReplace x k i = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp
  · simp
  · unfold SelfVis at h
    rw [extVisibilityReplace_ofOrd, ofOrd_inj] at h
    simp_all
    unfold visibilityReplace at h ⊢
    split_ifs with hfp
    · rw [ite_eq_left hfp] at h
      exfalso
      unfold ordinalReplace at h
      have := congrArg finitePart h
      rw [finitePart_limitPart_add_nat] at this
      omega
    · rfl

section
variable {α : Ordinal.{0}} {k : ℕ}

theorem extVisibilityReplace_of_le_finitePart (h : k ≤ finitePart α)
    i :
    extVisibilityReplace (ofOrd α) k i = ofOrd α := by
  rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_right (not_lt.mpr h)]

theorem extVisibilityReplace_of_finitePart_lt (h : finitePart α < k)
    i :
    extVisibilityReplace (ofOrd α) k i = ofOrd (limitPart α + i) := by
  rw [extVisibilityReplace_ofOrd, visibilityReplace, ite_eq_left h]; rfl

end

theorem limitPart_add_finitePart α : limitPart α + finitePart α = α :=
  decomposition α

/-- Visibility replacement at threshold `N` with offset `i ≤ N` does not push a label above a
self-visible-at-`N` bound it lies below. -/
theorem extVisibilityReplace_le_of_le_selfVis {x y} {N i} (hi : i ≤ N)
    (hy : extVisibilityReplace y N N = y) (hxy : x ≤ y) :
    extVisibilityReplace x N i ≤ y := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · simp
  · simp_all
  · rcases ExtOrd.cases y with rfl | rfl | ⟨δ, rfl⟩
    · simp_all
    · exact le_top
    · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
      rw [extVisibilityReplace_self_iff] at hy
      rcases hy with h | h | ⟨δ', hδ, hN⟩
      · exact absurd h (ofOrd_ne_bot δ)
      · exact absurd h (ofOrd_ne_top δ)
      · rw [ofOrd_inj] at hδ; subst hδ
        exact visReplace_le_of_le_selfVis (ofOrd_le_ofOrd.mp hxy) hN hi

/-- The antitone suppressor is bounded below at grade `≤ N` by its value at `N`. -/
theorem suppressor_le_of_grade_le {g : ℕ → ExtOrd} (hanti : ∀ n m, n < m → g m ≤ g n)
    {k N} (hk : k ≤ N) : g N ≤ g k := by grind

/-- Between distinct limit parts there is room for a whole block. -/
theorem lt_limitPart_of_limitPart_lt {ξ α} (h : limitPart ξ < limitPart α) :
    ξ < limitPart α := by
  unfold limitPart at h ⊢
  have hq : ξ / Ordinal.omega0 < α / Ordinal.omega0 := by simp_all
  have h1 : Ordinal.omega0 * (ξ / Ordinal.omega0 + 1) ≤ Ordinal.omega0 * (α / Ordinal.omega0) :=
    mul_le_mul_right (Order.add_one_le_of_lt hq) _
  refine lt_of_lt_of_le ?_ h1
  rw [mul_add_one]
  calc ξ = limitPart ξ + ↑(finitePart ξ) := (decomposition ξ).symm
    _ < limitPart ξ + Ordinal.omega0 :=
      add_lt_add_right (Ordinal.natCast_lt_omega0 _) _

/-! ## Visibility replacement is monotone -/

theorem visibilityReplace_mono {α β} (h : α ≤ β) {k i} (hi : i ≤ k) :
    visibilityReplace α k i ≤ visibilityReplace β k i := by
  unfold visibilityReplace
  split_ifs with ha hb hb
  · exact add_le_add (limitPart_mono h) le_rfl
  · unfold ordinalReplace
    rw [not_lt] at hb
    calc limitPart α + (i : Ordinal) ≤ limitPart β + (k : Ordinal) :=
          add_le_add (limitPart_mono h) (by exact_mod_cast hi)
      _ ≤ limitPart β + (finitePart β : Ordinal) := add_le_add_right (by exact_mod_cast hb) _
      _ = β := decomposition β
  · unfold ordinalReplace
    rw [not_lt] at ha
    have hlt : limitPart α < limitPart β := by
      rcases lt_or_eq_of_le (limitPart_mono h) with hlt | heq
      · exact hlt
      · exfalso
        have : β < α := by
          calc β = limitPart β + ↑(finitePart β) := (decomposition β).symm
            _ = limitPart α + ↑(finitePart β) := by rw [heq]
            _ < limitPart α + ↑(finitePart α) := add_lt_add_right
                (Nat.cast_lt.mpr (lt_of_lt_of_le hb ha) :
                  ((finitePart β : ℕ) : Ordinal) < (finitePart α : ℕ)) _
            _ = α := decomposition α
        exact absurd h (not_le.mpr this)
    exact le_trans (le_of_lt (lt_limitPart_of_limitPart_lt hlt)) le_self_add
  · exact h

theorem evr_mono {x y} (h : x ≤ y) {k i} (hi : i ≤ k) :
    extVisibilityReplace x k i ≤ extVisibilityReplace y k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · simp_all
  · rw [top_le_iff.mp h]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨β, rfl⟩
    · grind
    · simp_all
    · rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
      exact visibilityReplace_mono (ofOrd_le_ofOrd.mp h) hi

theorem extVisibilityReplace_max x y {k i} (hi : i ≤ k) :
    extVisibilityReplace (max x y) k i =
      max (extVisibilityReplace x k i) (extVisibilityReplace y k i) := by
  have hm : Monotone (fun z => extVisibilityReplace z k i) := fun a b h => evr_mono h hi
  exact hm.map_max

/-- A self-visible-at-`N` lower bound survives visibility replacement at threshold `N`. -/
theorem le_extVisibilityReplace_of_selfVis_le {x y} {N i}
    (hy : extVisibilityReplace y N N = y) (hyx : y ≤ x) : y ≤ extVisibilityReplace x N i := by
  rcases ExtOrd.cases y with rfl | rfl | ⟨δ, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hyx, extVisibilityReplace_top]
  · rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
    · exact absurd hyx (not_ofOrd_le_bot δ)
    · rw [extVisibilityReplace_top]; exact le_top
    · rw [extVisibilityReplace_ofOrd, ofOrd_le_ofOrd]
      rw [extVisibilityReplace_self_iff] at hy
      obtain ⟨δ', hδ, hN⟩ := (hy.resolve_left (ofOrd_ne_bot δ)).resolve_left (ofOrd_ne_top δ)
      rw [ofOrd_inj] at hδ; subst hδ
      have hβδ := ofOrd_le_ofOrd.mp hyx
      unfold visibilityReplace
      split_ifs with hfp
      · unfold ordinalReplace
        have hlp : limitPart δ < limitPart β := by
          by_contra hle
          push Not at hle
          have heq : limitPart β = limitPart δ := le_antisymm hle (limitPart_mono hβδ)
          have hlt : β < δ := by
            calc β = limitPart β + finitePart β := (decomposition β).symm
              _ = limitPart δ + finitePart β := by rw [heq]
              _ < limitPart δ + finitePart δ := by
                  exact (add_lt_add_iff_left _).mpr
                    (Nat.cast_lt.mpr (lt_of_lt_of_le hfp hN))
              _ = δ := decomposition δ
          exact absurd hβδ (not_le.mpr hlt)
        have hω : limitPart δ + Ordinal.omega0 ≤ limitPart β := by
          unfold limitPart at hlp ⊢
          have hab : δ / Ordinal.omega0 < β / Ordinal.omega0 := by
            by_contra hle
            push Not at hle
            exact absurd hlp (not_lt.mpr (by
              first
                | exact mul_le_mul_left' hle _
                | exact mul_le_mul_right hle _))
          calc Ordinal.omega0 * (δ / Ordinal.omega0) + Ordinal.omega0
              = Ordinal.omega0 * Order.succ (δ / Ordinal.omega0) := (Ordinal.mul_succ _ _).symm
            _ ≤ Ordinal.omega0 * (β / Ordinal.omega0) := by
                first
                  | exact mul_le_mul_left' (Order.succ_le_of_lt hab) _
                  | exact mul_le_mul_right (Order.succ_le_of_lt hab) _
        have hδlt : δ < limitPart β + i := by
          calc δ = limitPart δ + finitePart δ := (decomposition δ).symm
            _ < limitPart δ + Ordinal.omega0 :=
                (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 _)
            _ ≤ limitPart β := hω
            _ ≤ limitPart β + i := le_self_add
        exact hδlt.le
      · exact hβδ

/-- Visibility replacement of a nonbottom label is nonbottom. -/
theorem extVisibilityReplace_ne_bot {a} (ha : a ≠ ⊥) k i :
    extVisibilityReplace a k i ≠ ⊥ := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · grind
  · simp_all
  · simp_all

/-- Visibility replacement above a `k`-visible ordinal cutoff stays strictly above it. -/
theorem visReplace_gt_of_gt {ξ α} {k i} (hk : k ≤ finitePart ξ) (hα : ξ < α) :
    ξ < visibilityReplace α k i := by
  unfold visibilityReplace
  split_ifs with hfp
  · unfold ordinalReplace
    have hlp := limitPart_mono hα.le
    rcases lt_or_eq_of_le hlp with hlt | heq
    · exact lt_of_lt_of_le (lt_limitPart_of_limitPart_lt hlt) le_self_add
    · exfalso
      have h3 : α < ξ := by
        calc α = limitPart α + ↑(finitePart α) := (decomposition α).symm
          _ = limitPart ξ + ↑(finitePart α) := by rw [heq]
          _ < limitPart ξ + ↑(finitePart ξ) := add_lt_add_right
              (Nat.cast_lt.mpr (lt_of_lt_of_le hfp hk) :
                ((finitePart α : ℕ) : Ordinal) < (finitePart ξ : ℕ)) _
          _ = ξ := decomposition ξ
      exact absurd hα (not_lt.mpr h3.le)
  · exact hα

theorem visReplace_eq α k i :
    visibilityReplace α k i =
      limitPart α + ((if finitePart α < k then i else finitePart α : ℕ) : Ordinal) := by
  unfold visibilityReplace
  split_ifs with h
  · rfl
  · exact (decomposition α).symm

end VaughtConjecture.Knight
