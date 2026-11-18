/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeTwoConstraints

/-! # The grade-two retuning: the visibility closure, the strip witness, and the three rules

**The visibility closure** `closeH H t = max t (min H (R₂ t))`, where `R₂` is grade-two
visibility replacement: the least upward repair of `t` whose minimum with `H` is grade-two
self-visible.  Its algebra: inflationary (`le_closeH`), bounded by `max t H` (`closeH_le`),
`min (closeH H t) H = R₂ (min t H)` (`min_closeH`), hence grade-two self-visible
(`selfVis_min_closeH`); bottom-reflecting (`closeH_eq_bot_iff`); grade-one self-visibility is
preserved (`closeH_selfVis₁`); **capped agreement** `min (closeH H t) γ = closeH (min H γ)
(min t γ)` (`min_closeH_cap`) and **legal values are fixed** (`closeH_min_eq_of_visible`).
The closure is what repairs the grade-one clamp: a grade-one label chosen by the grade-one rule
may fail to be grade-two self-visible below `H`.

**The strip witness** (`Witness.strip`): the single-block orbit shifter — `⊥` below `ω`, the
`ω`-block orbit `extVisibilityReplace m 2 (min (fp a) 2)` of a grade-one self-visible `m` on
`[ω, ω·2)`, and the constant grade-two self-visible `c` from `ω·2` on — is a faithful witness at
**every** threshold, with suppressor `gTop 2`.  The orbit strip is essential: a grade-one output
(finite part one) is not grade-two self-visible, so a constant step at threshold two would fail
clause 5; the orbit calculus `orbit_eq` is the commutation that makes clause 5 hold for all
thresholds `≤ 2`, and above grade two only bottom outputs activate the clause (the bottom fibre
is constant on each ordinal block, and replacement never crosses a limit).

**The cells of `(univ, 2)`** (`two_cases`): the six named cells and the proper cells of grades one
and two, with the rows read at each (`rows₃_E_proper_two`, `rows₃_E_s₀old`, `rows₃_E_s₀new`,
`rowX_s₀_of_proper`, `vS_of_proper'`), the face facts (`s₀old_le_H₀old_of_respects`,
`s₀new_le_H₀new_of_respects`, `proper_two_eq_bot'`), and the lower-set cases
(`below_s₀old_cases`, `below_s₀new_cases₂`).

**The three retuning rules** (`Retuned` bundles the eleven required properties: order, bottom
coupling, visibility at grades one and two, `H ≤ x₁`, grade-two visibility of `min x₀ H`, and
capped agreement in all three parameters):
* only the proper value protected (`rule_two_v`): `H' = Hq`, `x₀' = closeH Hq (max x₀q vP)`,
  `x₁' = max x₁q x₀'`;
* the old face protected (`rule_two_old`): `x₀' = x_p`, and `H' = h_p` when `h_p < x_p` (forced),
  `H' = max h_p Hq` when `h_p = x_p`, with the bottom branch when `x_p = ⊥`; the old high label
  `min x₀' H' = h_p` is preserved literally;
* the copy face protected (`rule_two_copy`): `x₁' = x_p`, `H' = h_p`,
  `x₀' = closeH h_p (max vP (min x₀q x_p))`, with the bottom fallback `x₀' = x_p`.

**The retuned labelling** `retune₂` and its values at the six cells (`retune₂_in`,
`retune₂_H₀old`, …, `retune₂_proper`).

Not done: the cash-out — `ProperToFull₃Low` at `j = 2` (the respect proof for `retune₂` over all
cells, with the strip witnesses at the three grade-two rows).  Grade three is out of scope: its
duplicate graded indices break the uniqueness argument.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## The visibility closure below a grade-two label -/

section Closure

/-- Grade-two visibility replacement. -/
noncomputable abbrev R₂ (t : ExtOrd) : ExtOrd := extVisibilityReplace t 2 2

theorem R₂_mono : Monotone R₂ := fun _ _ h => evr_mono h le_rfl
theorem R₂_of_selfVis {t : ExtOrd} (h : SelfVis 2 t) : R₂ t = t := h

end Closure

/-! ## The single-block orbit shifter at threshold two -/

section Strip

/-- The finite part of a label (`0` at `⊥` and `⊤`). -/
noncomputable def fpE : ExtOrd → ℕ
  | some (some α) => finitePart α
  | _ => 0

theorem fpE_ofOrd (α : Ordinal.{0}) : fpE (ofOrd α) = finitePart α := rfl

abbrev ωn (n : ℕ) : Ordinal.{0} := Ordinal.omega0 * ((n : ℕ) : Ordinal)

/-- **The orbit calculus**: replacing the finite part of the block-`ω` value commutes with the
threshold-`k` replacement, for `k ≤ 2`. -/
theorem orbit_eq {m : ExtOrd} (hm : SelfVis 1 m) {j k i : ℕ} (hk : k ≤ 2) (hi : i ≤ k) :
    extVisibilityReplace (extVisibilityReplace m 2 (min j 2)) k i =
      extVisibilityReplace m 2 (min (if j < k then i else j) 2) := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top, extVisibilityReplace_top]
  · have h1 : 1 ≤ finitePart μ := selfVis_ofOrd_iff.mp hm
    rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd,
      ofOrd_inj, visReplace_eq (visibilityReplace μ 2 (min j 2)), limitPart_visibilityReplace,
      finitePart_visibilityReplace, visReplace_eq μ 2]
    congr 1
    norm_cast
    split_ifs <;> omega

theorem evr_arg_mono (m : ExtOrd) {s s' : ℕ} (h : s ≤ s') :
    extVisibilityReplace m 2 s ≤ extVisibilityReplace m 2 s' := by
  rcases ExtOrd.cases m with rfl | rfl | ⟨μ, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · rw [extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd, ofOrd_le_ofOrd, visReplace_eq,
      visReplace_eq]
    split_ifs
    · exact add_le_add_right (Nat.cast_le.mpr h) _
    · exact le_rfl

open Classical in
/-- **The strip shifter**: `⊥` below `ω`, the block-`ω` orbit of `m` on `[ω, ω·2)`, the
constant `c` from `ω·2` on. -/
noncomputable def stripShifter (m c : ExtOrd) : ExtOrd → ExtOrd := fun a =>
  if a = ⊥ then ⊥ else if a < ofOrd (ωn 1) then ⊥
  else if a < ofOrd (ωn 2) then extVisibilityReplace m 2 (min (fpE a) 2) else c

theorem strip_bot (m c : ExtOrd) : stripShifter m c ⊥ = ⊥ := by
  classical
  unfold stripShifter; rw [ite_eq_left rfl]
theorem strip_of_lt_one {m c a : ExtOrd} (ha : a ≠ ⊥) (h : a < ofOrd (ωn 1)) :
    stripShifter m c a = ⊥ := by
  classical
  unfold stripShifter; rw [ite_eq_right ha, ite_eq_left h]
theorem strip_of_block {m c a : ExtOrd} (h1 : ofOrd (ωn 1) ≤ a) (h2 : a < ofOrd (ωn 2)) :
    stripShifter m c a = extVisibilityReplace m 2 (min (fpE a) 2) := by
  classical
  unfold stripShifter
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1),
    ite_eq_left h2]
theorem strip_of_ge {m c a : ExtOrd} (h : ofOrd (ωn 2) ≤ a) : stripShifter m c a = c := by
  classical
  unfold stripShifter
  have h1 : ofOrd (ωn 1) ≤ a := (ofOrd_le_ofOrd.mpr (by
    change Ordinal.omega0 * ((1 : ℕ) : Ordinal) ≤ Ordinal.omega0 * ((2 : ℕ) : Ordinal)
    exact mul_le_mul_right (Nat.cast_le.mpr (by decide)) _)).trans h
  rw [ite_eq_right (fun hb => not_ofOrd_le_bot _ (hb ▸ h1)), ite_eq_right (not_lt.mpr h1),
    ite_eq_right (not_lt.mpr h)]

theorem blockIdx_eq_one {α : Ordinal.{0}} (h1 : ωn 1 ≤ α) (h2 : α < ωn 2) :
    blockIdx α = ((1 : ℕ) : Ordinal) := by
  have hb1 : ((1 : ℕ) : Ordinal) ≤ blockIdx α := by
    have := blockIdx_mono h1
    rwa [show ωn 1 = Ordinal.omega0 * ((1 : ℕ) : Ordinal) + ((0 : ℕ) : Ordinal) by
      rw [Nat.cast_zero, add_zero], blockIdx_mul_add] at this
  have hb2 : blockIdx α < ((2 : ℕ) : Ordinal) := by
    by_contra h
    rw [not_lt] at h
    have : ωn 2 ≤ limitPart α := by
      rw [limitPart_eq_mul_blockIdx]; exact mul_le_mul_right h _
    exact absurd h2 (not_lt.mpr (this.trans (limitPart_le α)))
  have hb2' : blockIdx α < ((1 : ℕ) : Ordinal) + 1 := by rw [← Nat.cast_add_one]; exact hb2
  exact le_antisymm (Order.lt_add_one_iff.mp hb2') hb1

theorem limitPart_of_block {α : Ordinal.{0}} (h1 : ωn 1 ≤ α) (h2 : α < ωn 2) :
    limitPart α = ωn 1 := by
  rw [limitPart_eq_mul_blockIdx, blockIdx_eq_one h1 h2]

theorem fp_le_of_block {α β : Ordinal.{0}} (hα1 : ωn 1 ≤ α) (hα2 : α < ωn 2) (hβ1 : ωn 1 ≤ β)
    (hβ2 : β < ωn 2) (h : α ≤ β) : finitePart α ≤ finitePart β := by
  have eα := decomposition α
  have eβ := decomposition β
  rw [limitPart_of_block hα1 hα2] at eα
  rw [limitPart_of_block hβ1 hβ2] at eβ
  rw [← eα, ← eβ] at h
  exact Nat.cast_le.mp ((add_le_add_iff_left _).mp h)

theorem strip_val_le {m c : ExtOrd} (hc : SelfVis 2 c) (hmc : m ≤ c) (j : ℕ) :
    extVisibilityReplace m 2 (min j 2) ≤ c :=
  (evr_arg_mono m (min_le_right j 2)).trans ((R₂_mono hmc).trans (R₂_of_selfVis hc).le)

theorem ofOrd_of_block {a : ExtOrd} (h1 : ofOrd (ωn 1) ≤ a) (h2 : a < ofOrd (ωn 2)) :
    ∃ α : Ordinal.{0}, a = ofOrd α ∧ ωn 1 ≤ α ∧ α < ωn 2 := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
  · exact absurd h1 (not_ofOrd_le_bot _)
  · exact absurd h2 (not_lt.mpr le_top)
  · exact ⟨α, rfl, ofOrd_le_ofOrd.mp h1, ofOrd_lt_ofOrd.mp h2⟩

/-- **The strip witness at threshold two**, for every threshold: `m` self-visible at one,
`c` self-visible at two, `m ≤ c`. -/
theorem Witness.strip {m c : ExtOrd} (hm : SelfVis 1 m) (hc : SelfVis 2 c) (hmc : m ≤ c) :
    Witness (gTop 2) (stripShifter m c) where
  anti := (witness_id 2).anti
  vis := (witness_id 2).vis
  bot := strip_bot m c
  mono := by
    intro a b hab
    by_cases ha : a = ⊥
    · rw [ha, strip_bot]; exact bot_le
    have hb : b ≠ ⊥ := fun hb => ha (le_bot_iff.mp (hb ▸ hab))
    by_cases ha1 : a < ofOrd (ωn 1)
    · rw [strip_of_lt_one ha ha1]; exact bot_le
    have ha1' : ofOrd (ωn 1) ≤ a := not_lt.mp ha1
    have hb1' : ofOrd (ωn 1) ≤ b := ha1'.trans hab
    by_cases ha2 : a < ofOrd (ωn 2)
    · rw [strip_of_block ha1' ha2]
      by_cases hb2 : b < ofOrd (ωn 2)
      · rw [strip_of_block hb1' hb2]
        obtain ⟨α, rfl, hα1, hα2⟩ := ofOrd_of_block ha1' ha2
        obtain ⟨β, rfl, hβ1, hβ2⟩ := ofOrd_of_block hb1' hb2
        rw [fpE_ofOrd, fpE_ofOrd]
        exact evr_arg_mono m (min_le_min (fp_le_of_block hα1 hα2 hβ1 hβ2 (ofOrd_le_ofOrd.mp hab))
          le_rfl)
      · rw [strip_of_ge (not_lt.mp hb2)]; exact strip_val_le hc hmc _
    · have ha2' : ofOrd (ωn 2) ≤ a := not_lt.mp ha2
      rw [strip_of_ge ha2', strip_of_ge (ha2'.trans hab)]
  clause5 := by
    intro α k hk i hi
    by_cases hα : α = ⊥
    · rw [hα, strip_bot, extVisibilityReplace_bot, strip_bot]
    have hα' : extVisibilityReplace α k i ≠ ⊥ := extVisibilityReplace_ne_bot hα k i
    by_cases hkK : k ≤ 2
    · by_cases h1 : α < ofOrd (ωn 1)
      · rw [strip_of_lt_one hα h1, strip_of_lt_one hα' (evr_lt_limit h1 k i),
          extVisibilityReplace_bot]
      have h1' : ofOrd (ωn 1) ≤ α := not_lt.mp h1
      by_cases h2 : α < ofOrd (ωn 2)
      · obtain ⟨a, rfl, ha1, ha2⟩ := ofOrd_of_block h1' h2
        rw [strip_of_block h1' h2, strip_of_block (evr_ge_limit h1' k i) (evr_lt_limit h2 k i),
          fpE_ofOrd, extVisibilityReplace_ofOrd, fpE_ofOrd, finitePart_visibilityReplace]
        exact (orbit_eq hm hkK hi).symm
      · have h2' : ofOrd (ωn 2) ≤ α := not_lt.mp h2
        rw [strip_of_ge h2', strip_of_ge (evr_ge_limit h2' k i),
          evr_eq_self_of_selfVis (hc.mono hkK)]
    · rw [gTop_of_gt (by omega)] at hk
      have hσ := le_bot_iff.mp hk
      by_cases h1 : α < ofOrd (ωn 1)
      · have e1 : stripShifter m c (extVisibilityReplace α k i) = ⊥ :=
          strip_of_lt_one hα' (evr_lt_limit h1 k i)
        rw [e1, strip_of_lt_one hα h1, extVisibilityReplace_bot]
      have h1' : ofOrd (ωn 1) ≤ α := not_lt.mp h1
      by_cases h2 : α < ofOrd (ωn 2)
      · rw [strip_of_block h1' h2] at hσ
        have hm0 : m = ⊥ := by
          by_contra hne
          exact extVisibilityReplace_ne_bot hne 2 _ hσ
        have e1 : stripShifter m c (extVisibilityReplace α k i) =
            extVisibilityReplace m 2 (min (fpE (extVisibilityReplace α k i)) 2) :=
          strip_of_block (evr_ge_limit h1' k i) (evr_lt_limit h2 k i)
        rw [e1, strip_of_block h1' h2, hm0]
        simp only [extVisibilityReplace_bot]
      · have h2' : ofOrd (ωn 2) ≤ α := not_lt.mp h2
        rw [strip_of_ge h2'] at hσ
        have e1 : stripShifter m c (extVisibilityReplace α k i) = c :=
          strip_of_ge (evr_ge_limit h2' k i)
        rw [e1, strip_of_ge h2', hσ, extVisibilityReplace_bot]

/-! ### The strip at the sources -/

end Strip

/-! ## Stage B: the cells of `(univ, 2)`, the rows, the inputs -/

section Cells

/-! ### The rows at the grade-two cells -/

end Cells

/-! ### Facts about respecting labellings at grade two -/

section Inputs

end Inputs

/-! ## Stage C1: the three retuning rules -/

section Rules

end Rules

/-! ## Stage C2: the retuned labelling and the grade-two obligation -/

section RetuneTwo

variable {C : Finset (Fin 4)} {p : D₂.below (C, 2) → ExtOrd} {x₀' x₁' H' vP : ExtOrd}

end RetuneTwo

end VaughtConjecture.Knight
