/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CappedDonorLowRef
import VaughtConjecture.Knight.SourceBlockLocalityTransport

/-! # Exact release of the private frontier (audit16 §2, note §3.2)

The second original-row operation of the two-threshold family, on the **unchanged private scheme
`C`**, from the strict source gap (GAP) and numerical shielding.

Every extension call below goes through the equal-index form of bountifulness
(`Semantics.IsBountiful.extend`, in `CappedDonorReceiving`), so no separate case is needed when
the owner's lower domain is the whole cutoff or the low face is the owner's whole lower domain.

**Exact frontier release, arbitrary root** (`LowRef.exists_release`; newapproach2 §5): let `v`
be lawful at a cutoff `j ≥ K`, let `γ > ⊥` be permissible there, and suppose the frontier
exceeds `γ` while every present donor non-top face value is strictly below `γ` (SHIELD, on the
whole present root, high grades included).  Then there is a lawful `v'` with the whole present
face literal, every value retained below `γ`, the low source exactly `γ`, the owner's value not
lowered, and frontier exactly `γ`:

* with `L = v c > γ` and `τ` the exact normalized witness of `v` at `c`, retune
  `ν x = τ x ∧ γ` for `x ≤ h` and `ν x = τ x` above `h` (`releaseShifter`) — bounded, monotone
  and replacement-compatible through `K` because `h` is `K`-visible (`releaseShifter_witness`);
* `w = ν ∘ E_c` is lawful on the owner's whole lower domain by source-block transport: it has the
  bottom pattern of the lawful capped old target `v ∧ L = τ ∘ E_c` because `γ` is positive;
  GAP keeps the donor-top face values at `τ ∘ E_c`, SHIELD keeps the non-top ones, so
  `w = v ∧ L` on the face, `w c = L` and `w r = γ`;
* restore the exact **grade-`≤ K` part of the face** at cap `L` inside the owner's lower domain
  (`L` is a valid grade-`K` cap there; an empty low part needs no call) and prescribe the result
  into the cutoff at cap `γ` by old `C`-bountifulness — two extension calls inside the unchanged
  `C`;
* a face cell of grade above `K` is donor non-top, so SHIELD and the `γ`-cap agreement fix its
  value exactly: the two caps `L` (through `K` only) and `γ` (at the cutoff) are kept apart.

This may alter private values above `γ`; it does not retain them literally.  Still-future
coordinates are outside the current numerical domain and are untouched when the lemma is applied
to a source-state fibre. -/

namespace VaughtConjecture.Knight

open  Value   

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I]   
   {K : ℕ} 

namespace LowRef

/-! ## The release shifter -/

/-- The release shifter: the old witness capped at `γ` up to `h`, the old witness above. -/
noncomputable def releaseShifter (τ : LabelMap) (h γ x : ExtOrd) :=
  if x ≤ h then min (τ x) γ else τ x

theorem releaseShifter_of_le {τ : LabelMap} {h γ x : ExtOrd} (hx : x ≤ h) :
    releaseShifter τ h γ x = min (τ x) γ := by
  unfold releaseShifter; rw [ite_eq_left hx]

theorem releaseShifter_of_lt {τ : LabelMap} {h γ x : ExtOrd} (hx : h < x) :
    releaseShifter τ h γ x = τ x := by
  unfold releaseShifter; rw [ite_eq_right (not_le.mpr hx)]

theorem releaseShifter_eq_bot_iff {τ : LabelMap} {h γ : ExtOrd} (hγ : γ ≠ ⊥) (x : ExtOrd) :
    releaseShifter τ h γ x = ⊥ ↔ τ x = ⊥ := by simp_all [releaseShifter] <;> aesop

theorem releaseShifter_le {τ : LabelMap} (h γ x : ExtOrd) :
    releaseShifter τ h γ x ≤ τ x := by
  unfold releaseShifter
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- The release shifter is a normalized witness through `K` whenever the old witness is, the
split point `h` and the cap `γ` are `K`-visible and `γ` is positive. -/
theorem releaseShifter_witness {τ : LabelMap} (hτ : Witness (gTop K) τ) {h γ : ExtOrd}
    (hh : SelfVis K h) (hγ : SelfVis K γ) (hγpos : γ ≠ ⊥) :
    Witness (gTop K) (releaseShifter τ h γ) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by rw [releaseShifter_of_le bot_le, hτ.bot, min_bot_left]
  mono := by
    intro x y hxy
    by_cases hy : y ≤ h
    · rw [releaseShifter_of_le (hxy.trans hy), releaseShifter_of_le hy]
      exact min_le_min_right _ (hτ.mono hxy)
    · rw [releaseShifter_of_lt (not_le.mp hy)]
      exact (releaseShifter_le h γ x).trans (hτ.mono hxy)
  clause5 := by
    intro x kk hle i hi
    by_cases hkk : kk ≤ K
    · have h1 : τ (extVisibilityReplace x kk i) = extVisibilityReplace (τ x) kk i :=
        hτ.clause5 x kk (by rw [gTop_of_le hkk]; exact le_top) i hi
      by_cases hx : x ≤ h
      · rw [releaseShifter_of_le hx, releaseShifter_of_le (evr_le_of_le_selfVis hh hkk hi hx), h1,
          evr_min_of_selfVis hγ hkk hi]
      · rw [releaseShifter_of_lt (not_le.mp hx),
          releaseShifter_of_lt (lt_evr_of_selfVis_lt (hh.mono hkk) (not_le.mp hx)), h1]
    · rw [gTop_of_gt (not_le.mp hkk), le_bot_iff] at hle
      have hx : τ x = ⊥ := (releaseShifter_eq_bot_iff hγpos x).mp hle
      have h1 : τ (extVisibilityReplace x kk i) = ⊥ := by
        rw [hτ.clause5 x kk (by rw [gTop_of_gt (not_le.mp hkk), hx]) i hi, hx,
          extVisibilityReplace_bot]
      rw [hle, ]
      exact (releaseShifter_eq_bot_iff hγpos _).mpr h1

/-! ## Geometry of the owner's lower domain at a cutoff -/

/-! ## Exact frontier release -/




