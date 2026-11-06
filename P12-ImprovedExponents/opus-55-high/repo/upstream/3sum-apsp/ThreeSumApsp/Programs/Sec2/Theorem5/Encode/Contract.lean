/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning

/-!
# What the callers of encode assume

The callers of encode (Section 2.4.1) assume a specification of the procedure that does not name its
body: `EncodeLSpec` for the array a and the forms φ_λ, `EncodeRSpec` for b and ψ_λ.  Both hold for
every program that has encStep and encode at their numbers.  The places that the callers provide are
a layout for encode (`EncodePlaces.layout`), so the specification of encode on lists applies
(`encode_entry`, for any alphabet of seven variables); the two specifications are its cases for the
left variables with the forms φ_λ and for the right variables with the forms ψ_λ.
-/


namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {n Lmax src dst scr tab p7 p10 : ℕ} {μ : ℕ → ℤ}

/-- The scratch area of encode has fewer than 7^L cells. -/
theorem scrSize_le (L : ℕ) : scrSize L + 1 ≤ 7 ^ L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    grind [scrSize]

/-- The places that the callers provide are a layout for encode. -/
theorem EncodePlaces.layout (std : Std lim)
    (h : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ) :
    EncodeLayout lim src dst scr tab p7 p10 n := by
  light_facts h
  have hscr := scrSize_le n
  exact ⟨std, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A cell of a table of powers. -/
theorem pow_of_seg {p b : ℕ} (h : Seg μ p (powList b (Lmax + 1))) (hn : n ≤ Lmax) :
    ∀ i < n, μ (p + i) = ((b ^ i : ℕ) : ℤ) := fun i hi => by
  rw [h.get (by simp; omega), getElem_powList]



