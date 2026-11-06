/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Recursion
import ThreeSumApsp.Sec2.Lemma10
import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays

/-!
# What encode computes, in the paper's terms

The result of encode is described by a recursion on positions in arrays (`encIdx`).  Here this is
linked with the definitions of the paper (Section 2.4.1) through arrays on strings as lists: if the
source holds an array on strings and the table holds the coefficients of the linear forms, then the
output holds the encoding of the array.

Both sides are treated at once, for an alphabet of seven variables with any coefficients:
`computeEncoding` is the procedure of Section 2.4.1 for such an alphabet,
`encIdx_eq_computeEncoding` says that the recursion on positions computes it, and `encode_str` is
the specification of encode in these terms. For the two alphabets of the paper the procedure gives
the two encodings (`computeEncoding_phi`, `computeEncoding_psi`).
-/


open ThreeSumApsp

namespace Light.Sec2

open ThreeSumApsp.Spec

/-! ## From positions to strings -/

section
variable {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)

/-- The recursion on positions computes the procedure of Section 2.4.1, if the array and the table
of coefficients are stored by digits. -/
theorem encIdx_eq_computeEncoding {c : ℕ → ℤ}
    (hc : ∀ lam s, c (7 * (termIdx lam : ℕ) + (e s : ℕ)) = coef lam s) (L : ℕ)
    (A : (Fin L → α) → ℤ) {arr : ℕ → ℤ}
    (harr : ∀ j < 7 ^ L, arr j = A (decodeStr e L j)) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c L arr i = computeEncoding coef L A (decodeT L i) := by
  induction L generalizing arr i with
  | zero =>
    rw [encIdx, harr 0 (by norm_num)]
    exact congrArg A (Subsingleton.elim _ _)
  | succ L ih =>
    -- The first digit of i is the digit of a term λ, and the rest of i is the code of a leaf below.
    have hdigit : i / 10 ^ L < 10 := by simp_all [Nat.div_lt_iff_lt_mul, pow_succ']
    have hrest : i % 10 ^ L < 10 ^ L := by omega
    obtain ⟨lam, hidx⟩ : ∃ lam : Term, ((termEquiv lam : Fin 10) : ℕ) = i / 10 ^ L :=
      ⟨termOfNat _, termIdx_termOfNat hdigit⟩
    have hleaf : decodeT _ i = Fin.cons lam (decodeT L (i % 10 ^ L)) := by
      have hcons := decodeStr_cons termEquiv lam hrest
      rwa [hidx, Nat.div_add_mod'] at hcons
    rw [encIdx, hleaf, computeEncoding, Fin.cons_zero]
    unfold encSlice
    -- Step (2) of the procedure of Section 2.4.1: the sum over the digits is the sum over the
    -- variables.
    refine ih _ (fun j hj => ?_) hrest
    rw [← Fin.sum_univ_eq_sum_range,
      ← e.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sliceAt, ← hidx, show termEquiv lam = termIdx lam from rfl, hc,
      harr _ (by simp_all [pow_succ', Nat.mul_add_lt_mul]), decodeStr_cons e s hj]

end

/-! ## The specification of encode, on lists -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src out scr tab p7 p10 L : ℕ} {V : ℤ}

/-- The hypotheses of encode hold if the source, the table of coefficients and the two tables of
powers are in their places and the numbers obey the bounds. -/
theorem EncodePre.of_seg {l T : List ℤ} (lay : EncodeLayout lim src out scr tab p7 p10 L)
    (hl : l.length = 7 ^ L) (hsrc : Seg μ src l) (hV : ∀ x ∈ l, -V ≤ x ∧ x ≤ V)
    (hT : T.length = 70) (htab : Seg μ tab T) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) :
    EncodePre lim μ src out scr tab p7 p10 V L (fun j => l.getD j 0) (fun i => T.getD i 0) :=
  ⟨lay, by aesop, by simp_all, by aesop, by simp_all, h7, h10, hVB⟩

