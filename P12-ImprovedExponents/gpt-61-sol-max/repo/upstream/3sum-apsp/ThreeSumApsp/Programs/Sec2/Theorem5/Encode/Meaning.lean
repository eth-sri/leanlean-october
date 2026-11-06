/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Recursion
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays

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

public section

open ThreeSumApsp

namespace Light.Sec2

open ThreeSumApsp.Spec

/-! ## From positions to strings -/

section
variable {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)

/-- The recursion on positions computes the procedure of Section 2.4.1, if the array and the table
of coefficients are stored by digits. -/
private theorem encIdx_eq_computeEncoding {c}
    (hc : ∀ lam s, c (7 * termIdx lam + e s) = coef lam s) L
     A {arr}
    (harr : ∀ j < 7 ^ L, arr j = A (decodeStr e L j)) {i} (hi : i < 10 ^ L) :
    encIdx c L arr i = computeEncoding coef L A (decodeT L i) := by
  induction L generalizing arr i with
  | zero =>
    rw [encIdx, computeEncoding, harr 0 (by norm_num)]
    exact congrArg A (Subsingleton.elim _ _)
  | succ L ih =>
    -- The first digit of i is the digit of a term λ, and the rest of i is the code of a leaf below.
    have hpos : 0 < 10 ^ L := by positivity

    have hrest : i % 10 ^ L < 10 ^ L := Nat.mod_lt _ hpos
    obtain ⟨lam, hidx⟩ : ∃ lam : Term, (termEquiv lam : ℕ) = i / 10 ^ L :=
      ⟨termOfNat _, termIdx_termOfNat (by rwa [Nat.div_lt_iff_lt_mul hpos, ← pow_succ'])⟩

    rw [encIdx, (by
      have hcons := decodeStr_cons termEquiv lam hrest
      rwa [hidx, Nat.div_add_mod'] at hcons
     : decodeT (L + 1) i = Fin.cons lam (decodeT L (i % 10 ^ L))), computeEncoding, Fin.cons_zero, Fin.tail_cons]
    unfold encSlice
    -- Step (2) of the procedure of Section 2.4.1: the sum over the digits is the sum over the
    -- variables.
    refine ih _ (fun j hj => ?_) hrest
    rw [← Fin.sum_univ_eq_sum_range (fun s => c (7 * (i / 10 ^ L) + s) * arr (s * 7 ^ L + j)) 7,
      ← e.sum_comp fun s  => c (7 * (i / 10 ^ L) + s) * arr (s * 7 ^ L + j)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [sliceAt, ← hidx, show (termEquiv lam : ℕ) = termIdx lam from rfl, hc,
      harr _ (by rw [pow_succ']; exact Nat.mul_add_lt_mul (e s).isLt hj), decodeStr_cons e s hj]

end

/-! ## The specification of encode, on lists -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : Light.Memory} {src out scr tab p7 p10 L : ℕ} {V : ℤ}

/-- The hypotheses of encode hold if the source, the table of coefficients and the two tables of
powers are in their places and the numbers obey the bounds. -/
private theorem EncodePre.of_seg {l T} (lay : EncodeLayout lim src out scr tab p7 p10 L)
    (hl : l.length = 7 ^ L) (hsrc : Seg μ src l) (hV : ∀ x ∈ l, -V ≤ x ∧ x ≤ V)
    (hT : T.length = 70) (htab : Seg μ tab T) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (h7 : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)) (h10 : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ))
    (hVB : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word) :
    EncodePre lim μ src out scr tab p7 p10 V L (fun j => l.getD j 0) fun i => T.getD i 0 :=
  { lay := lay
    srcV := fun j hj => hsrc.getD (by omega) 0
    src_bound := fun j hj => by
      simp_all
    tabV := fun i hi => htab.getD (by omega) 0
    coef_bound := fun i hi => by
      simp_all
    p7V := h7, p10V := h10, word_bound := hVB }

end Light.Sec2
