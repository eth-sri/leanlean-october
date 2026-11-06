/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec3.Chunks
import ThreeSumApsp.Sec3.Parameters
import ThreeSumApsp.Sec3.Theorem17.Hashing

/-!
# Theorem 17, second step: the instances

With `s = ⌊√D⌋`, the part `C` is split into `h` pieces of at most `⌈s/g⌉` vertices, the pairs
`(a,b)` are grouped by `ϱ = w(a,b) mod p` into the sets `W_ϱ`, and every `W_ϱ` is cut into chunks of
at most `n²/√D` pairs.  There is one instance of Lop-AE-SparseTri(n, D) for each chunk and each
piece.  As in the paper:

* the pieces, and `h ≤ ⌈ng/s⌉` (`existsUnique_mem_piece`, `card_piece_le`,
  `numPieces_le`);
* the sets `W_ϱ` and their chunks (`TriangleInstance.existsUnique_mem_residueClass`,
  `TriangleInstance.card_chunkOf_le`);
* there are at most `p + √D ≤ 2√D` chunks in all (`TriangleInstance.totalChunks_le`); as a chunk
  holds a whole number of pairs, this rests on `n² < (s + 1)⌊n²/√D⌋ + p` (`sq_lt_mul_queryCap_add`);
* the middle part has at most `sp ≤ D` vertices (`TriangleInstance.middleAtMost_lopInstance`);
* within a chunk, `S(a,b,c) ≡ 0 (mod p)` is an equality of labels
  (`TriangleInstance.S_modEq_zero_iff`), so a query pair has a common neighbor if and only if some
  `c` in the piece has `S(a,b,c) ≡ 0 (mod p)` (`TriangleInstance.inTriangle_lopInstance_iff`);
* there are at most `2√D h ≤ 4ng` instances (`le_sOf_and_sqrt_le`,
  `TriangleInstance.card_instanceIndices_le`).

The file ends with a remark of Section 3.1 and of Remark 20: a vertex of `A` or `B` has at most
`⌈s/g⌉` neighbors in an instance (`TriangleInstance.ncard_nbr_lopInstance_le`).  Nothing else rests
on it.
-/


namespace ThreeSumApsp

variable {n D g p : ℕ}

/-! ### The pieces -/

/-- `s = ⌊√D⌋ ≤ √D`. -/
theorem sOf_le_sqrt (D : ℕ) : (sOf D : ℝ) ≤ Real.sqrt D := Nat.floor_le (Real.sqrt_nonneg _)

/-- `√D < s + 1`. -/
theorem sqrt_lt_sOf_add_one (D : ℕ) : Real.sqrt D < (sOf D : ℝ) + 1 := Nat.lt_floor_add_one _

/-- `s > 0` because `D ≥ 16`. -/
theorem sOf_pos (hD : 16 ≤ D) : (0 : ℝ) < sOf D := by
  linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD, sqrt_lt_sOf_add_one D]

/-- The bound `⌈s/g⌉` on the size of a piece is at least 1. -/
theorem pieceSize_pos (hD : 16 ≤ D) (hg1 : 1 ≤ g) : 0 < pieceSize D g :=
  Nat.ceil_pos.mpr (div_pos (sOf_pos hD) (by positivity))



/-- Proof of Theorem 17: "so that h ≤ ⌈ng/s⌉". -/
theorem numPieces_le (hD : 16 ≤ D) (hg1 : 1 ≤ g) :
    numPieces n D g ≤ ⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ := by
  have hsize : (0 : ℝ) < pieceSize D g := by exact_mod_cast pieceSize_pos hD hg1
  have hg : (0 : ℝ) < g := by positivity
  -- `s ≤ ⌈s/g⌉ g`
  have hs : sOf D ≤ pieceSize D g * (g : ℝ) := (div_le_iff₀ hg).mp (Nat.le_ceil _)
  apply Nat.ceil_mono
  rw [div_le_div_iff₀ hsize (sOf_pos hD)]
  calc n * sOf D ≤ n * (pieceSize D g * (g : ℝ)) := by gcongr
    _ = n * g * pieceSize D g := by ring

/-! ### Residues -/

/-- The residue of the integer `x` modulo `p`, as an element of `Fin p`. -/
def resFin (hp : p ≠ 0) (x : ℤ) : Fin p :=
  ⟨(x % (p : ℤ)).toNat, Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) x⟩

variable (hp : p ≠ 0)

/-- The residue of `x` is congruent to `x`. -/
theorem resFin_modEq (x : ℤ) : ((resFin hp x : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] := by
  grind [resFin, Int.natCast_toNat_emod, Nat.pos_of_ne_zero, Int.mod_modEq]

/-- An element of `Fin p` is congruent to `x` modulo `p` exactly if it is the residue of `x`. -/
theorem modEq_iff_eq_resFin (σ : Fin p) (x : ℤ) :
    ((σ : ℕ) : ℤ) ≡ x [ZMOD (p : ℤ)] ↔ σ = resFin hp x := by
  refine ⟨fun h => ?_, by grind [resFin_modEq]⟩
  -- Two congruent numbers in `{0, …, p − 1}` are equal.
  have hmod :=
    Int.natCast_modEq_iff.mp (h.trans (resFin_modEq hp x).symm)
  grind [Fin.ext, Nat.ModEq.eq_of_lt_of_lt]

/-! ### The arithmetic behind the two counts -/

/-- The number `⌈|S|/cap⌉` of chunks of `S` satisfies `⌈|S|/cap⌉ cap ≤ |S| + cap − 1`. -/
theorem numChunks_mul_le (S : Finset (Fin n × Fin n)) (cap : ℕ) (hcap : 1 ≤ cap) :
    numChunks S cap * cap + 1 ≤ S.card + cap := by
  rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]
  exact Nat.ceilDiv_mul_lt hcap

/-- `s + 1` exceeds `√D` by at least `1/(2√D + 1)`: since `(s + 1)²` and `D` are integers,
`1 ≤ (s + 1)² − D = (s + 1 − √D)(s + 1 + √D)`. -/
theorem one_le_gap_mul (D : ℕ) :
    1 ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) := by
  have hsq : Real.sqrt D ^ 2 = D := by simp
  have hle := sOf_le_sqrt D
  have hlt := sqrt_lt_sOf_add_one D
  have hinteger : D + 1 ≤ ((sOf D : ℝ) + 1) ^ 2 := by
    have hreal :=
      hsq ▸ pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) two_ne_zero
    have hnat : D < (sOf D + 1) ^ 2 := by exact_mod_cast hreal
    exact_mod_cast hnat
  calc 1 ≤ ((sOf D) + 1) ^ 2 - Real.sqrt D ^ 2 := by linarith
    _ = ((sOf D) + 1 - Real.sqrt D) * ((sOf D) + 1 + Real.sqrt D) := by ring
    _ ≤ ((sOf D) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) :=
        by grind [mul_le_mul_of_nonneg_left]

/-- The inequality behind "at most p + √D [...] chunks": `n² < (s + 1) ⌊n²/√D⌋ + p`.

Write `r = √D`, `x = n²/r` and `δ = s + 1 − r`.  Then
`(s + 1)⌊x⌋ > (s + 1)(x − 1) = n² + xδ − (s + 1)`, so it is enough that `xδ ≥ r/2 + 1 ≥ s + 1 − p`.
This holds because `x ≥ r³` (as `D ≤ n`), `δ ≥ 1/(2r + 1)` (as `D` is an integer) and `r ≥ 4`. -/
theorem sq_lt_mul_queryCap_add (hD : 16 ≤ D) (hDn : D ≤ n)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : n ^ 2 < (sOf D + 1) * queryCap n D + p := by
  have hs := sOf_le_sqrt D
  set r := Real.sqrt D with hr
  set δ := sOf D + 1 - r with hδ
  set x := n ^ 2 / r with hx
  have hr4 := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hxr : x * r = n ^ 2 := by grind
  have hx3 : r ^ 3 ≤ x := by
    rw [le_div_iff₀ (by linarith)]
    calc r ^ 3 * r = (r ^ 2) ^ 2 := by ring
      _ = (D : ℝ) ^ 2 := by simp_all
      _ ≤ n ^ 2 := by gcongr
  have hxδ : r / 2 + 1 ≤ x * δ := by
    refine le_of_mul_le_mul_right ?_ (show 0 < 2 * r + 1 by linarith)
    calc (r / 2 + 1) * (2 * r + 1) ≤ r ^ 3 := by
          -- `r³ ≥ 4r²` and `r² ≥ 4r`
          linarith [mul_le_mul_of_nonneg_right hr4 (sq_nonneg r),
            mul_le_mul_of_nonneg_right hr4 (show 0 ≤ r by linarith)]
      _ ≤ x * 1 := by linarith
      _ ≤ x * (δ * (2 * r + 1)) :=
          mul_le_mul_of_nonneg_left (one_le_gap_mul D) (by positivity)
      _ = x * δ * (2 * r + 1) := by ring
  have hfloor : x < queryCap n D + 1 := Nat.lt_floor_add_one _
  exact_mod_cast calc n ^ 2 = x * r := hxr.symm
      _ ≤ x * r + x * δ - ((sOf D) + 1) + r / 2 := by
          -- `s + 1 ≤ r + 1 ≤ xδ + r/2`
          linarith
      _ = ((sOf D) + 1) * (x - 1) + r / 2 := by linarith
      _ < ((sOf D) + 1) * queryCap n D + p :=
          by grind [add_lt_add_of_lt_of_le, mul_lt_mul_of_pos_left]

/-- Proof of Theorem 17: the two facts used for the count of the instances, "s ≥ √D − 1 ≥ 3√D/4
because D ≥ 16, and √D ≤ √n ≤ 2n/3 because D ≤ n and we may assume n ≥ 3". -/
theorem le_sOf_and_sqrt_le (hD : 16 ≤ D) (hDn : D ≤ n) :
    3 * Real.sqrt D / 4 ≤ (sOf D : ℝ) ∧ Real.sqrt D ≤ 2 * (n : ℝ) / 3 := by
  have hsqrtD := Real.four_le_sqrt_natCast_of_sixteen_le hD
  constructor
  · grind [sqrt_lt_sOf_add_one]
  · calc Real.sqrt D ≤ Real.sqrt n := by simp_all
      _ ≤ 2 * n / 3 := by
          -- `n = √n √n ≥ 4√n`
          linarith [mul_le_mul_of_nonneg_right (Real.four_le_sqrt_natCast_of_sixteen_le (hD.trans hDn)) (Real.sqrt_nonneg n),
            Real.mul_self_sqrt (Nat.cast_nonneg n)]

namespace TriangleInstance

variable (T : TriangleInstance ℤ n)

/-! ### The sets `W_ϱ` -/

/-- A pair lies in `W_ϱ` exactly if `ϱ` is the residue of its weight. -/
theorem mem_residueClass (hp : p ≠ 0) (ϱ : Fin p) (q : Fin n × Fin n) :
    q ∈ T.residueClass p ϱ ↔ ϱ = resFin hp (T.wAB q.1 q.2) := by
  rw [← modEq_iff_eq_resFin]
  simp [residueClass, Finset.mem_filter, Finset.mem_univ]
  tauto

/-- The sets `W_ϱ` have `n²` pairs in all. -/
theorem sum_card_residueClass (hp : p ≠ 0) :
    ∑ ϱ : Fin p, (T.residueClass p ϱ).card = n ^ 2 := by
  calc ∑ ϱ : Fin p, (T.residueClass p ϱ).card
      = ∑ ϱ : Fin p, ((Finset.univ : Finset (Fin n × Fin n)).filter
          fun q => resFin hp (T.wAB q.1 q.2) = ϱ).card := by
        refine Finset.sum_congr rfl fun ϱ _ => congrArg Finset.card ?_
        ext q
        rw [T.mem_residueClass hp]
        grind
    _ = Finset.univ.card :=
        (Finset.card_eq_sum_card_fiberwise fun _ _ => by simp).symm
    _ = n ^ 2 := by simp [sq]

/-! ### The chunks -/

/-- There are at most `p + s` chunks in all.  Each `W_ϱ` has at most `(|W_ϱ| + cap − 1)/cap` chunks,
where `cap = ⌊n²/√D⌋`, so `p + s + 1` chunks or more would need `n² ≥ (s + 1) cap + p` pairs. -/
theorem totalChunks_le_add_sOf (hD : 16 ≤ D) (hDn : D ≤ n) (hp0 : p ≠ 0)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : T.totalChunks D p ≤ p + sOf D := by
  have hsum : T.totalChunks D p * queryCap n D + p ≤ n ^ 2 + p * queryCap n D := by
    have h := Finset.sum_le_sum fun ϱ (_ : ϱ ∈ (Finset.univ : Finset _)) =>
      numChunks_mul_le (T.residueClass p ϱ) (queryCap n D) (by grind [one_le_queryCap])
    simp [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] at h
    rwa [T.sum_card_residueClass hp0] at h
  have hpairs := sq_lt_mul_queryCap_add hD hDn hp
  by_contra hmany
  have hmul : (p + sOf D + 1) * queryCap n D ≤ T.totalChunks D p * queryCap n D :=
    by simp_all [Nat.mul_le_mul_right]
  linarith

/-- Proof of Theorem 17: "There are at most p + √D ≤ 2√D chunks in all."

NOTE.  A chunk holds a whole number of pairs, at most `⌊n²/√D⌋`, so the count is at most
`p + (n² − p)/⌊n²/√D⌋`, and the second term can exceed `√D` slightly.  The printed bound is still
true, because the count is an integer, `D` is an integer and `D ≤ n` (`sq_lt_mul_queryCap_add`). -/
theorem totalChunks_le (hD : 16 ≤ D) (hDn : D ≤ n) (hp : p ∈ primesInRange D) :
    (T.totalChunks D p : ℝ) ≤ (p : ℝ) + Real.sqrt D ∧
    (p : ℝ) + Real.sqrt D ≤ 2 * Real.sqrt D := by
  obtain ⟨hprime, hge, hlt⟩ := mem_primesInRange.mp hp
  have hnat : T.totalChunks D p ≤ p + (sOf D : ℝ) := by
    exact_mod_cast T.totalChunks_le_add_sOf hD hDn hprime.ne_zero hge
  grind [sOf_le_sqrt]

/-! ### The instances -/



/-- There are as many instances as chunks times pieces. -/
theorem card_instanceIndices (D g p : ℕ) :
    (T.instanceIndices D g p).card = T.totalChunks D p * numPieces n D g := by
  unfold instanceIndices totalChunks
  rw [Finset.card_biUnion, Finset.sum_mul]
  · grind [Finset.sum_congr, Finset.card_image_of_injective, Prod.mk_right_injective, Finset.card_product, Finset.card_range]
  · intro ϱ _ ϱ' _ hne
    grind [Finset.disjoint_left]

/-- Proof of Theorem 17: "There are at most 2√D h ≤ 2√D(ng/s + 1) ≤ 4ng instances". -/
theorem card_instanceIndices_le (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hp : p ∈ primesInRange D) :
    ((T.instanceIndices D g p).card : ℝ) ≤ 4 * (n : ℝ) * (g : ℝ) := by
  obtain ⟨hs, hsqrt⟩ := le_sOf_and_sqrt_le hD hDn
  obtain ⟨hchunks, hchunks'⟩ := T.totalChunks_le hD hDn hp
  have hpieces :=
    calc numPieces n D g ≤ (⌈(n : ℝ) * (g : ℝ) / (sOf D : ℝ)⌉₊ : ℝ) := by
          exact_mod_cast numPieces_le hD hg1
      _ ≤ n * g / sOf D + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- `2√D · ng/s ≤ 8ng/3` because `s ≥ 3√D/4`, and `2√D ≤ 4n/3 ≤ 4ng/3`.
  have hmain :
      Real.sqrt D * (n * g / (sOf D)) ≤ 4 / 3 * (n * g) := by
    rw [← mul_div_assoc, div_le_iff₀ (sOf_pos hD)]
    calc Real.sqrt D * (n * g)
        = 4 / 3 * (n * g) * (3 * Real.sqrt D / 4) := by ring
      _ ≤ 4 / 3 * (n * g) * sOf D := by gcongr
  have hng : n ≤ n * (g : ℝ) :=
    by simp_all [le_mul_of_one_le_right, Nat.cast_nonneg]
  calc (T.instanceIndices D g p).card
      = T.totalChunks D p * (numPieces n D g : ℝ) := by
        rw [card_instanceIndices, Nat.cast_mul]
    _ ≤ 2 * Real.sqrt D * numPieces n D g := by gcongr; linarith
    _ ≤ 2 * Real.sqrt D * (n * g / (sOf D) + 1) := by gcongr
    _ ≤ 4 * n * g := by linarith

end TriangleInstance

/-! ### The neighborhoods in an instance -/




