/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem17.Host.InstanceData
import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters

/-!
# The host of Theorem 17: what is true of the list of its instances

Proof of Theorem 17.  A `HostData` describes the instances that the host forms after the prime has
been chosen, the answers of the solver, and the scans.  This file proves, without any program in
sight:

* the instances are well formed: pieces, chunks, query pairs and matrices have the sizes that the
  solver asks for (`Valid.piece_le`, `Valid.lo_add_le`, `Valid.length_WI`, `length_matX`, …);
* the query pair number `i` of instance `t` is `(rowOf t i, colOf t i)`, read off its place
  `a n + b` (`getD_WI`, `getD_WJ`), which is the entry at position `lo t + i` of the list of all
  pairs; every pair meets every vertex of `C` in some instance (`Valid.exists_query`);
* a query pair `(a, b)` is accepted if and only if the piece has a vertex `c` with `p ∣ S(a,b,c)`,
  where `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` is `sumAt` (`acc_iff`), and its scan succeeds if and
  only if the piece has a `c` with `S(a,b,c) = 0` (`hit_iff`);
* a zero triangle is found if and only if there is one (`found_m`; for the reduction on finite sets,
  of which `theorem_17` speaks, the same sentence is `TriangleInstance.exists_mem_acceptedPairs`,
  and neither proof uses the other);
* all scans but one fail (`sum_execs_le`);
* the parameters of Theorem 17 give valid data (`valid_of_params`).
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostData

/-- What is assumed about the data: positive sizes, a piece with its labels fits into the middle
part, and three lists of `n²` weights. -/
structure Valid (X : HostData) : Prop where
  n_pos : 1 ≤ X.n
  p_pos : 1 ≤ X.p
  q_pos : 1 ≤ X.q
  cap_pos : 1 ≤ X.cap
  qp_le : X.q * X.p ≤ X.D
  lenAB : X.AB.length = X.n * X.n
  lenBC : X.BC.length = X.n * X.n
  lenAC : X.AC.length = X.n * X.n

variable {X : HostData}

/-! ## Residues, pieces and chunks -/

/-- The prime is not 0. -/
theorem Valid.p_ne (hv : X.Valid) : X.p ≠ 0 := Nat.ne_of_gt hv.p_pos

/-- All residues are below `p`. -/
theorem Valid.rab_lt (hv : X.Valid) (i : ℕ) : X.RAB.getD i 0 < X.p := by
  rw [RAB, getD_residList]
  exact resid_lt hv.p_ne _

/-- The list of all pairs has `n²` entries. -/
theorem Valid.length_sortedIdx (hv : X.Valid) : (sortedIdx X.n X.p X.RAB).length = X.n * X.n := by
  rw [length_sortedIdx_eq, classStart_eq_sq fun i _ => hv.rab_lt i]

variable {t : ℕ}

/-- The number `t / chunkCount` of the piece of an instance `t < m` is below the number of pieces.
-/
theorem div_chunkCount_lt (ht : t < X.m) : t / X.chunkCount < X.h :=
  Nat.div_lt_of_lt_mul' ht

/-- The number `t % chunkCount` of the chunk of an instance `t < m` is below the number of chunks.
-/
theorem mod_chunkCount_lt (ht : t < X.m) : t % X.chunkCount < X.chunkCount :=
  Nat.mod_lt_of_lt_mul ht

/-- The chunk of an instance is an entry of the table of the chunks. -/
theorem chunk_mem (ht : t < X.m) : X.chunk t ∈ chunkTab X.n X.p X.cap X.RAB := by
  rw [chunk, List.getD_eq_getElem _ _ (mod_chunkCount_lt ht)]
  exact List.getElem_mem _

/-- The residue of a chunk is below `p`; a chunk has between 1 and `cap` pairs, and it ends within
the list of all pairs. -/
theorem Valid.chunk_entry (hv : X.Valid) (ht : t < X.m) :
    (X.chunk t).Fits X.n X.p X.cap :=
  chunkTab_entry hv.cap_pos (fun i _ => hv.rab_lt i) (chunk_mem ht)

/-- The residue of a chunk is below `p`. -/
theorem Valid.rho_lt (hv : X.Valid) (ht : t < X.m) : X.rho t < X.p :=
  (hv.chunk_entry ht).residue_lt

/-- A chunk has at most `cap` pairs. -/
theorem w_le_cap (X : HostData) (ht : t < X.m) : X.w t ≤ X.cap := by
  obtain ⟨rho, -, i, -, h⟩ := (mem_chunkTab _).1 (chunk_mem ht)
  rw [w, h]
  exact Nat.min_le_left _ _

/-- A chunk ends within the list of all pairs. -/
theorem Valid.lo_add_le (hv : X.Valid) (ht : t < X.m) : X.lo t + X.w t ≤ X.n * X.n :=
  (hv.chunk_entry ht).end_le

/-- A piece starts below `n`. -/
theorem Valid.c0_lt (hv : X.Valid) (ht : t < X.m) : X.c0 t < X.n :=
  (Nat.lt_ceilDiv_iff hv.q_pos).1 (div_chunkCount_lt ht)

/-- A piece has at most `q` vertices. -/
theorem len_le (X : HostData) (t : ℕ) : X.len t ≤ X.q := Nat.min_le_left _ _

/-- A piece ends within `C`. -/
theorem Valid.piece_le (hv : X.Valid) (ht : t < X.m) : X.c0 t + X.len t ≤ X.n := by
  have := hv.c0_lt ht
  grind [len]

/-- A piece with its labels fits into the middle part. -/
theorem Valid.len_mul_le (hv : X.Valid) (t : ℕ) : X.len t * X.p ≤ X.D :=
  (Nat.mul_le_mul_right _ (X.len_le t)).trans hv.qp_le

/-! ## The query pairs of an instance -/

/-- The place `a n + b` of the query pair `(a, b)` number `i` of instance `t`: the entry at position
`lo t + i` of the list of all pairs. -/
def place (X : HostData) (t i : ℕ) : ℕ := (sortedIdx X.n X.p X.RAB).getD (X.lo t + i) 0

/-- The vertex `a` of the query pair number `i` of instance `t`. -/
def rowOf (X : HostData) (t i : ℕ) : ℕ := X.place t i / X.n

/-- The vertex `b` of the query pair number `i` of instance `t`. -/
def colOf (X : HostData) (t i : ℕ) : ℕ := X.place t i % X.n

variable {i : ℕ}

/-- The rows of the query pairs, as the host lists them. -/
theorem getD_WI (hi : i < X.w t) : (X.WI t).getD i 0 = X.rowOf t i := by
  rw [WI, List.getD_take_of_lt _ hi, QI, queryRows, rowOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (· / X.n)

/-- The columns of the query pairs, as the host lists them. -/
theorem getD_WJ (hi : i < X.w t) : (X.WJ t).getD i 0 = X.colOf t i := by
  rw [WJ, List.getD_take_of_lt _ hi, QJ, queryCols, colOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (· % X.n)

/-- A place is below `n²`. -/
theorem Valid.place_lt (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
    X.place t i < X.n * X.n := by
  have hend := hv.lo_add_le ht
  have hlen := hv.length_sortedIdx
  rw [place, List.getD_eq_getElem _ _ (by omega)]
  exact lt_of_mem_sortedIdx (List.getElem_mem _)

/-- The row of a query pair is a vertex of `A`. -/
theorem Valid.rowOf_lt (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
    X.rowOf t i < X.n := Nat.div_lt_of_lt_mul' (hv.place_lt ht hi)

/-- The column of a query pair is a vertex of `B`. -/
theorem Valid.colOf_lt (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
    X.colOf t i < X.n := Nat.mod_lt_of_lt_mul (hv.place_lt ht hi)

/-- The pair gives the place back. -/
theorem rowOf_mul_add_colOf (X : HostData) (t i : ℕ) :
    X.rowOf t i * X.n + X.colOf t i = X.place t i := Nat.div_add_mod' _ _

/-- The weight `w(a,b)` of a query pair has the residue of its chunk. -/
theorem Valid.rab_place (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
    X.RAB.getD (X.place t i) 0 = X.rho t := chunkTab_class (chunk_mem ht) hi

/-- The query pairs of an instance, from the places. -/
theorem zip_eq (X : HostData) (t : ℕ) :
    (X.WI t).zip (X.WJ t) =
      (((sortedIdx X.n X.p X.RAB).drop (X.lo t)).take (X.w t)).map fun s => (s / X.n, s % X.n) := by
  rw [WI, WJ, QI, QJ, queryRows, queryCols, ← List.map_drop, ← List.map_drop, ← List.map_take,
    ← List.map_take, List.zip_map']

/-- No query pair is listed twice. -/
theorem nodup_zip (X : HostData) (t : ℕ) : ((X.WI t).zip (X.WJ t)).Nodup := by
  grind [zip_eq, sortedIdx_nodup, List.take_sublist, Prod.mk.injEq, Nat.div_add_mod]

variable {a : ℕ}

/-- The rows of the query pairs are vertices of `A`. -/
theorem lt_of_mem_WI (ha : a ∈ X.WI t) : a < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  exact Nat.div_lt_of_lt_mul' (lt_of_mem_sortedIdx hs)

variable {b : ℕ}

/-- The columns of the query pairs are vertices of `B`. -/
theorem lt_of_mem_WJ (hb : b ∈ X.WJ t) : b < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  exact Nat.mod_lt_of_lt_mul (lt_of_mem_sortedIdx hs)

/-- The list of the rows of all pairs has `n²` entries. -/
theorem Valid.length_QI (hv : X.Valid) : X.QI.length = X.n * X.n := by
  rw [QI, queryRows, List.length_map, hv.length_sortedIdx]

/-- The list of the columns of all pairs has `n²` entries. -/
theorem Valid.length_QJ (hv : X.Valid) : X.QJ.length = X.n * X.n := by
  rw [QJ, queryCols, List.length_map, hv.length_sortedIdx]

/-- An instance lists the row of each of its query pairs. -/
theorem Valid.length_WI (hv : X.Valid) (ht : t < X.m) : (X.WI t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WI, List.length_take, List.length_drop, hv.length_QI]
  omega

/-- An instance lists the column of each of its query pairs. -/
theorem Valid.length_WJ (hv : X.Valid) (ht : t < X.m) : (X.WJ t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WJ, List.length_take, List.length_drop, hv.length_QJ]
  omega

/-! ## The two matrices of an instance -/

/-- The matrix `X` has `n` rows and `D` columns. -/
theorem length_matX (X : HostData) (t : ℕ) : (X.matX t).length = X.n * X.D := by simp [matX, xList]

/-- The matrix `Y` has `D` rows and `n` columns. -/
theorem length_matY (X : HostData) (t : ℕ) : (X.matY t).length = X.D * X.n := by simp [matY, yList]

/-- The entries of `X` are 0 and 1. -/
theorem matX_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matX t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  omega

/-- The entries of `Y` are 0 and 1. -/
theorem matY_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matY t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  omega

/-- Every place stands at some position of the list of all pairs. -/
theorem Valid.exists_getD_sortedIdx (hv : X.Valid) {s : ℕ} (hs : s < X.n * X.n) :
    ∃ j < X.n * X.n, (sortedIdx X.n X.p X.RAB).getD j 0 = s := by
  have hmem : s ∈ sortedIdx X.n X.p X.RAB :=
    List.mem_flatMap.2 ⟨X.RAB.getD s 0, List.mem_range.2 (hv.rab_lt s), mem_classIdx.2 ⟨hs, rfl⟩⟩
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hmem
  exact ⟨j, hv.length_sortedIdx ▸ hj, by simp_all⟩

/-- Proof of Theorem 17, "its c lies in some piece": every pair `(a, b)` is a query pair of an
instance whose piece contains a given vertex `c`. -/
theorem Valid.exists_query (hv : X.Valid) {c : ℕ} (ha : a < X.n) (hb : b < X.n)
    (hc : c < X.n) :
    ∃ t < X.m, ∃ i < X.w t,
      X.rowOf t i = a ∧ X.colOf t i = b ∧ ∃ c' < X.len t, X.c0 t + c' = c := by
  -- The position `j` of the pair in the list of all pairs, and the chunk `k` of that position.
  obtain ⟨j, hj, hplace⟩ := hv.exists_getD_sortedIdx (Nat.mul_add_lt_mul ha hb)
  obtain ⟨y, hy, hlo, hhi⟩ := chunkTab_cover hv.cap_pos (fun i _ => hv.rab_lt i) hj
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  -- The instance of that chunk and of the piece of `c`.
  obtain ⟨t, ht, hdiv, hmod⟩ : ∃ t < X.m, t / X.chunkCount = c / X.q ∧ t % X.chunkCount = k :=
    ⟨_, Nat.mul_add_lt_mul ((Nat.lt_ceilDiv_iff hv.q_pos).2 (lt_of_le_of_lt (Nat.div_mul_le_self c X.q) hc)) hk, Nat.mul_add_div_of_lt hk, Nat.mul_add_mod_of_lt hk⟩
  have hentry : X.chunk t = (chunkTab X.n X.p X.cap X.RAB)[k] := by
    rw [chunk, hmod]
    exact List.getD_eq_getElem _ _ hk
  have hlo' : X.lo t ≤ j := by grind [lo]
  have hhi' : j < X.lo t + X.w t := by grind [lo, w]
  have hpair : X.place t (j - X.lo t) = a * X.n + b := by
    grind [place]
  have hdivmod := c.div_add_mod' X.q
  refine ⟨t, ht, j - X.lo t, by omega, ?_, ?_, c % X.q, ?_, ?_⟩
  · grind [rowOf, Nat.mul_add_div_of_lt]
  · grind [colOf, Nat.mul_add_mod_of_lt]
  · have := c.mod_lt hv.q_pos
    grind [len, c0]
  grind [c0]

/-! ## Acceptance -/

/-- The weight `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` of the triangle `(a, b, c)`, read from the
three lists. -/
def sumAt (X : HostData) (a b c : ℕ) : ℤ :=
  X.AB.getD (a * X.n + b) 0 + X.BC.getD (b * X.n + c) 0 + X.AC.getD (a * X.n + c) 0

/-- A sum of numbers that are 0 or 1 is not 0 if and only if one of them is 1. -/
theorem sum_ne_zero_iff (f : ℕ → ℤ) (N : ℕ) (h01 : ∀ k < N, f k = 0 ∨ f k = 1) :
    ((List.range N).map f).sum ≠ 0 ↔ ∃ k < N, f k = 1 := by
  grind [List.sum_map_range, Finset.sum_eq_zero_iff_of_nonneg]

variable {p : ℕ}

/-- Proof of Theorem 17: "the condition S(a,b,c) ≡ 0 (mod p) has become the equality w(a,c) + ϱ ≡
−w(b,c) of a label of (a,c) and a label of (b,c)".  Here `wAC`, `wAB` and `wBC` are the three
weights, and `ϱ` is the residue of `wAB`. -/
theorem labels_eq_iff (hp : p ≠ 0) (wAC wAB wBC : ℤ) :
    (resid p wAC + resid p wAB) % p = (p - resid p wBC) % p ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
  have hleft : resid p wAC + resid p wAB ≡ wAC + wAB [ZMOD p] := by
    rw [resid_cast hp, resid_cast hp]
    exact (Int.mod_modEq wAC p).add (Int.mod_modEq wAB p)
  have hright : (p - resid p wBC : ℕ) ≡ -wBC [ZMOD p] := by
    rw [Nat.cast_sub (resid_lt hp wBC).le, resid_cast hp]
    simpa using (Int.modEq_zero_iff_dvd.2 (by simp)).sub (Int.mod_modEq wBC p)
  have hiff : wAC + wAB ≡ -wBC [ZMOD p] ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
    rw [Int.modEq_iff_dvd, ← dvd_neg, show -(-wBC - (wAC + wAB)) = wAB + wBC + wAC by ring]
  rw [← hiff, ← Nat.ModEq, ← Int.natCast_modEq_iff]
  exact ⟨fun h => (hleft.symm.trans h).trans hright, fun h => (hleft.trans h).trans hright.symm⟩

variable {n D len rho c0 k : ℕ} {RAC : List ℕ}

/-- An entry of the matrix `X` of an instance. -/
theorem getD_xList (ha : a < n)
    (hk : k < D) :
    (xList n D p c0 len rho RAC).getD (a * D + k) 0 =
      if k / p < len ∧ k % p = (RAC.getD (a * n + c0 + k / p) 0 + rho) % p then 1 else 0 := by
  grind [xList, List.getD_map_range, Nat.mul_add_lt_mul, Nat.mul_add_mod_of_lt, Nat.mul_add_div_of_lt]

variable {RBC : List ℕ}

/-- An entry of the matrix `Y` of an instance. -/
theorem getD_yList (hb : b < n) (hk : k < D) :
    (yList n D p c0 len RBC).getD (k * n + b) 0 =
      if k / p < len ∧ k % p = (p - RBC.getD (b * n + c0 + k / p) 0) % p then 1 else 0 := by
  grind [yList, List.getD_map_range, Nat.mul_add_lt_mul, Nat.mul_add_mod_of_lt, Nat.mul_add_div_of_lt]

/-- The entry `(XY)[a, b]` of an instance is not 0 if and only if the labels of `a` and `b` agree at
some vertex of the piece. -/
theorem thinEntry_ne_zero_iff     (hp : p ≠ 0) (hlen : len * p ≤ D) (ha : a < n) (hb : b < n) :
    thinEntry n D (xList n D p c0 len rho RAC) (yList n D p c0 len RBC) a b ≠ 0 ↔
      ∃ c < len,
        (RAC.getD (a * n + c0 + c) 0 + rho) % p = (p - RBC.getD (b * n + c0 + c) 0) % p := by
  rw [thinEntry, sum_ne_zero_iff]
  · constructor
    · -- The column `k` is the middle vertex `(c, σ)` with `c = k / p` and `σ = k % p`.
      grind [getD_xList, getD_yList]
    · -- The middle vertex `(c, σ)` with the common label `σ` is the column `c p + σ`.
      rintro ⟨c, hc, hlabel⟩
      have hσ : (RAC.getD (a * n + c0 + c) 0 + rho) % p < p := Nat.mod_lt _ (Nat.pos_of_ne_zero hp)
      have hk := (Nat.mul_add_lt_mul hc hσ).trans_le hlen
      refine ⟨_, hk, ?_⟩
      rw [getD_xList ha hk, getD_yList hb hk, Nat.mul_add_div_of_lt hσ, Nat.mul_add_mod_of_lt hσ,
        if_pos ⟨hc, rfl⟩, if_pos ⟨hc, hlabel⟩, mul_one]
  grind [getD_xList, getD_yList]

/-- The answer of the solver for a query pair: 1 if `(XY)[a, b] ≠ 0`, and 0 otherwise. -/
theorem Valid.getD_ans (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
    (X.ans t).getD i 0 =
      if thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) = 0 then 0 else 1 := by
  have hiI : i < (X.WI t).length := by rw [hv.length_WI ht]; assumption
  have hiJ : i < (X.WJ t).length := by rw [hv.length_WJ ht]; assumption
  rw [← getD_WI hi, ← getD_WJ hi, ans, thinOut, List.getD_eq_getElem _ _ (by simp_all),
    List.getElem_map, List.getElem_map, List.getElem_zip, List.getD_eq_getElem _,
    List.getD_eq_getElem _]

/-- Proof of Theorem 17: "a query pair (a,b) ∈ 𝒬 has a common neighbor if and only if some c ∈ C_k
has S(a,b,c) ≡ 0 (mod p)". -/
theorem acc_iff (hv : X.Valid) (ht : t < X.m) (hi : i < X.w t) :
    X.acc t i = true ↔
      ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) := by
  have hentry : X.acc t i = true ↔
      thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) ≠ 0 := by
    rw [acc, decide_eq_true_eq, hv.getD_ans ht hi]
    omega
  rw [hentry, matX, matY, thinEntry_ne_zero_iff hv.p_ne (hv.len_mul_le t) (hv.rowOf_lt ht hi)
    (hv.colOf_lt ht hi)]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [RAC, RBC, getD_residList, getD_residList, ← hv.rab_place ht hi, RAB, getD_residList,
    labels_eq_iff hv.p_ne, ← rowOf_mul_add_colOf, sumAt, Nat.add_assoc, Nat.add_assoc]

/-- Proof of Theorem 17, "scan the piece C_k of its instance for a c with S(a,b,c) = 0": when the
scan succeeds.
-/
theorem hit_iff (hi : i < X.w t) :
    X.hit t i = true ↔ ∃ c < X.len t, X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) = 0 := by
  rw [hit, getD_WI hi, getD_WJ hi]
  simp [scanHit, sumAt, Nat.add_assoc]

/-! ## Correctness -/

/-- Brute force finds a zero triangle if and only if there is one. -/
theorem hasZero_iff_sumAt (X : HostData) :
    hasZero X.n X.AB X.BC X.AC = true ↔ ∃ a < X.n, ∃ b < X.n, ∃ c < X.n, X.sumAt a b c = 0 := by
  simp [hasZero, scanHit, sumAt]

/-- A zero triangle has been found before instance `T` if and only if some accepted query pair of an
earlier instance has a successful scan. -/
theorem found_iff (X : HostData) (T : ℕ) :
    X.found T = true ↔ ∃ t < T, ∃ i < X.w t, X.acc t i = true ∧ X.hit t i = true := by
  induction T with
  | zero => aesop
  | succ T ih =>
    grind [found, foundAt]

/-- Proof of Theorem 17: "A zero triangle is always found, since its c lies in some piece and makes
the oracle accept its pair."  After all instances a zero triangle has been found if and only if
there is one.
-/
theorem found_m (hv : X.Valid) : X.found X.m = hasZero X.n X.AB X.BC X.AC := by
  rw [Bool.eq_iff_iff, found_iff, hasZero_iff_sumAt]
  constructor
  · rintro ⟨t, ht, i, hi, -, hhit⟩
    obtain ⟨c, hc, hzero⟩ := (hit_iff hi).1 hhit
    have hpiece := hv.piece_le ht
    exact ⟨_, hv.rowOf_lt ht hi, _, hv.colOf_lt ht hi, _, by omega, hzero⟩
  · rintro ⟨a, ha, b, hb, c, hc, hzero⟩
    obtain ⟨t, ht, i, hi, rfl, rfl, c', hc', rfl⟩ := hv.exists_query ha hb hc
    exact ⟨t, ht, i, hi, (acc_iff hv ht hi).2 ⟨c', hc', by simp_all⟩,
      by grind [hit_iff]⟩

/-- Proof of Theorem 17: "We stop as soon as a zero triangle is found", so all scans but one fail.
-/
theorem sum_execs_le (X : HostData) :
    ∑ t ∈ Finset.range X.m, X.execs t ≤ ∑ t ∈ Finset.range X.m, X.fails t + 1 := by
  have key : ∀ T, ∑ t ∈ Finset.range T, X.execs t
      ≤ ∑ t ∈ Finset.range T, X.fails t + (X.found T).toNat := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have hstep : X.execs T + (X.found T).toNat ≤ X.fails T + (X.found (T + 1)).toNat :=
        execsUpto_le _ _ _ _
      grind [Finset.sum_range_succ]
  grind [Bool.toNat_le]

/-- The parameters of Theorem 17 give valid data. -/
theorem valid_of_params {g : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) (lenAB : AB.length = n * n) (lenBC : BC.length = n * n)
    (lenAC : AC.length = n * n) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).Valid := ⟨le_trans (by norm_num) (h.sixteen_le.trans h.le_n), (mem_primesInRange.mp hp).1.one_le, by
    rw [pieceSizeNat_eq D h.one_le_g]
    exact (pieceSize_mul_le h.sixteen_le h.one_le_g hp).1, by
    have hD := h.sixteen_le
    have hDn := h.le_n
    rw [queryCapNat, Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]
    grind [Nat.le_self_pow], by
    rw [pieceSizeNat_eq D h.one_le_g]
    exact (pieceSize_mul_le h.sixteen_le h.one_le_g hp).2, lenAB, lenBC, lenAC⟩
