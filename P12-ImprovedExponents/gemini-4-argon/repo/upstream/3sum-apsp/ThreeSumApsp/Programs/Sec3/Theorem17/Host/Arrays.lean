module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan
public import ThreeSumApsp.Spec.Sec3.Theorem17.Chunks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.WriteMatrices
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ChoosePrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Instances.Chunks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Spec.Sec3.Theorem17.Cyclic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Reading the answers of one instance and scanning for witnesses

Proof of Theorem 17: "For every query pair that the oracle accepts, scan the piece C_k of its
instance for a c with S(a,b,c) = 0 [...].  We stop as soon as a zero triangle is found."

scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the
pair `(qa[i], qb[i])`, as long as none has been found (`f = 0`).  The result is the new value of `f`
(`scanPairs_spec`).  No scan is made after the first successful one, so the number of scans is at
most the number of failed scans plus one (`execsUpto_le`).
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- The number of accepted pairs among the first w whose scan would fail. -/
def failsUpto (acc hit : ℕ → Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter fun i => acc i && !hit i).length

theorem failsUpto_succ (acc hit : ℕ → Bool) (w : ℕ) :
    failsUpto acc hit (w + 1) = failsUpto acc hit w + (if acc w && !hit w then 1 else 0) := by
  simp only [failsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-! ## The routine -/

/-- What `scanPairs` assumes about the answers of the solver and the `w` query pairs of an instance:
three arrays in the memory, and the query pairs are pairs of vertices. -/
structure Answers (lim : Limits) (μ : ℕ → ℤ) (out qa qb w n : ℕ) (OUT : List ℤ) (QA QB : List ℕ) :
    Prop where
  arrOUT : ListAt μ out OUT w lim.space
  arrQA : IndexAt μ qa QA w n lim.space
  arrQB : IndexAt μ qb QB w n lim.space
  w_lt : w < lim.space

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {f : Bool}

/-- The answer for the query pair number `i` is not 0. -/
abbrev accOf (OUT : List ℤ) (i : ℕ) : Bool := decide (OUT.getD i 0 ≠ 0)

/-- The scan for the query pair number `i` succeeds. -/
abbrev hitOf (n : ℕ) (AB BC AC : List ℤ) (QA QB : List ℕ) (c0 len i : ℕ) : Bool :=
  scanHit n AB BC AC (QA.getD i 0) (QB.getD i 0) c0 len

end


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The host of Theorem 17: the list of its instances, as pure data

Proof of Theorem 17, "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k form the instance".  After the prime
has been chosen, the host runs one loop over all instances: instance number `t` belongs to the piece
number `t / chunkCount` of `C` and to the chunk number `t % chunkCount` of the table of chunks.
This file defines what the host writes (`matX`, `matY`, `WI`, `WJ`), what the solver answers
(`ans`), which query pairs are accepted and which scans succeed (`acc`, `hit`), and whether a zero
triangle has been found before instance `t` (`found`).  The class of a residue `ϱ < p` is the
paper's `W_ϱ`: the pairs `(a, b)` whose weight is congruent to `ϱ` modulo `p`.  The pairs are listed
class after class, in the order of the residues, and a chunk is a segment of a class.
-/




/-- The hypotheses of Theorem 17 on its parameters, in natural numbers: "Let 16 ≤ D ≤ n, and let
1 ≤ g ≤ √D be an integer." -/
structure BigCase (n D g : ℕ) : Prop where
  sixteen_le : 16 ≤ D
  le_n : D ≤ n
  one_le_g : 1 ≤ g
  g_le_sqrt : g ≤ Nat.sqrt D

/-- The data on which the loop over the instances depends. -/
structure HostData : Type where
  /-- The number of vertices of each part. -/
  n : ℕ
  /-- The bound on the number of middle vertices of an instance of Lop-AE-SparseTri, that is, the
  inner dimension of its matrices `X` and `Y`. -/
  D : ℕ
  /-- The prime. -/
  p : ℕ
  /-- The number of vertices of a piece of `C`. -/
  q : ℕ
  /-- The largest number of query pairs of an instance. -/
  cap : ℕ
  /-- The weights of the edges `(a, b)`, row by row. -/
  AB : List ℤ
  /-- The weights of the edges `(b, c)`, row by row. -/
  BC : List ℤ
  /-- The weights of the edges `(a, c)`, row by row. -/
  AC : List ℤ

namespace HostData

variable (X : HostData)

/-- The residues modulo `p` of the weights of the edges `(a, b)`. -/
def RAB : List ℕ := residList X.p X.AB
/-- The residues modulo `p` of the weights of the edges `(b, c)`. -/
def RBC : List ℕ := residList X.p X.BC
/-- The residues modulo `p` of the weights of the edges `(a, c)`. -/
def RAC : List ℕ := residList X.p X.AC
/-- The rows `a` of all pairs `(a, b)`, class after class. -/
def QI : List ℕ := queryRows X.n X.p X.RAB
/-- The columns `b` of all pairs `(a, b)`, class after class. -/
def QJ : List ℕ := queryCols X.n X.p X.RAB
/-- The table of the chunks. -/
def CT : List Chunk := chunkTab X.n X.p X.cap X.RAB
/-- The number of chunks. -/
def chunkCount : ℕ := X.CT.length
/-- The number of pieces. -/
def h : ℕ := X.n ⌈/⌉ X.q
/-- The number of instances. -/
def m : ℕ := X.h * X.chunkCount

/-- The first vertex of the piece of instance t. -/
def c0 (t : ℕ) : ℕ := t / X.chunkCount * X.q
/-- The number of vertices of the piece of instance t. -/
def len (t : ℕ) : ℕ := min X.q (X.n - X.c0 t)
/-- The chunk of instance t. -/
def chunk (t : ℕ) : Chunk := X.CT.getD (t % X.chunkCount) ⟨0, 0, 0⟩
/-- The residue `ϱ` of the chunk of instance t. -/
def rho (t : ℕ) : ℕ := (X.chunk t).residue
/-- The first place of the chunk of instance t in the list of all pairs. -/
def lo (t : ℕ) : ℕ := (X.chunk t).start
/-- The number of query pairs of instance t. -/
def w (t : ℕ) : ℕ := (X.chunk t).len

/-- The matrix `X` of instance t. -/
def matX (t : ℕ) : List ℤ := xList X.n X.D X.p (X.c0 t) (X.len t) (X.rho t) X.RAC
/-- The matrix `Y` of instance t. -/
def matY (t : ℕ) : List ℤ := yList X.n X.D X.p (X.c0 t) (X.len t) X.RBC
/-- The rows of the query pairs of instance t. -/
def WI (t : ℕ) : List ℕ := (X.QI.drop (X.lo t)).take (X.w t)
/-- The columns of the query pairs of instance t. -/
def WJ (t : ℕ) : List ℕ := (X.QJ.drop (X.lo t)).take (X.w t)

/-- The answers of a solver of Lop-AE-SparseTri to instance t. -/
def ans (t : ℕ) : List ℤ :=
  (thinOut X.n X.D (X.matX t) (X.matY t) (X.WI t) (X.WJ t)).map fun v => if v = 0 then 0 else 1

/-- The query pair number i of instance t is accepted. -/
def acc (t i : ℕ) : Bool := decide ((X.ans t).getD i 0 ≠ 0)
/-- The scan for the query pair number i of instance t succeeds. -/
def hit (t i : ℕ) : Bool :=
  scanHit X.n X.AB X.BC X.AC ((X.WI t).getD i 0) ((X.WJ t).getD i 0) (X.c0 t) (X.len t)

/-- The number of accepted query pairs of instance t whose scan fails or would fail. -/
def fails (t : ℕ) : ℕ := failsUpto (X.acc t) (X.hit t) (X.w t)

end HostData

end Light.Sec3
end

section
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

/-- The number `t / chunkCount` of the piece of an instance `t < m` is below the number of pieces.
-/
theorem div_chunkCount_lt {t : ℕ} (ht : t < X.m) : t / X.chunkCount < X.h :=
  Nat.div_lt_of_lt_mul' ht

/-- The number `t % chunkCount` of the chunk of an instance `t < m` is below the number of chunks.
-/
theorem mod_chunkCount_lt {t : ℕ} (ht : t < X.m) : t % X.chunkCount < X.chunkCount :=
  Nat.mod_lt_of_lt_mul ht

/-- The chunk of an instance is an entry of the table of the chunks. -/
theorem chunk_mem {t : ℕ} (ht : t < X.m) : X.chunk t ∈ chunkTab X.n X.p X.cap X.RAB := by
  rw [chunk, List.getD_eq_getElem _ _ (mod_chunkCount_lt ht)]
  exact List.getElem_mem _

/-- The residue of a chunk is below `p`; a chunk has between 1 and `cap` pairs, and it ends within
the list of all pairs. -/
theorem Valid.chunk_entry (hv : X.Valid) {t : ℕ} (ht : t < X.m) :
    (X.chunk t).Fits X.n X.p X.cap :=
  chunkTab_entry hv.cap_pos (fun i _ => hv.rab_lt i) (chunk_mem ht)

/-- The residue of a chunk is below `p`. -/
theorem Valid.rho_lt (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.rho t < X.p :=
  (hv.chunk_entry ht).residue_lt

/-- A chunk has at most `cap` pairs. -/
theorem w_le_cap (X : HostData) {t : ℕ} (ht : t < X.m) : X.w t ≤ X.cap := by
  obtain ⟨rho, -, i, -, h⟩ := (mem_chunkTab _).1 (chunk_mem ht)
  rw [w, h]
  exact Nat.min_le_left _ _

/-- A chunk ends within the list of all pairs. -/
theorem Valid.lo_add_le (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.lo t + X.w t ≤ X.n * X.n :=
  (hv.chunk_entry ht).end_le

/-- A piece starts below `n`. -/
theorem Valid.c0_lt (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.c0 t < X.n :=
  (Nat.lt_ceilDiv_iff hv.q_pos).1 (div_chunkCount_lt ht)

/-- A piece has at most `q` vertices. -/
theorem len_le (X : HostData) (t : ℕ) : X.len t ≤ X.q := Nat.min_le_left _ _

/-- A piece ends within `C`. -/
theorem Valid.piece_le (hv : X.Valid) {t : ℕ} (ht : t < X.m) : X.c0 t + X.len t ≤ X.n := by
  have := hv.c0_lt ht
  rw [len]
  omega

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

/-- The rows of the query pairs, as the host lists them. -/
theorem getD_WI {t i : ℕ} (hi : i < X.w t) : (X.WI t).getD i 0 = X.rowOf t i := by
  rw [WI, List.getD_take_of_lt _ hi, List.getD_drop, QI, queryRows, rowOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (n := X.lo t + i) (· / X.n)

/-- The columns of the query pairs, as the host lists them. -/
theorem getD_WJ {t i : ℕ} (hi : i < X.w t) : (X.WJ t).getD i 0 = X.colOf t i := by
  rw [WJ, List.getD_take_of_lt _ hi, List.getD_drop, QJ, queryCols, colOf, place]
  simpa using List.getD_map (l := sortedIdx X.n X.p X.RAB) (d := 0) (n := X.lo t + i) (· % X.n)

/-- A place is below `n²`. -/
theorem Valid.place_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.place t i < X.n * X.n := by
  have := hv.lo_add_le ht
  have := hv.length_sortedIdx
  rw [place, List.getD_eq_getElem _ _ (by omega)]
  exact lt_of_mem_sortedIdx (List.getElem_mem _)

/-- The row of a query pair is a vertex of `A`. -/
theorem Valid.rowOf_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.rowOf t i < X.n := Nat.div_lt_of_lt_mul' (hv.place_lt ht hi)

/-- The column of a query pair is a vertex of `B`. -/
theorem Valid.colOf_lt (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.colOf t i < X.n := Nat.mod_lt_of_lt_mul (hv.place_lt ht hi)

/-- The pair gives the place back. -/
theorem rowOf_mul_add_colOf (X : HostData) (t i : ℕ) :
    X.rowOf t i * X.n + X.colOf t i = X.place t i := Nat.div_add_mod' _ _

/-- The weight `w(a,b)` of a query pair has the residue of its chunk. -/
theorem Valid.rab_place (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.RAB.getD (X.place t i) 0 = X.rho t := chunkTab_class hv.cap_pos (chunk_mem ht) hi


/-- The rows of the query pairs are vertices of `A`. -/
theorem lt_of_mem_WI {t a : ℕ} (ha : a ∈ X.WI t) : a < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  exact Nat.div_lt_of_lt_mul' (lt_of_mem_sortedIdx hs)

/-- The columns of the query pairs are vertices of `B`. -/
theorem lt_of_mem_WJ {t b : ℕ} (hb : b ∈ X.WJ t) : b < X.n := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  exact Nat.mod_lt_of_lt_mul (lt_of_mem_sortedIdx hs)

/-- The list of the rows of all pairs has `n²` entries. -/
theorem Valid.length_QI (hv : X.Valid) : X.QI.length = X.n * X.n := by
  rw [QI, queryRows, List.length_map, hv.length_sortedIdx]

/-- The list of the columns of all pairs has `n²` entries. -/
theorem Valid.length_QJ (hv : X.Valid) : X.QJ.length = X.n * X.n := by
  rw [QJ, queryCols, List.length_map, hv.length_sortedIdx]

/-- An instance lists the row of each of its query pairs. -/
theorem Valid.length_WI (hv : X.Valid) {t : ℕ} (ht : t < X.m) : (X.WI t).length = X.w t := by
  have := hv.lo_add_le ht
  rw [WI, List.length_take, List.length_drop, hv.length_QI]
  omega

/-- An instance lists the column of each of its query pairs. -/
theorem Valid.length_WJ (hv : X.Valid) {t : ℕ} (ht : t < X.m) : (X.WJ t).length = X.w t := by
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
  exact (ite_eq_or_eq _ _ _).symm

/-- The entries of `Y` are 0 and 1. -/
theorem matY_zero_or_one (X : HostData) (t : ℕ) : ∀ e ∈ X.matY t, e = 0 ∨ e = 1 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  exact (ite_eq_or_eq _ _ _).symm

/-- Every place stands at some position of the list of all pairs. -/
theorem Valid.exists_getD_sortedIdx (hv : X.Valid) {s : ℕ} (hs : s < X.n * X.n) :
    ∃ j < X.n * X.n, (sortedIdx X.n X.p X.RAB).getD j 0 = s := by
  have hmem : s ∈ sortedIdx X.n X.p X.RAB :=
    List.mem_flatMap.2 ⟨X.RAB.getD s 0, List.mem_range.2 (hv.rab_lt s), mem_classIdx.2 ⟨hs, rfl⟩⟩
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hmem
  exact ⟨j, hv.length_sortedIdx ▸ hj, (List.getD_eq_getElem _ _ hj).trans hjs⟩

/-- Proof of Theorem 17, "its c lies in some piece": every pair `(a, b)` is a query pair of an
instance whose piece contains a given vertex `c`. -/
theorem Valid.exists_query (hv : X.Valid) {a b c : ℕ} (ha : a < X.n) (hb : b < X.n)
    (hc : c < X.n) :
    ∃ t < X.m, ∃ i < X.w t,
      X.rowOf t i = a ∧ X.colOf t i = b ∧ ∃ c' < X.len t, X.c0 t + c' = c := by
  -- The position `j` of the pair in the list of all pairs, and the chunk `k` of that position.
  obtain ⟨j, hj, hplace⟩ := hv.exists_getD_sortedIdx (Nat.mul_add_lt_mul ha hb)
  obtain ⟨y, hy, hlo, hhi⟩ := chunkTab_cover hv.cap_pos (fun i _ => hv.rab_lt i) hj
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  -- The instance of that chunk and of the piece of `c`.
  have hpiece : c / X.q < X.h :=
    (Nat.lt_ceilDiv_iff hv.q_pos).2 (lt_of_le_of_lt (Nat.div_mul_le_self c X.q) hc)
  obtain ⟨t, ht, hdiv, hmod⟩ : ∃ t < X.m, t / X.chunkCount = c / X.q ∧ t % X.chunkCount = k :=
    ⟨_, Nat.mul_add_lt_mul hpiece hk, Nat.mul_add_div_of_lt hk, Nat.mul_add_mod_of_lt hk⟩
  have hentry : X.chunk t = (chunkTab X.n X.p X.cap X.RAB)[k] := by
    rw [chunk, hmod]
    exact List.getD_eq_getElem _ _ hk
  have hlo' : X.lo t ≤ j := by rw [lo, hentry]; exact hlo
  have : j < X.lo t + X.w t := by rw [lo, w, hentry]; exact hhi
  have hpair : X.place t (j - X.lo t) = a * X.n + b := by
    rw [place, Nat.add_sub_cancel' hlo', hplace]
  have hdivmod := Nat.div_add_mod' c X.q
  refine ⟨t, ht, j - X.lo t, by omega, ?_, ?_, c % X.q, ?_, ?_⟩
  · rw [rowOf, hpair, Nat.mul_add_div_of_lt hb]
  · rw [colOf, hpair, Nat.mul_add_mod_of_lt hb]
  · have := Nat.mod_lt c hv.q_pos
    rw [len, c0, hdiv]
    omega
  · rw [c0, hdiv, hdivmod]

/-! ## Acceptance -/

/-- The weight `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` of the triangle `(a, b, c)`, read from the
three lists. -/
def sumAt (X : HostData) (a b c : ℕ) : ℤ :=
  X.AB.getD (a * X.n + b) 0 + X.BC.getD (b * X.n + c) 0 + X.AC.getD (a * X.n + c) 0

/-- A sum of numbers that are 0 or 1 is not 0 if and only if one of them is 1. -/
theorem sum_ne_zero_iff (f : ℕ → ℤ) (N : ℕ) (h01 : ∀ k < N, f k = 0 ∨ f k = 1) :
    ((List.range N).map f).sum ≠ 0 ↔ ∃ k < N, f k = 1 := by
  have hnonneg : ∀ k ∈ Finset.range N, 0 ≤ f k := fun k hk => by
    rcases h01 k (Finset.mem_range.1 hk) with h | h <;> omega
  rw [List.sum_map_range, Ne, Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro hne
    by_contra hnone
    exact hne fun k hk => (h01 k (Finset.mem_range.1 hk)).resolve_right
      fun hone => hnone ⟨k, Finset.mem_range.1 hk, hone⟩
  · rintro ⟨k, hk, hone⟩ hall
    have := hall k (Finset.mem_range.2 hk)
    omega

/-- Proof of Theorem 17: "the condition S(a,b,c) ≡ 0 (mod p) has become the equality w(a,c) + ϱ ≡
−w(b,c) of a label of (a,c) and a label of (b,c)".  Here `wAC`, `wAB` and `wBC` are the three
weights, and `ϱ` is the residue of `wAB`. -/
theorem labels_eq_iff {p : ℕ} (hp : p ≠ 0) (wAC wAB wBC : ℤ) :
    (resid p wAC + resid p wAB) % p = (p - resid p wBC) % p ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
  have hleft : ((resid p wAC + resid p wAB : ℕ) : ℤ) ≡ wAC + wAB [ZMOD (p : ℤ)] := by
    push_cast
    rw [resid_cast hp, resid_cast hp]
    exact (Int.mod_modEq wAC p).add (Int.mod_modEq wAB p)
  have hright : ((p - resid p wBC : ℕ) : ℤ) ≡ -wBC [ZMOD (p : ℤ)] := by
    rw [Nat.cast_sub (resid_lt hp wBC).le, resid_cast hp]
    simpa using (Int.modEq_zero_iff_dvd.2 (dvd_refl (p : ℤ))).sub (Int.mod_modEq wBC p)
  have hiff : wAC + wAB ≡ -wBC [ZMOD (p : ℤ)] ↔ (p : ℤ) ∣ wAB + wBC + wAC := by
    rw [Int.modEq_iff_dvd, ← dvd_neg, show -(-wBC - (wAC + wAB)) = wAB + wBC + wAC by ring]
  rw [← hiff, ← Nat.ModEq, ← Int.natCast_modEq_iff]
  exact ⟨fun h => (hleft.symm.trans h).trans hright, fun h => (hleft.trans h).trans hright.symm⟩

/-- An entry of the matrix `X` of an instance. -/
theorem getD_xList {n D p c0 len rho : ℕ} {RAC : List ℕ} {a k : ℕ} (ha : a < n)
    (hk : k < D) :
    (xList n D p c0 len rho RAC).getD (a * D + k) 0 =
      if k / p < len ∧ k % p = (RAC.getD (a * n + c0 + k / p) 0 + rho) % p then 1 else 0 := by
  rw [xList, List.getD_map_range _ (Nat.mul_add_lt_mul ha hk), Nat.mul_add_mod_of_lt hk,
    Nat.mul_add_div_of_lt hk]

/-- An entry of the matrix `Y` of an instance. -/
theorem getD_yList {n D p c0 len : ℕ} {RBC : List ℕ} {b k : ℕ} (hb : b < n) (hk : k < D) :
    (yList n D p c0 len RBC).getD (k * n + b) 0 =
      if k / p < len ∧ k % p = (p - RBC.getD (b * n + c0 + k / p) 0) % p then 1 else 0 := by
  rw [yList, List.getD_map_range _ (Nat.mul_add_lt_mul hk hb), Nat.mul_add_mod_of_lt hb,
    Nat.mul_add_div_of_lt hb]

/-- The entry `(XY)[a, b]` of an instance is not 0 if and only if the labels of `a` and `b` agree at
some vertex of the piece. -/
theorem thinEntry_ne_zero_iff {n D p c0 len rho : ℕ} {RAC RBC : List ℕ} {a b : ℕ}
    (hp : p ≠ 0) (hlen : len * p ≤ D) (ha : a < n) (hb : b < n) :
    thinEntry n D (xList n D p c0 len rho RAC) (yList n D p c0 len RBC) a b ≠ 0 ↔
      ∃ c < len,
        (RAC.getD (a * n + c0 + c) 0 + rho) % p = (p - RBC.getD (b * n + c0 + c) 0) % p := by
  rw [thinEntry, sum_ne_zero_iff]
  · constructor
    · -- The column `k` is the middle vertex `(c, σ)` with `c = k / p` and `σ = k % p`.
      rintro ⟨k, hk, hone⟩
      rw [getD_xList ha hk, getD_yList hb hk] at hone
      split_ifs at hone with hX hY
      · exact ⟨k / p, hX.1, hX.2.symm.trans hY.2⟩
      all_goals simp at hone
    · -- The middle vertex `(c, σ)` with the common label `σ` is the column `c p + σ`.
      rintro ⟨c, hc, hlabel⟩
      have hσ : (RAC.getD (a * n + c0 + c) 0 + rho) % p < p := Nat.mod_lt _ (Nat.pos_of_ne_zero hp)
      have hk := (Nat.mul_add_lt_mul hc hσ).trans_le hlen
      refine ⟨_, hk, ?_⟩
      rw [getD_xList ha hk, getD_yList hb hk, Nat.mul_add_div_of_lt hσ, Nat.mul_add_mod_of_lt hσ,
        if_pos ⟨hc, rfl⟩, if_pos ⟨hc, hlabel⟩, mul_one]
  · intro k hk
    rw [getD_xList ha hk, getD_yList hb hk]
    split_ifs <;> simp

/-- The answer of the solver for a query pair: 1 if `(XY)[a, b] ≠ 0`, and 0 otherwise. -/
theorem Valid.getD_ans (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    (X.ans t).getD i 0 =
      if thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) = 0 then 0 else 1 := by
  have hiI : i < (X.WI t).length := by rw [hv.length_WI ht]; exact hi
  have hiJ : i < (X.WJ t).length := by rw [hv.length_WJ ht]; exact hi
  have hzip : i < ((X.WI t).zip (X.WJ t)).length := by rw [List.length_zip]; omega
  rw [← getD_WI hi, ← getD_WJ hi, ans, thinOut, List.getD_eq_getElem _ _ (by simpa using hzip),
    List.getElem_map, List.getElem_map, List.getElem_zip, List.getD_eq_getElem _ _ hiI,
    List.getD_eq_getElem _ _ hiJ]

/-- Proof of Theorem 17: "a query pair (a,b) ∈ 𝒬 has a common neighbor if and only if some c ∈ C_k
has S(a,b,c) ≡ 0 (mod p)". -/
theorem acc_iff (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t) :
    X.acc t i = true ↔
      ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) := by
  have hentry : X.acc t i = true ↔
      thinEntry X.n X.D (X.matX t) (X.matY t) (X.rowOf t i) (X.colOf t i) ≠ 0 := by
    rw [acc, decide_eq_true_eq, hv.getD_ans ht hi]
    split_ifs with h <;> simp [h]
  rw [hentry, matX, matY, thinEntry_ne_zero_iff hv.p_ne (hv.len_mul_le t) (hv.rowOf_lt ht hi)
    (hv.colOf_lt ht hi)]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [RAC, RBC, getD_residList, getD_residList, ← hv.rab_place ht hi, RAB, getD_residList,
    labels_eq_iff hv.p_ne, ← rowOf_mul_add_colOf, sumAt, Nat.add_assoc, Nat.add_assoc]

/-- Proof of Theorem 17, "scan the piece C_k of its instance for a c with S(a,b,c) = 0": when the
scan succeeds.
-/
theorem hit_iff {t i : ℕ} (hi : i < X.w t) :
    X.hit t i = true ↔ ∃ c < X.len t, X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) = 0 := by
  rw [hit, getD_WI hi, getD_WJ hi]
  simp [scanHit, sumAt, Nat.add_assoc]

end HostData

end Light.Sec3
end

section
namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace HostLocal

/-- The number n of vertices of a part. -/
abbrev Size : ℕ := 0
/-- The inner dimension D. -/
abbrev ParD : ℕ := 1
/-- The prime p. -/
abbrev ThePrime : ℕ := 2
/-- The number q of vertices of a piece. -/
abbrev PieceLen : ℕ := 3
/-- The number chunkCount of chunks. -/
abbrev NumChunks : ℕ := 4
/-- The number m of instances. -/
abbrev NumInst : ℕ := 5
/-- The weights w(a,b). -/
abbrev AdrAB : ℕ := 6
/-- The weights w(b,c). -/
abbrev AdrBC : ℕ := 7
/-- The weights w(a,c). -/
abbrev AdrAC : ℕ := 8
/-- The residues of the weights w(a,c). -/
abbrev ResAC : ℕ := 9
/-- The residues of the weights w(b,c). -/
abbrev ResBC : ℕ := 10
/-- The rows of the sorted query pairs. -/
abbrev Rows : ℕ := 11
/-- The columns of the sorted query pairs. -/
abbrev Cols : ℕ := 12
/-- The classes of the chunks. -/
abbrev TabR : ℕ := 13
/-- The first places of the chunks. -/
abbrev TabL : ℕ := 14
/-- The numbers of query pairs of the chunks. -/
abbrev TabW : ℕ := 15
/-- The matrix X. -/
abbrev MatX : ℕ := 16
/-- The matrix Y. -/
abbrev MatY : ℕ := 17
/-- The answers of the solver. -/
abbrev AdrOut : ℕ := 18
/-- The free pointer. -/
abbrev SolverFree : ℕ := 19
/-- The number t of the instance. -/
abbrev Inst : ℕ := 20
/-- The number ch of its chunk. -/
abbrev ChunkNo : ℕ := 21
/-- The first vertex c0 of its piece. -/
abbrev PieceStart : ℕ := 22
/-- 1 if a zero triangle has been found. -/
abbrev Found : ℕ := 23
/-- The number len of vertices of the piece. -/
abbrev Len : ℕ := 24
/-- The class rho of the chunk. -/
abbrev Residue : ℕ := 25
/-- The first place lo of the chunk. -/
abbrev Start : ℕ := 26
/-- The number w of query pairs of the chunk. -/
abbrev NumPairs : ℕ := 27
/-- Results that are not used. -/
abbrev Unused : ℕ := 28

end HostLocal

open HostLocal

/-- The numbers of the next instance, of its chunk, and the first vertex of its piece. -/
def hostNext : Stmt :=
  .set ChunkNo (v ChunkNo +' k 1) ;;
  .ite (v ChunkNo =' v NumChunks)
    (.set ChunkNo (k 0) ;; .set PieceStart (v PieceStart +' v PieceLen)) .skip ;;
  .set Inst (v Inst +' k 1)

/-- The parameters of the instance: the number of vertices of its piece, and the class, the first
place and the number of query pairs of its chunk. -/
def hostParams : Stmt :=
  .set Len (v PieceLen) ;;
  .ite (v Size -' v PieceStart <' v PieceLen) (.set Len (v Size -' v PieceStart)) .skip ;;
  .set Residue (M (v TabR +' v ChunkNo)) ;;
  .set Start (M (v TabL +' v ChunkNo)) ;;
  .set NumPairs (M (v TabW +' v ChunkNo))

/-- The time for writing the two matrices of an instance whose piece has len vertices, with the
calls and the bookkeeping of a round. -/
def tWrites (n D len : ℕ) : ℕ := 101 + tWriteX n D len + tWriteY n D len

/-! ## What the loop relies on -/

/-- The facts about the data that the loop relies on; U is a bound on the weights. -/
structure HostOk (X : HostData) (U : ℕ) : Prop where
  valid : X.Valid
  leAB : AbsLe X.AB U
  leBC : AbsLe X.BC U
  leAC : AbsLe X.AC U

/-- The addresses of the arrays. -/
structure HostAddr : Type where
  ab : ℕ
  bc : ℕ
  ac : ℕ
  rac : ℕ
  rbc : ℕ
  qi : ℕ
  qj : ℕ
  cr : ℕ
  cl : ℕ
  cw : ℕ
  x : ℕ
  y : ℕ
  out : ℕ
  fr : ℕ

/-- What the memory holds: the weights, the residues of w(a,c) and w(b,c), the sorted query pairs,
and the three components of the table of chunks. -/
structure HostMem (X : HostData) (A : HostAddr) (μ : ℕ → ℤ) : Prop where
  segAB : Seg μ A.ab X.AB
  segBC : Seg μ A.bc X.BC
  segAC : Seg μ A.ac X.AC
  segRAC : SegN μ A.rac X.RAC
  segRBC : SegN μ A.rbc X.RBC
  segQI : SegN μ A.qi X.QI
  segQJ : SegN μ A.qj X.QJ
  segCR : SegN μ A.cr (X.CT.map fun c => c.residue)
  segCL : SegN μ A.cl (X.CT.map fun c => c.start)
  segCW : SegN μ A.cw (X.CT.map fun c => c.len)

/-- Where the arrays lie: everything that is read lies below x; then come the two matrices, the
answers, and the free pointer. -/
structure HostLay (X : HostData) (A : HostAddr) : Prop where
  bAB : A.ab + X.n * X.n ≤ A.x
  bBC : A.bc + X.n * X.n ≤ A.x
  bAC : A.ac + X.n * X.n ≤ A.x
  bRAC : A.rac + X.n * X.n ≤ A.x
  bRBC : A.rbc + X.n * X.n ≤ A.x
  bQI : A.qi + X.n * X.n ≤ A.x
  bQJ : A.qj + X.n * X.n ≤ A.x
  bCR : A.cr + X.chunkCount ≤ A.x
  bCL : A.cl + X.chunkCount ≤ A.x
  bCW : A.cw + X.chunkCount ≤ A.x
  xy : A.x + X.n * X.D ≤ A.y
  yo : A.y + X.D * X.n ≤ A.out
  ofr : ∀ t < X.m, A.out + X.w t ≤ A.fr

/-- What the limits have to allow for; need is the need of the solver. -/
structure HostLim (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr)
    (need : List ℕ → Need) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  fr : A.fr < lim.space
  prime : 2 * X.p < lim.space
  count : (X.m : ℤ) ≤ lim.word
  step : ((X.n + X.q : ℕ) : ℤ) ≤ lim.word
  weights : ((3 * U + 1 : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  solver : ∀ t < X.m, (need [X.n, X.D, X.w t]).Ok lim A.fr (d + 1)

/-- The context of hostLoop: a solver of Lop-AE-SparseTri, and the procedures writeX, writeY,
scanPairs, scan in the program. -/
structure HostCtx (P₀ R : Program) (pS pWriteX pWriteY pScan : ℕ) (Tn : List ℕ → ℕ)
    (need : List ℕ → Need) : Prop where
  sol : SolvesN lopDetectTask P₀ pS Tn need
  writeX : (P₀ ++ R)[pWriteX]? = some writeXBody
  writeY : (P₀ ++ R)[pWriteY]? = some writeYBody
  scan : (P₀ ++ R)[pScan]? = some scanBody

/-- The arguments of hostLoop. -/
def hostLoopArgs (X : HostData) (A : HostAddr) : List ℤ :=
  [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr, A.cl,
    A.cw, A.x, A.y, A.out, A.fr]

/-! ## What the calls assume -/

/-- Everything that hostLoop assumes, and a memory μ' that agrees with the first memory μ below
x. -/
structure HostSetting (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr)
    (need : List ℕ → Need) (μ μ' : ℕ → ℤ) : Prop where
  ok : HostOk X U
  mem : HostMem X A μ
  lay : HostLay X A
  fits : HostLim lim d X U A need
  kept : Kept μ μ' A.x

/-- Entries 0 and 1 have absolute value at most 1. -/
theorem absLe_one_of_zero_or_one {L : List ℤ} (h : ∀ e ∈ L, e = 0 ∨ e = 1) :
    AbsLe L ((1 : ℕ) : ℤ) := by
  intro e he
  rcases h e he with rfl | rfl <;> simp

namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : List ℕ → Need} {μ μ' μ'' : ℕ → ℤ} {t : ℕ}

/-- The order of the regions of the memory, the limits, and the sizes of instance t. -/
theorem places (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    A.ab + X.n * X.n ≤ A.x ∧ A.bc + X.n * X.n ≤ A.x ∧ A.ac + X.n * X.n ≤ A.x ∧
      A.rac + X.n * X.n ≤ A.x ∧ A.rbc + X.n * X.n ≤ A.x ∧ A.qi + X.n * X.n ≤ A.x ∧
      A.qj + X.n * X.n ≤ A.x ∧ A.cr + X.chunkCount ≤ A.x ∧ A.cl + X.chunkCount ≤ A.x ∧
      A.cw + X.chunkCount ≤ A.x ∧ A.x + X.n * X.D ≤ A.y ∧ A.y + X.D * X.n ≤ A.out ∧
      A.out + X.w t ≤ A.fr ∧
      (lim.space : ℤ) ≤ lim.word ∧ A.fr < lim.space ∧ 2 * X.p < lim.space ∧
      (X.m : ℤ) ≤ lim.word ∧ ((X.n + X.q : ℕ) : ℤ) ≤ lim.word ∧ d + 2 ≤ lim.depth ∧
      X.c0 t + X.len t ≤ X.n ∧ X.lo t + X.w t ≤ X.n * X.n ∧ t % X.chunkCount < X.chunkCount :=
  ⟨S.lay.bAB, S.lay.bBC, S.lay.bAC, S.lay.bRAC, S.lay.bRBC, S.lay.bQI, S.lay.bQJ, S.lay.bCR,
    S.lay.bCL, S.lay.bCW, S.lay.xy, S.lay.yo, S.lay.ofr t ht, S.fits.space, S.fits.fr, S.fits.prime,
    S.fits.count, S.fits.step, S.fits.depth, S.ok.valid.piece_le ht, S.ok.valid.lo_add_le ht,
    HostData.mod_chunkCount_lt ht⟩

/-- A later memory that agrees with μ' below x. -/
theorem next (S : HostSetting lim d X U A need μ μ') (h : ∀ a < A.x, μ'' a = μ' a) :
    HostSetting lim d X U A need μ μ'' :=
  { S with kept := fun a ha => (h a ha).trans (S.kept a ha) }

/-- There are `n²` residues of the weights `w(a,c)`. -/
theorem length_RAC (S : HostSetting lim d X U A need μ μ') : X.RAC.length = X.n * X.n := by
  simp [HostData.RAC, residList, S.ok.valid.lenAC]

/-- There are `n²` residues of the weights `w(b,c)`. -/
theorem length_RBC (S : HostSetting lim d X U A need μ μ') : X.RBC.length = X.n * X.n := by
  simp [HostData.RBC, residList, S.ok.valid.lenBC]

/-- What the loop reads stands in μ' as it stood in μ. -/
theorem mem' (S : HostSetting lim d X U A need μ μ') : HostMem X A μ' := by
  light_facts S S.lay S.ok.valid
  have := S.length_RAC
  have := S.length_RBC
  have := S.ok.valid.length_QI
  have := S.ok.valid.length_QJ
  have : X.CT.length = X.chunkCount := rfl
  have h := S.mem
  exact
    { segAB := h.segAB.keep
      segBC := h.segBC.keep
      segAC := h.segAC.keep
      segRAC := h.segRAC.keep
      segRBC := h.segRBC.keep
      segQI := h.segQI.keep
      segQJ := h.segQJ.keep
      segCR := h.segCR.keep
      segCL := h.segCL.keep
      segCW := h.segCW.keep }

/-- Reading an entry of a component of the table of chunks. -/
theorem read_tab {a : ℕ} (f : Chunk → ℕ) (h : SegN μ a (X.CT.map f)) {i : ℕ}
    (hi : i < X.chunkCount) : μ (a + i) = (f (X.CT.getD i ⟨0, 0, 0⟩) : ℤ) := by
  have hi' : i < X.CT.length := hi
  rw [h i (by simpa using hi'), List.getD_eq_getElem _ _ hi']
  simp

/-- The three parameters of the chunk of instance t, in the memory. -/
theorem read_chunk (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    μ' (A.cr + t % X.chunkCount) = X.rho t ∧ μ' (A.cl + t % X.chunkCount) = X.lo t ∧
      μ' (A.cw + t % X.chunkCount) = X.w t :=
  ⟨read_tab (fun c => c.residue) S.mem'.segCR (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.start) S.mem'.segCL (HostData.mod_chunkCount_lt ht),
    read_tab (fun c => c.len) S.mem'.segCW (HostData.mod_chunkCount_lt ht)⟩

/-- What writeX and writeY assume, for a matrix of size cells at dst and the residues of a list of
weights at r. -/
theorem write (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) {dst size r : ℕ}
    {weights : List ℤ} (seg : SegN μ' r (residList X.p weights))
    (length : (residList X.p weights).length = X.n * X.n) (hsize : size = X.D * X.n)
    (hdst : dst + size < lim.space) (hr : r + X.n * X.n ≤ dst) :
    WritePre lim μ' dst size r X.n X.D X.p (X.c0 t) (X.len t) (residList X.p weights) where
  hw := S.fits.space
  seg := seg
  length := length
  lt := fun x hx => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact resid_lt S.ok.valid.p_ne z
  fits := S.ok.valid.len_mul_le t
  piece := S.ok.valid.piece_le ht
  size := hsize
  spaceM := hdst
  spaceR := by omega
  spaceP := S.fits.prime
  apart := Or.inr hr

/-- The precondition of writeX holds. -/
theorem writeX (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.x (X.n * X.D) A.rac X.n X.D X.p (X.c0 t) (X.len t) X.RAC := by
  have := S.places ht
  exact S.write ht S.mem'.segRAC S.length_RAC (Nat.mul_comm _ _) (by omega) (by omega)

/-- The precondition of writeY holds. -/
theorem writeY (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    WritePre lim μ' A.y (X.D * X.n) A.rbc X.n X.D X.p (X.c0 t) (X.len t) X.RBC := by
  have := S.places ht
  exact S.write ht S.mem'.segRBC S.length_RBC rfl (by omega) (by omega)

/-- The instance number t, as the solver gets it. -/
def inst (X : HostData) (A : HostAddr) (t : ℕ) : ThinInst :=
  { N := X.n, D := X.D, w := X.w t, U := 1, x := A.x, y := A.y, wi := A.qi + X.lo t,
    wj := A.qj + X.lo t, out := A.out, X := X.matX t, Y := X.matY t, WI := X.WI t, WJ := X.WJ t }

/-- The precondition of the solver holds, once the two matrices are written. -/
theorem solver (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) : lopDetectTask.Pre (inst X A t) μ' A.fr := by
  have := S.places ht
  have hv := S.ok.valid
  refine ⟨?_, rfl⟩
  exact
    { N_pos := hv.n_pos
      D_pos := le_trans (Nat.mul_pos hv.q_pos hv.p_pos) hv.qp_le
      lenX := X.length_matX t
      lenY := X.length_matY t
      lenWI := hv.length_WI ht
      lenWJ := hv.length_WJ ht
      segX := hX
      segY := hY
      segWI := SegN.drop_take S.mem'.segQI _ _
      segWJ := SegN.drop_take S.mem'.segQJ _ _
      leX := absLe_one_of_zero_or_one (X.matX_zero_or_one t)
      leY := absLe_one_of_zero_or_one (X.matY_zero_or_one t)
      ltWI := fun _ => HostData.lt_of_mem_WI
      ltWJ := fun _ => HostData.lt_of_mem_WJ
      belowX := by simp only [inst]; omega
      belowY := by simp only [inst]; omega
      belowWI := by simp only [inst]; omega
      belowWJ := by simp only [inst]; omega
      belowOut := by simp only [inst]; omega
      apartX := by simp only [inst]; omega
      apartY := by simp only [inst]; omega
      apartWI := by simp only [inst]; omega
      apartWJ := by simp only [inst]; omega }

/-- The weights are where the scans read them. -/
theorem weights (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Weights lim μ' A.ab A.bc A.ac X.n U X.AB X.BC X.AC := by
  have := S.places ht
  have hm := S.mem'
  have hv := S.ok.valid
  exact
    { hw := S.fits.space
      hU := by exact_mod_cast S.fits.weights
      arrAB := { len := hv.lenAB, seg := hm.segAB, bound := S.ok.leAB }
      arrBC := { len := hv.lenBC, seg := hm.segBC, bound := S.ok.leBC }
      arrAC := { len := hv.lenAC, seg := hm.segAC, bound := S.ok.leAC } }

/-- The answers of the solver and the query pairs of the chunk are where the scans read them. -/
theorem answers (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (hans : Seg μ' A.out (X.ans t)) :
    Answers lim μ' A.out (A.qi + X.lo t) (A.qj + X.lo t) (X.w t) X.n (X.ans t) (X.WI t)
      (X.WJ t) := by
  have := S.places ht
  have hv := S.ok.valid
  exact
    { arrOUT :=
        { len := by simp [HostData.ans, thinOut, hv.length_WI ht, hv.length_WJ ht], seg := hans }
      arrQA :=
        { len := hv.length_WI ht, seg := SegN.drop_take S.mem'.segQI _ _
          lt := fun _ => HostData.lt_of_mem_WI }
      arrQB :=
        { len := hv.length_WJ ht, seg := SegN.drop_take S.mem'.segQJ _ _
          lt := fun _ => HostData.lt_of_mem_WJ }
      w_lt := by omega }

end HostSetting

/-! ## The parts of a round -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScan : ℕ} {Tn : List ℕ → ℕ}
  {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ} {t : ℕ}

/-- The state of hostLoop: the arguments, the numbers t, ch and c0 of the instance, and what the
locals Found, Len, Residue, Start, NumPairs and Unused hold. -/
abbrev hostState (X : HostData) (A : HostAddr) (t ch c0 : ℕ) (fnd len rho lo w res : ℤ)
    (μ' : ℕ → ℤ) : State :=
  ⟨frame [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr,
    A.cl, A.cw, A.x, A.y, A.out, A.fr, t, ch, c0, fnd, len, rho, lo, w, res], μ'⟩

/-- **The parameters of instance t.** -/
theorem hostParams_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostParams (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 27
      (· = hostState X A t (t % X.chunkCount) (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res
        μ') := by
  have := S.places ht
  obtain ⟨hrho, hlo, hw⟩ := S.read_chunk ht
  have : X.len t = min X.q (X.n - X.c0 t) := rfl
  generalize t % X.chunkCount = ch at *
  -- rho := mem[cr + ch]; lo := mem[cl + ch]; w := mem[cw + ch]
  have htail : ∀ len' : ℤ, len' = X.len t → Ends lim P d
      (.set Residue (M (v TabR +' v ChunkNo)) ;; .set Start (M (v TabL +' v ChunkNo)) ;;
        .set NumPairs (M (v TabW +' v ChunkNo)))
      (hostState X A t ch (X.c0 t) fnd len' rho lo w res μ') 15
      (· = hostState X A t ch (X.c0 t) fnd (X.len t) (X.rho t) (X.lo t) (X.w t) res μ') := by
    rintro _ rfl
    refine Ends.setToThen (X.rho t : ℤ) ?_ (by light_side [hrho])
    refine Ends.setToThen (X.lo t : ℤ) ?_ (by light_side [hlo])
    exact Ends.setTo (X.w t : ℤ) rfl (by light_side [hw])
  unfold hostParams
  -- len := q
  light_set X.q
  -- if n - c0 < q then len := n - c0
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    exact Ends.setToThen (X.len t : ℤ) ((htail _ rfl).mono (by light_time) fun _ h => h)
  · replace hc : ¬ (X.n : ℤ) - X.c0 t < X.q := by simpa using hc
    refine Ends.next 0 (Ends.skip ?_)
    exact (htail _ (by omega)).mono (by light_time) fun _ h => h

/-- The call of writeX for instance t. -/
theorem HostCtx.writeX_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteX (d + 1)
      [(A.x : ℤ), A.rac, X.n, X.D, X.p, X.c0 t, X.len t, X.rho t] μ' (tWriteX X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.x (X.matX t) ∧ SameOutside μ' μ₁ A.x (X.n * X.D) :=
  Meets.of_body C.writeX (writeX_spec (S.writeX ht) (S.ok.valid.rho_lt ht))

/-- The call of writeY for instance t. -/
theorem HostCtx.writeY_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) :
    Meets lim (P₀ ++ R) pWriteY (d + 1) [(A.y : ℤ), A.rbc, X.n, X.D, X.p, X.c0 t, X.len t] μ'
      (tWriteY X.n X.D (X.len t))
      fun _ μ₁ => Seg μ₁ A.y (X.matY t) ∧ SameOutside μ' μ₁ A.y (X.D * X.n) :=
  Meets.of_body C.writeY (writeY_spec (S.writeY ht))

/-- The call of the solver for instance t, once the two matrices are written. -/
theorem HostCtx.solver_meets (C : HostCtx P₀ R pS pWriteX pWriteY pScan Tn need)
    (S : HostSetting lim d X U A need μ μ') (ht : t < X.m) (hX : Seg μ' A.x (X.matX t))
    (hY : Seg μ' A.y (X.matY t)) :
    Meets lim (P₀ ++ R) pS (d + 1)
      [(X.n : ℤ), X.D, X.w t, (1 : ℕ), A.x, A.y, (A.qi + X.lo t : ℕ), (A.qj + X.lo t : ℕ), A.out,
        A.fr] μ' (Tn [X.n, X.D, X.w t])
      fun _ μ₁ => Seg μ₁ A.out (X.ans t) ∧ KeptBut μ' μ₁ A.fr A.out (X.w t) :=
  C.sol.meets R (HostSetting.inst X A t) (S.solver ht hX hY) (S.fits.solver t ht)

theorem hostNext_spec {P : Program} (S : HostSetting lim d X U A need μ μ') (ht : t < X.m)
    (fnd len rho lo w res : ℤ) :
    Ends lim P d hostNext (hostState X A t (t % X.chunkCount) (X.c0 t) fnd len rho lo w res μ') 18
      (· = hostState X A (t + 1) ((t + 1) % X.chunkCount) (X.c0 (t + 1)) fnd len rho lo w res
        μ') := by
  have hplaces := S.places ht
  have hlast := Nat.succ_div_mod_of_eq (n := X.chunkCount) (i := t)
  have hinner := Nat.succ_div_mod_of_ne (n := X.chunkCount) (i := t) (by omega)
  have hc0 : X.c0 t = t / X.chunkCount * X.q := rfl
  have hc0' : X.c0 (t + 1) = (t + 1) / X.chunkCount * X.q := rfl
  generalize t % X.chunkCount = ch at *
  generalize (t + 1) % X.chunkCount = ch' at *
  have htail : Ends lim P d (.set Inst (v Inst +' k 1))
      (hostState X A t ch' (X.c0 (t + 1)) fnd len rho lo w res μ') 4
      (· = hostState X A (t + 1) ch' (X.c0 (t + 1)) fnd len rho lo w res μ') :=
    Ends.setTo (t + 1 : ℕ) rfl
  unfold hostNext
  light_set (ch + 1 : ℕ)
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · replace hc : ch + 1 = X.chunkCount := by
      have : ((ch + 1 : ℕ) : ℤ) = X.chunkCount := by simpa using hc
      exact_mod_cast this
    obtain ⟨hdiv, rfl⟩ := hlast hc
    have hstep : X.c0 (t + 1) = X.c0 t + X.q := by rw [hc0', hc0, hdiv, Nat.succ_mul]
    have hwrap : Ends lim P d (.set ChunkNo (k 0) ;; .set PieceStart (v PieceStart +' v PieceLen))
        (hostState X A t (ch + 1) (X.c0 t) fnd len rho lo w res μ') 6
        (· = hostState X A t 0 (X.c0 (t + 1)) fnd len rho lo w res μ') :=
      Ends.setToThen ((0 : ℕ) : ℤ)
        (Ends.setTo (X.c0 (t + 1) : ℕ) rfl (by light_side [hstep]))
    refine Ends.next _ (hwrap.mono le_rfl ?_)
    rintro _ rfl
    exact htail.mono (by light_time) fun _ h => h
  · replace hc : ch + 1 ≠ X.chunkCount := fun h => hc (by simp; exact_mod_cast h)
    obtain ⟨hdiv, rfl⟩ := hinner hc
    have hstep : X.c0 (t + 1) = X.c0 t := by rw [hc0', hc0, hdiv]
    refine Ends.next 0 (Ends.skip ?_)
    rw [← hstep]
    exact htail.mono (by light_time) fun _ h => h

end Light.Sec3
end

section
namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The procedure -/

/-- The numbers of the procedures that et17 calls, directly or through the procedures that it
calls: the two parameter procedures, sqrt, brute, scan, choosePrime, queryCapNat, ceilDiv, bitLen,
dblTable, resid, residues, classes, chunks, hostLoop, the solver, writeX, writeY, scanPairs, and
the procedures below choosePrime. -/
structure Et17Nums : Type where
  pD : ℕ
  pG : ℕ
  pSqrt : ℕ
  pScan : ℕ
  pChoose : ℕ
  pCap : ℕ
  pCeil : ℕ
  pBitLen : ℕ
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pClasses : ℕ
  pChunks : ℕ
  pS : ℕ
  pWriteX : ℕ
  pWriteY : ℕ
  ch : ChNums

namespace Et17

/-- The locals of `et17`.  The arguments: `n`, `U`, the addresses of the three arrays of weights,
and the free pointer (the table of doubles is there).  Then `D`, `g`, `s = ⌊√D⌋`, the prime `p`,
`cap`, the number `q` of vertices of a piece, the number `h` of pieces, `len = bitLen U`, and `n²`.
Then the addresses of the residues of `w(a,b)`, `w(b,c)`, `w(a,c)`, of the starts of the classes,
the running places, the rows and the columns of the sorted pairs, the three components of the table
of chunks, `X`, `Y`, the answers, and the solver's free pointer.  Then `n² + p`, the number of
chunks, the number of instances, a flag (also the place for results that are not used), and `n D`.
-/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AdrAB : ℕ := 2
@[inherit_doc Size] abbrev AdrBC : ℕ := 3
@[inherit_doc Size] abbrev AdrAC : ℕ := 4
@[inherit_doc Size] abbrev Free : ℕ := 5
@[inherit_doc Size] abbrev ParD : ℕ := 6
@[inherit_doc Size] abbrev ParG : ℕ := 7
@[inherit_doc Size] abbrev RootD : ℕ := 8
@[inherit_doc Size] abbrev ThePrime : ℕ := 9
@[inherit_doc Size] abbrev Cap : ℕ := 10
@[inherit_doc Size] abbrev PieceLen : ℕ := 11
@[inherit_doc Size] abbrev NumPieces : ℕ := 12
@[inherit_doc Size] abbrev Bits : ℕ := 13
@[inherit_doc Size] abbrev SizeSq : ℕ := 14
@[inherit_doc Size] abbrev ResAB : ℕ := 16
@[inherit_doc Size] abbrev ResBC : ℕ := 17
@[inherit_doc Size] abbrev ResAC : ℕ := 18
@[inherit_doc Size] abbrev Cls : ℕ := 19
@[inherit_doc Size] abbrev Cur : ℕ := 20
@[inherit_doc Size] abbrev Rows : ℕ := 21
@[inherit_doc Size] abbrev Cols : ℕ := 22
@[inherit_doc Size] abbrev TabR : ℕ := 23
@[inherit_doc Size] abbrev TabL : ℕ := 24
@[inherit_doc Size] abbrev TabW : ℕ := 25
@[inherit_doc Size] abbrev MatX : ℕ := 26
@[inherit_doc Size] abbrev MatY : ℕ := 27
@[inherit_doc Size] abbrev AdrOut : ℕ := 28
@[inherit_doc Size] abbrev SolverFree : ℕ := 29
@[inherit_doc Size] abbrev Room : ℕ := 30
@[inherit_doc Size] abbrev NumChunks : ℕ := 31
@[inherit_doc Size] abbrev NumInst : ℕ := 32
@[inherit_doc Size] abbrev Small : ℕ := 33
@[inherit_doc Size] abbrev Area : ℕ := 34

end Et17

open Et17 in
/-- The first part of et17: `D`, `g`, `s`, and the flag that says whether `n` is small. -/
def et17Params (ν : Et17Nums) : Stmt :=
  .call ν.pD [v Size] ParD ;;
  .call ν.pG [v ParD] ParG ;;
  .call ν.pSqrt [v ParD] RootD ;;
  .ite (v ParD <' k 16) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v Size <' v ParD) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v ParG <' k 1) (.set Small (k 1)) (.set Small (v Small)) ;;
  .ite (v RootD <' v ParG) (.set Small (k 1)) (.set Small (v Small)) ;;
  .skip

open Et17 in
/-- The end of the second part: the sizes n², nD, n² + p, and the addresses of the arrays. -/
def et17Addr : Stmt :=
  .set SizeSq (v Size *' v Size) ;;
  .set Area (v Size *' v ParD) ;;
  .set Room (v SizeSq +' v ThePrime) ;;
  .set ResAB (v Free +' (v Bits +' k 1)) ;;
  .set ResBC (v ResAB +' v SizeSq) ;;
  .set ResAC (v ResBC +' v SizeSq) ;;
  .set Cls (v ResAC +' v SizeSq) ;;
  .set Cur (v Cls +' (v ThePrime +' k 1)) ;;
  .set Rows (v Cur +' v ThePrime) ;;
  .set Cols (v Rows +' v SizeSq) ;;
  .set TabR (v Cols +' v SizeSq) ;;
  .set TabL (v TabR +' v Room) ;;
  .set TabW (v TabL +' v Room) ;;
  .set MatX (v TabW +' v Room) ;;
  .set MatY (v MatX +' v Area) ;;
  .set AdrOut (v MatY +' v Area) ;;
  .set SolverFree (v AdrOut +' v Cap) ;;
  .skip

/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/

/-- n is small for the parameters D and g: the host runs the brute force. -/
def SmallCase (n D g : ℕ) : Prop := D < 16 ∨ n < D ∨ g < 1 ∨ Nat.sqrt D < g

instance (n D g : ℕ) : Decidable (SmallCase n D g) := by unfold SmallCase; infer_instance

/-- The largest time of the solver on an instance with at most cap query pairs. -/
def supTime (Tn : List ℕ → ℕ) (n D cap : ℕ) : ℕ :=
  (Finset.range (cap + 1)).sup fun w => Tn [n, D, w]

/-- The largest need of the solver on an instance with at most cap query pairs. -/
def supNeed (need : List ℕ → Need) (n D cap : ℕ) : Need :=
  ⟨(Finset.range (cap + 1)).sup fun w => (need [n, D, w]).word,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).cells,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).depth⟩

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)" for the selected prime.
Here the second form, with the constant `Hashing.falsePositiveConst` and with κ = kappaOf n U =
max(1, log U / log n), so that U ≤ n^κ. -/
noncomputable def falsePositiveBound (n U D : ℕ) : ℕ :=
  ⌊Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D)⌋₊

/-- The time of the parameter procedures, of the square root and of the tests. -/
def hostSetup (tD tG : ℕ → ℕ) (n D : ℕ) : ℕ := tD n + tG D + (18 * Nat.sqrt D + 12) + 60

/-- The cells of the arrays of et17, with s in place of the prime. -/
def hostLayout (n U D : ℕ) : ℕ :=
  (bitLen U + 1) + 3 * (n * n) + (Nat.sqrt D + 1) + Nat.sqrt D + 2 * (n * n)
    + 3 * (n * n + Nat.sqrt D) + 2 * (n * D) + queryCapNat n D

/-- The largest number that et17 and the procedures below it form, apart from the solver; a and b
bound the numbers that the two parameter procedures form. -/
def hostWord (a b n U D g : ℕ) : ℕ :=
  a + b                                                     -- the two parameter procedures
    + (4 * D + 4)                                           -- the square root, the primes up to √D
    + (3 * U + 1)                                           -- a sum of three weights
    + (2 * U + 2)                                           -- the number of binary digits of U
    + (2 * n + 1)                                           -- the power of two above n
    + Nat.sqrt D * 2 ^ (bitLen U + 1)                       -- the table of doubles
    + 4 * (16 ^ Nat.clog 2 n * Nat.sqrt D)                  -- the entries in Strassen's algorithm
    + n * n * (16 ^ Nat.clog 2 n * Nat.sqrt D)              -- the count for a prime
    + (4 * n ^ 4 + D + 2)                                   -- cap
    + (Nat.sqrt D + g + 1)                                  -- the size of a piece
    + (n + pieceSizeNat D g + 1)                                -- the number of pieces
    + 4 * n * g                                             -- the number of instances
    + 100

/-- The need of the host for given parameters D and g. -/
def hostNeedAt (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n D (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n D (queryCapNat n D)).cells + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n D (queryCapNat n D)).depth⟩

/-- **The need of the host**, over a solver with the need `need`; wD and wG bound the numbers that
the parameter procedures form. -/
def hostNeed (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-! ## The context -/

/-- A procedure that computes a function of one number and changes no cell; t is its time, w bounds
the numbers it forms, and it nests calls at most three deep. -/
def ParamProc (P : Program) (p : ℕ) (f t w : ℕ → ℕ) : Prop :=
  ∀ (lim : Limits) (d x : ℕ) (μ : ℕ → ℤ), 1 ≤ x → (lim.space : ℤ) ≤ lim.word →
    ((w x : ℕ) : ℤ) ≤ lim.word → d + 4 ≤ lim.depth →
    Meets lim P p (d + 1) [(x : ℤ)] μ (t x) fun r μ' => r = (f x : ℕ) ∧ μ' = μ

/-- The context of et17: the solver and what hostLoop calls; the procedures of the host; the
two parameter procedures. -/
structure Et17Ctx (P₀ R : Program) (ν : Et17Nums) (Tn : List ℕ → ℕ) (need : List ℕ → Need)
    (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  loop : HostCtx P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScan Tn need
  hSqrt : (P₀ ++ R)[ν.pSqrt]? = some sqrtBody
  hChoose : (P₀ ++ R)[ν.pChoose]? = some (choosePrimeBody ν.ch)
  ch : ChCtx (P₀ ++ R) ν.ch
  hCap : (P₀ ++ R)[ν.pCap]? = some queryCapNatBody
  hCeil : (P₀ ++ R)[ν.pCeil]? = some ceilDivBody
  hBitLen : (P₀ ++ R)[ν.pBitLen]? = some bitLenBody
  hDbl : (P₀ ++ R)[ν.pDbl]? = some dblTableBody
  hResid : (P₀ ++ R)[ν.pResid]? = some residBody
  hResidues : (P₀ ++ R)[ν.pResidues]? = some (residuesBody ν.pResid)
  hClasses : (P₀ ++ R)[ν.pClasses]? = some classesBody
  hChunks : (P₀ ++ R)[ν.pChunks]? = some chunksBody
  dProc : ParamProc (P₀ ++ R) ν.pD Dfun tD wD
  gProc : ParamProc (P₀ ++ R) ν.pG Gfun tG wG
  D_pos : ∀ n, 1 ≤ n → 1 ≤ Dfun n

/-! ## The data, the addresses and the local variables of a run -/

/-- The address of the residues of `w(a,b)`; the table of doubles is at fr. -/
def aRab (_X : HostData) (U fr : ℕ) : ℕ := fr + (bitLen U + 1)
/-- The address of the residues of `w(b,c)`. -/
def aRbc (X : HostData) (U fr : ℕ) : ℕ := aRab X U fr + X.n * X.n
/-- The address of the residues of `w(a,c)`. -/
def aRac (X : HostData) (U fr : ℕ) : ℕ := aRbc X U fr + X.n * X.n
/-- The address of the starts of the classes. -/
def aCls (X : HostData) (U fr : ℕ) : ℕ := aRac X U fr + X.n * X.n
/-- The address of the running places. -/
def aCur (X : HostData) (U fr : ℕ) : ℕ := aCls X U fr + (X.p + 1)
/-- The address of the rows of the sorted pairs. -/
def aQi (X : HostData) (U fr : ℕ) : ℕ := aCur X U fr + X.p
/-- The address of the columns of the sorted pairs. -/
def aQj (X : HostData) (U fr : ℕ) : ℕ := aQi X U fr + X.n * X.n
/-- The address of the residues of the chunks. -/
def aCr (X : HostData) (U fr : ℕ) : ℕ := aQj X U fr + X.n * X.n
/-- The address of the starts of the chunks. -/
def aCl (X : HostData) (U fr : ℕ) : ℕ := aCr X U fr + (X.n * X.n + X.p)
/-- The address of the lengths of the chunks. -/
def aCw (X : HostData) (U fr : ℕ) : ℕ := aCl X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matX` of an instance. -/
def aX (X : HostData) (U fr : ℕ) : ℕ := aCw X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matY` of an instance. -/
def aY (X : HostData) (U fr : ℕ) : ℕ := aX X U fr + X.n * X.D
/-- The address of the answers. -/
def aOut (X : HostData) (U fr : ℕ) : ℕ := aY X U fr + X.n * X.D
/-- The free pointer that is handed to the solver. -/
def aFr (X : HostData) (U fr : ℕ) : ℕ := aOut X U fr + X.cap

/-- The arrays of the host stand one after the other. -/
theorem host_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCur X U fr = aCls X U fr + (X.p + 1) ∧ aQi X U fr = aCur X U fr + X.p ∧
      aQj X U fr = aQi X U fr + X.n * X.n ∧ aCr X U fr = aQj X U fr + X.n * X.n ∧
      aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧ aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧
      aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧ aY X U fr = aX X U fr + X.n * X.D ∧
      aOut X U fr = aY X U fr + X.n * X.D ∧ aFr X U fr = aOut X U fr + X.cap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The addresses that hostLoop gets. -/
def hostAddr (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  ⟨x.ab, x.bc, x.ac, aRac X x.U fr, aRbc X x.U fr, aQi X x.U fr, aQj X x.U fr, aCr X x.U fr,
    aCl X x.U fr, aCw X x.U fr, aX X x.U fr, aY X x.U fr, aOut X x.U fr, aFr X x.U fr⟩

/-- The locals at the start: the arguments, then zeros. -/
def et17Loc0 (x : TriInst) (fr : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals after the first part. -/
def et17LocA (x : TriInst) (fr D g : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (D : ℤ), (g : ℤ),
    ((Nat.sqrt D : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    (if SmallCase x.n D g then 1 else 0), 0]

/-- The locals of the third part, for the data X of the loop: those after the second part, with the
number of chunks in NumChunks and the result of the last call in Small.  ParG and RootD are not
read. -/
abbrev Et17.locals (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res : ℤ) : List ℤ :=
  [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s, (X.p : ℤ),
    (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), ((X.n * X.n : ℕ) : ℤ), 0,
    ((aRab X x.U fr : ℕ) : ℤ), ((aRbc X x.U fr : ℕ) : ℤ), ((aRac X x.U fr : ℕ) : ℤ),
    ((aCls X x.U fr : ℕ) : ℤ), ((aCur X x.U fr : ℕ) : ℤ), ((aQi X x.U fr : ℕ) : ℤ),
    ((aQj X x.U fr : ℕ) : ℤ), ((aCr X x.U fr : ℕ) : ℤ), ((aCl X x.U fr : ℕ) : ℤ),
    ((aCw X x.U fr : ℕ) : ℤ), ((aX X x.U fr : ℕ) : ℤ), ((aY X x.U fr : ℕ) : ℤ),
    ((aOut X x.U fr : ℕ) : ℤ), ((aFr X x.U fr : ℕ) : ℤ), ((X.n * X.n + X.p : ℕ) : ℤ), nch, 0, res,
    ((X.n * X.D : ℕ) : ℤ)]

end Light.Sec3
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Pure facts about the starts of the classes and the table of chunks

Proof of Theorem 17.  The `n²` pairs `(a, b)` are listed class after class, where the class
of a residue `ϱ < p` holds the pairs whose weight is congruent to `ϱ` modulo the prime `p`, and each
class is cut into chunks of at most `cap` pairs.  The list of the starts of the classes has `p + 1`
entries, none above `n²`; the table of chunks has at most `n² + p` entries.
-/


namespace ThreeSumApsp.Spec

/-- The list of the starts of the classes has one entry for each residue, and one more for the
end. -/
theorem length_classStarts (n p : ℕ) (RAB : List ℕ) : (classStarts n p RAB).length = p + 1 := by
  simp [classStarts]

/-- A class starts at a place of the list of all n² pairs, or at its end. -/
theorem classStart_le_sq (n : ℕ) (RAB : List ℕ) (rho : ℕ) : classStart n RAB rho ≤ n * n := by
  rw [classStart_eq_length_filter]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- No entry of the list of the starts of the classes is above n². -/
theorem le_of_mem_classStarts {n p : ℕ} {RAB : List ℕ} {x : ℕ} (hx : x ∈ classStarts n p RAB) :
    x ≤ n * n := by
  obtain ⟨rho, -, rfl⟩ := List.mem_map.1 hx
  exact classStart_le_sq n RAB rho

/-- If `cap ≥ 1` and every residue is below `p`, the table of chunks has at most `n² + p` entries.
This is the number of cells that the host procedure of Theorem 17 reserves for each of its three
components. -/
theorem length_chunkTab_le_add {n p cap : ℕ} {RAB : List ℕ} (hcap : 1 ≤ cap)
    (hlt : ∀ i < n * n, RAB.getD i 0 < p) : (chunkTab n p cap RAB).length ≤ n * n + p := by
  have := length_chunkTab_le hcap hlt
  have := Nat.div_le_self (n * n) cap
  omega

end ThreeSumApsp.Spec

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The host of Theorem 17: failed scans and false positives

Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans" (`HostData.sum_fails_le`).  An accepted query pair `(a, b)` of an instance whose scan
fails has a vertex `c` in the piece of the instance with `p ∣ S(a,b,c)` and `S(a,b,c) ≠ 0`
(`exists_false_positive`); such a triple is a false positive of `p`, and `F(p)` is their number.
Different pairs (instance, query pair) give different triples (`Valid.eq_of_place_eq`): `c`
determines the piece; `(a, b)` determines the place `a n + b`; the place determines the position in
the list of all pairs, which has no repetition; and the position determines the chunk.

The statement `theorem_17` is about the reduction on finite sets, and there the same sentences are
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`,
`TriangleInstance.eq_of_mem_acceptedPairs` and `TriangleInstance.card_failedScans_le`.  The two
proofs run in parallel.  They share `F(p)` and the counting step, which is stated for any family of
scans (`TriangleInstance.card_le_F_of_distinct_scans`).
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace HostData

variable {X : HostData}

/-- Two query pairs at the same place, of instances with the same piece, are the same. -/
theorem Valid.eq_of_place_eq (hv : X.Valid) {t t' i i' : ℕ} (ht : t < X.m) (ht' : t' < X.m)
    (hi : i < X.w t) (hi' : i' < X.w t') (hplace : X.place t i = X.place t' i')
    (hpiece : t / X.chunkCount = t' / X.chunkCount) : t = t' ∧ i = i' := by
  have := hv.length_sortedIdx
  have := hv.lo_add_le ht
  have := hv.lo_add_le ht'
  -- The list of all pairs has no repetition, so the two pairs stand at the same position in it.
  have hpos : X.lo t + i = X.lo t' + i' := by
    rw [place, place, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      at hplace
    exact (List.Nodup.getElem_inj_iff (sortedIdx_nodup X.n X.p X.RAB)).1 hplace
  -- A position lies in one chunk only.
  have hchunk : ∀ s (hs : s % X.chunkCount < (chunkTab X.n X.p X.cap X.RAB).length),
      (chunkTab X.n X.p X.cap X.RAB)[s % X.chunkCount] = X.chunk s := fun s hs =>
    (List.getD_eq_getElem _ _ hs).symm
  have hmod : t % X.chunkCount = t' % X.chunkCount :=
    chunkTab_unique hv.cap_pos (j := X.lo t + i) (mod_chunkCount_lt ht) (mod_chunkCount_lt ht')
      (hchunk t _ ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
      (hchunk t' _ ▸ hpos ▸ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi' _⟩)
  obtain rfl : t = t' := by
    rw [← Nat.div_add_mod t X.chunkCount, ← Nat.div_add_mod t' X.chunkCount, hpiece, hmod]
  exact ⟨rfl, by omega⟩

/-- Proof of Theorem 17: "A failed scan [...] contains a c ∈ C_k with S(a,b,c) ≡ 0 (mod p) but
S(a,b,c) ≠ 0". -/
theorem exists_false_positive (hv : X.Valid) {t i : ℕ} (ht : t < X.m) (hi : i < X.w t)
    (hacc : X.acc t i = true) (hhit : X.hit t i = false) :
    ∃ c < X.len t, (X.p : ℤ) ∣ X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ∧
      X.sumAt (X.rowOf t i) (X.colOf t i) (X.c0 t + c) ≠ 0 := by
  obtain ⟨c, hc, hdvd⟩ := (acc_iff hv ht hi).1 hacc
  refine ⟨c, hc, hdvd, fun hzero => ?_⟩
  rw [(hit_iff hi).2 ⟨c, hc, hzero⟩] at hhit
  exact absurd hhit (by decide)

/-- A vertex of the piece of an instance determines the number of the piece. -/
theorem c0_add_div {t c : ℕ} (hc : c < X.len t) : (X.c0 t + c) / X.q = t / X.chunkCount := by
  rw [c0, Nat.mul_add_div_of_lt (hc.trans_le (X.len_le t))]

/-- The length of a filtered range, as the size of a set. -/
theorem length_filter_range (k : ℕ) (f : ℕ → Bool) :
    ((List.range k).filter f).length = #{i ∈ range k | f i = true} := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans". -/
theorem sum_fails_le (hv : X.Valid) :
    ∑ t ∈ range X.m, X.fails t ≤ (triOf X.n X.AB X.BC X.AC).F X.p := by
  -- The failed scans, as a set of pairs (instance, query pair).
  set failed : Finset (Σ _ : ℕ, ℕ) :=
    (range X.m).sigma fun t => {i ∈ range (X.w t) | (X.acc t i && !X.hit t i) = true} with hfailed
  have hcard : ∑ t ∈ range X.m, X.fails t = failed.card := by
    rw [hfailed, Finset.card_sigma]
    exact Finset.sum_congr rfl fun t _ => length_filter_range _ _
  have hmem : ∀ z ∈ failed,
      z.1 < X.m ∧ z.2 < X.w z.1 ∧ X.acc z.1 z.2 = true ∧ X.hit z.1 z.2 = false := by
    intro z hz
    simpa [hfailed, and_assoc] using hz
  rw [hcard]
  classical
  refine Finset.card_le_card_of_forall_subsingleton
    (fun z τ => τ.1.val = X.rowOf z.1 z.2 ∧ τ.2.1.val = X.colOf z.1 z.2 ∧
      ∃ c < X.len z.1, τ.2.2.val = X.c0 z.1 + c) (fun z hz => ?_) ?_
  · obtain ⟨ht, hi, hacc, hhit⟩ := hmem z hz
    obtain ⟨c, hc, hdvd, hne⟩ := exists_false_positive hv ht hi hacc hhit
    have hpiece := hv.piece_le ht
    exact ⟨(⟨_, hv.rowOf_lt ht hi⟩, ⟨_, hv.colOf_lt ht hi⟩, ⟨X.c0 z.1 + c, by omega⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hdvd⟩, rfl, rfl, c, hc, rfl⟩
  · rintro τ _ z ⟨hz, hrow, hcol, c, hc, hvertex⟩ z' ⟨hz', hrow', hcol', c', hc', hvertex'⟩
    obtain ⟨ht, hi, -, -⟩ := hmem z hz
    obtain ⟨ht', hi', -, -⟩ := hmem z' hz'
    have hplace : X.place z.1 z.2 = X.place z'.1 z'.2 := by
      rw [← rowOf_mul_add_colOf, ← rowOf_mul_add_colOf, ← hrow, ← hcol, hrow', hcol']
    have hpiece : z.1 / X.chunkCount = z'.1 / X.chunkCount := by
      rw [← c0_add_div hc, ← c0_add_div hc', ← hvertex, hvertex']
    obtain ⟨ht_eq, hi_eq⟩ := hv.eq_of_place_eq ht ht' hi hi' hplace hpiece
    exact Sigma.ext ht_eq (heq_of_eq hi_eq)

end HostData


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/





variable {n D g p : ℕ}

theorem sOf_le_sqrt (D : ℕ) : (sOf D : ℝ) ≤ Real.sqrt D := Nat.floor_le (Real.sqrt_nonneg _)

theorem sqrt_lt_sOf_add_one (D : ℕ) : Real.sqrt D < (sOf D : ℝ) + 1 := Nat.lt_floor_add_one _

theorem sOf_pos (hD : 16 ≤ D) : (0 : ℝ) < sOf D := by
  linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD, sqrt_lt_sOf_add_one D]

theorem one_le_gap_mul (D : ℕ) :
    1 ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) := by
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  have := sOf_le_sqrt D
  have hlt := sqrt_lt_sOf_add_one D
  have hinteger : (D : ℝ) + 1 ≤ ((sOf D : ℝ) + 1) ^ 2 := by
    have hreal : (D : ℝ) < ((sOf D : ℝ) + 1) ^ 2 :=
      hsq ▸ pow_lt_pow_left₀ hlt (Real.sqrt_nonneg _) two_ne_zero
    have hnat : D < (sOf D + 1) ^ 2 := by exact_mod_cast hreal
    exact_mod_cast hnat
  calc (1 : ℝ) ≤ ((sOf D : ℝ) + 1) ^ 2 - Real.sqrt D ^ 2 := by linarith [hinteger, hsq]
    _ = ((sOf D : ℝ) + 1 - Real.sqrt D) * ((sOf D : ℝ) + 1 + Real.sqrt D) := by ring
    _ ≤ ((sOf D : ℝ) + 1 - Real.sqrt D) * (2 * Real.sqrt D + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)

theorem sq_lt_mul_queryCap_add (hD : 16 ≤ D) (hDn : D ≤ n)
    (hp : Real.sqrt D / 2 ≤ (p : ℝ)) : n ^ 2 < (sOf D + 1) * queryCap n D + p := by
  have hgap := one_le_gap_mul D
  have hs := sOf_le_sqrt D
  set r := Real.sqrt D with hr
  set δ := (sOf D : ℝ) + 1 - r with hδ
  set x := (n : ℝ) ^ 2 / r with hx
  have hr4 : 4 ≤ r := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hxr : x * r = (n : ℝ) ^ 2 := div_mul_cancel₀ _ (by linarith)
  have hx3 : r ^ 3 ≤ x := by
    rw [hx, le_div_iff₀ (by linarith)]
    calc r ^ 3 * r = (r ^ 2) ^ 2 := by ring
      _ = (D : ℝ) ^ 2 := by rw [hr, Real.sq_sqrt (Nat.cast_nonneg D)]
      _ ≤ (n : ℝ) ^ 2 := by gcongr
  have hxδ : r / 2 + 1 ≤ x * δ := by
    refine le_of_mul_le_mul_right ?_ (show 0 < 2 * r + 1 by linarith)
    calc (r / 2 + 1) * (2 * r + 1) ≤ r ^ 3 := by
          linarith [mul_le_mul_of_nonneg_right hr4 (sq_nonneg r),
            mul_le_mul_of_nonneg_right hr4 (show 0 ≤ r by linarith)]
      _ ≤ x * 1 := by rw [mul_one]; exact hx3
      _ ≤ x * (δ * (2 * r + 1)) :=
          mul_le_mul_of_nonneg_left hgap (le_trans (by positivity) hx3)
      _ = x * δ * (2 * r + 1) := by ring
  have hfloor : x < (queryCap n D : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmain : (n : ℝ) ^ 2 < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
    calc (n : ℝ) ^ 2 = x * r := hxr.symm
      _ ≤ x * r + x * δ - ((sOf D : ℝ) + 1) + r / 2 := by linarith [hxδ, hs]
      _ = ((sOf D : ℝ) + 1) * (x - 1) + r / 2 := by rw [hδ]; ring
      _ < ((sOf D : ℝ) + 1) * (queryCap n D : ℝ) + p :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (by linarith [hfloor]) (by positivity)) hp
  exact_mod_cast hmain

theorem le_sOf_and_sqrt_le (hD : 16 ≤ D) (hDn : D ≤ n) :
    3 * Real.sqrt D / 4 ≤ (sOf D : ℝ) ∧ Real.sqrt D ≤ 2 * (n : ℝ) / 3 := by
  have := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hsqrtn := Real.four_le_sqrt_natCast_of_sixteen_le (hD.trans hDn)
  constructor
  · calc 3 * Real.sqrt D / 4 ≤ Real.sqrt D - 1 := by linarith
      _ ≤ (sOf D : ℝ) := by linarith [sqrt_lt_sOf_add_one D]
  · calc Real.sqrt D ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hDn)
      _ ≤ 2 * (n : ℝ) / 3 := by
          linarith [mul_le_mul_of_nonneg_right hsqrtn (Real.sqrt_nonneg n),
            Real.mul_self_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem HostData.m_le {n D g p : ℕ} {AB BC AC : List ℤ} (h : BigCase n D g)
    (hp : p ∈ primesInRange D) :
    (⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩ : HostData).m ≤ 4 * n * g := by
  obtain ⟨hD, hDn, hg, -⟩ := h
  obtain ⟨hprime, hge, hlt⟩ := mem_primesInRange.mp hp
  have hD1 : 1 ≤ D := by omega
  have hcap : 1 ≤ queryCapNat n D := by
    rw [queryCapNat, Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]
    have : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
    omega
  set X : HostData := ⟨n, D, p, pieceSizeNat D g, queryCapNat n D, AB, BC, AC⟩
  have hsum : X.chunkCount * queryCap n D + p ≤ n ^ 2 + p * queryCap n D := by
    rw [← queryCapNat_eq n hD1, sq]
    exact length_chunkTab_mul_le hcap fun i _ => by
      rw [HostData.RAB, getD_residList]
      exact resid_lt hprime.ne_zero _
  have hpairs := sq_lt_mul_queryCap_add hD hDn hge
  have hchunks_nat : X.chunkCount ≤ p + sOf D := by
    by_contra hmany
    have hmul : (p + sOf D + 1) * queryCap n D ≤ X.chunkCount * queryCap n D :=
      Nat.mul_le_mul_right _ (by omega)
    rw [show (p + sOf D + 1) * queryCap n D = p * queryCap n D + (sOf D + 1) * queryCap n D by
      ring] at hmul
    omega
  have hchunks : (X.chunkCount : ℝ) ≤ 2 * Real.sqrt D := by
    have : (X.chunkCount : ℝ) ≤ (p : ℝ) + (sOf D : ℝ) := by exact_mod_cast hchunks_nat
    linarith [sOf_le_sqrt D]
  obtain ⟨hs, hsqrt⟩ := le_sOf_and_sqrt_le hD hDn
  have hs0 := sOf_pos hD
  have hq : 1 ≤ pieceSizeNat D g := by
    have : 4 ≤ Nat.sqrt D := Nat.le_sqrt.2 (by omega)
    exact (Nat.lt_ceilDiv_iff hg).2 (by omega)
  have hpieces_mul : (X.h : ℝ) * (sOf D : ℝ) ≤ (n : ℝ) * g + (sOf D : ℝ) := by
    have h1 : X.h * pieceSizeNat D g < n + pieceSizeNat D g := Nat.ceilDiv_mul_lt (a := n) hq
    have h1' : (X.h - 1) * pieceSizeNat D g ≤ n := by
      rw [Nat.sub_mul, Nat.one_mul]
      omega
    have h2 : sOf D ≤ pieceSizeNat D g * g := by
      rw [sOf_eq_sqrt, pieceSizeNat]
      exact (Nat.ceilDiv_le_iff hg).1 le_rfl
    have h3 : (X.h - 1) * sOf D ≤ n * g :=
      (Nat.mul_le_mul_left _ h2).trans (by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right g h1')
    rw [Nat.sub_mul, Nat.one_mul] at h3
    exact_mod_cast (by omega : X.h * sOf D ≤ n * g + sOf D)
  have hpieces : (X.h : ℝ) ≤ (n : ℝ) * g / (sOf D : ℝ) + 1 := by
    rw [← le_div_iff₀ hs0] at hpieces_mul
    linarith [add_div ((n : ℝ) * g) (sOf D : ℝ) (sOf D : ℝ), div_self hs0.ne']
  have hmain : Real.sqrt D * ((n : ℝ) * g / (sOf D : ℝ)) ≤ 4 / 3 * ((n : ℝ) * g) := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    calc Real.sqrt D * ((n : ℝ) * g) = 4 / 3 * ((n : ℝ) * g) * (3 * Real.sqrt D / 4) := by ring
      _ ≤ 4 / 3 * ((n : ℝ) * g) * (sOf D : ℝ) := by gcongr
  have hng : (n : ℝ) ≤ (n : ℝ) * g := le_mul_of_one_le_right (Nat.cast_nonneg n) (by exact_mod_cast hg)
  have hcard : (X.m : ℝ) ≤ ((4 * n * g : ℕ) : ℝ) := by
    push_cast [HostData.m]
    calc (X.h : ℝ) * (X.chunkCount : ℝ) ≤ (X.h : ℝ) * (2 * Real.sqrt D) := by gcongr
      _ = 2 * Real.sqrt D * (X.h : ℝ) := by ring
      _ ≤ 2 * Real.sqrt D * ((n : ℝ) * g / (sOf D : ℝ) + 1) := by gcongr
      _ ≤ 4 * (n : ℝ) * g := by linarith [hmain, hng, hsqrt]
  exact_mod_cast hcard


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/






theorem not_smallCase_iff {n D g : ℕ} : ¬ SmallCase n D g ↔ BigCase n D g := by
  unfold SmallCase
  exact ⟨fun h => ⟨by omega, by omega, by omega, by omega⟩,
    fun ⟨_, _, _, _⟩ => by omega⟩

theorem hostWord_le {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) :
    ((hostWord a b n U D g : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast Nat.le_add_right _ _) hok.word

theorem le_word_of_le_hostWord {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {n U fr D g : ℕ}
    (hok : (hostNeedAt a b need n U D g).Ok lim fr d) {z : ℕ}
    (hz : z ≤ hostWord a b n U D g := by unfold hostWord; omega) : ((z : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hz) (hostWord_le hok)

theorem choosePre_of_ok {lim : Limits} {d a b : ℕ} {need : List ℕ → Need} {x : TriInst} {μ : ℕ → ℤ}
    {fr D g : ℕ} (hpre : x.Pre μ fr) (hok : (hostNeedAt a b need x.n x.U D g).Ok lim fr d) :
    ChoosePrimePre lim (d + 1) μ x D fr := by
  have hcells := hok.cells
  have hdepth := hok.depth
  simp only [hostNeedAt] at hcells hdepth
  exact
    { space_le := hok.space
      inst := hpre
      cells := by omega
      wordD := le_word_of_le_hostWord hok
      wordU := le_word_of_le_hostWord hok
      wordN := le_word_of_le_hostWord hok
      wordDbl := le_word_of_le_hostWord hok
      wordStr := le_word_of_le_hostWord hok
      wordSum := le_word_of_le_hostWord hok
      depth := by omega }

theorem F_le_falsePositiveBound {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) :
    (triOf x.n x.AB x.BC x.AC).F (chosenPrime x.n D x.AB x.BC x.AC)
      ≤ falsePositiveBound x.n x.U D :=
  Nat.le_floor (F_chosenPrime_le h.sixteen_le h.le_n hpre.U_pos hpre.leAB hpre.leBC hpre.leAC)

theorem et17Addr_spec {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} (x : TriInst) (X : HostData)
    {fr : ℕ} {g s : ℤ} (hw : (lim.space : ℤ) ≤ lim.word) (htop : aFr X x.U fr ≤ lim.space) :
    Ends lim P d et17Addr
      ⟨frame [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s,
        (X.p : ℤ), (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], μ⟩
      et17Addr.blockCost fun σ' => σ' = ⟨frame (Et17.locals x X fr g s 0 0), μ⟩ := by
  have := host_places X x.U fr
  have : (0 : ℤ) ≤ (X.n : ℤ) * X.n := by positivity
  have : (0 : ℤ) ≤ (X.n : ℤ) * X.D := by positivity
  unfold et17Addr
  light_set (X.n * X.n : ℕ)
  light_set (X.n * X.D : ℕ)
  light_set (X.n * X.n + X.p : ℕ)
  light_set (aRab X x.U fr)
  light_set (aRbc X x.U fr)
  light_set (aRac X x.U fr)
  light_set (aCls X x.U fr)
  light_set (aCur X x.U fr)
  light_set (aQi X x.U fr)
  light_set (aQj X x.U fr)
  light_set (aCr X x.U fr)
  light_set (aCl X x.U fr)
  light_set (aCw X x.U fr)
  light_set (aX X x.U fr)
  light_set (aY X x.U fr)
  light_set (aOut X x.U fr)
  light_set (aFr X x.U fr)
  rfl

def strNumsAt (o : ℕ) : StrNums := ⟨o + 12, o + 13, o + 14, o + 15, o + 16⟩

def cpNumsAt (o : ℕ) : CpNums := ⟨o + 5, o + 6, o + 7, o + 8, o + 9, o + 10, o + 11, strNumsAt o⟩

def chNumsAt (o : ℕ) : ChNums := ⟨o + 3, o + 4, o + 17, cpNumsAt o, o, o + 28⟩

def et17NumsAt (pS pD pG o : ℕ) : Et17Nums :=
  ⟨pD, pG, o, o + 1, o + 18, o + 19, o + 20, o + 4, o + 5, o + 6, o + 7, o + 21, o + 22,
    pS, o + 23, o + 24, chNumsAt o⟩

namespace Et17

/-- A call that puts its result into the local Small. -/
theorem setLocal_res (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res r : ℤ) :
    setLocal (locals x X fr g s nch res) Small r = locals x X fr g s nch r := rfl

/-- What the third part needs, for the data X of the loop: the limits, the prime, and the three
matrices below the free pointer. -/
structure Ready (lim : Limits) (d : ℕ) (x : TriInst) (X : HostData) (μ : ℕ → ℤ) (fr : ℕ) :
    Prop where
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  prime : 1 ≤ X.p
  word : ((X.p * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  top : aFr X x.U fr < lim.space
  segAB : Seg μ x.ab X.AB
  segBC : Seg μ x.bc X.BC
  segAC : Seg μ x.ac X.AC
  lenAB : X.AB.length = X.n * X.n
  lenBC : X.BC.length = X.n * X.n
  lenAC : X.AC.length = X.n * X.n
  leAB : AbsLe X.AB x.U
  leBC : AbsLe X.BC x.U
  leAC : AbsLe X.AC x.U
  belowAB : x.ab + X.n * X.n ≤ fr
  belowBC : x.bc + X.n * X.n ≤ fr
  belowAC : x.ac + X.n * X.n ≤ fr

variable {lim : Limits} {P : Program} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}

/-- The places of the lists of residues: they stand one after the other behind the table of doubles,
and end where the array of the classes begins, below the free pointer of the solver. -/
theorem resid_places (X : HostData) (U fr : ℕ) :
    aRab X U fr = fr + (bitLen U + 1) ∧ aRbc X U fr = aRab X U fr + X.n * X.n ∧
      aRac X U fr = aRbc X U fr + X.n * X.n ∧ aCls X U fr = aRac X U fr + X.n * X.n ∧
      aCls X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega

/-- The places of the arrays of the classes and the chunks: they stand one after the other behind
the lists of residues, and end at aX, the first matrix of the instance that is handed to the solver,
below the free pointer of the solver. -/
theorem class_places (X : HostData) (U fr : ℕ) :
    aRbc X U fr = aRab X U fr + X.n * X.n ∧ aRac X U fr = aRbc X U fr + X.n * X.n ∧
      aCls X U fr = aRac X U fr + X.n * X.n ∧ aCur X U fr = aCls X U fr + (X.p + 1) ∧
      aQi X U fr = aCur X U fr + X.p ∧ aQj X U fr = aQi X U fr + X.n * X.n ∧
      aCr X U fr = aQj X U fr + X.n * X.n ∧ aCl X U fr = aCr X U fr + (X.n * X.n + X.p) ∧
      aCw X U fr = aCl X U fr + (X.n * X.n + X.p) ∧ aX X U fr = aCw X U fr + (X.n * X.n + X.p) ∧
      aX X U fr ≤ aFr X U fr := by
  have := host_places X U fr
  omega

/-- The memory after the first four calls: the three lists of residues; only cells between the free
pointer and the array of the classes have changed. -/
structure ResidMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  rab : SegN μ' (aRab X x.U fr) X.RAB
  rbc : SegN μ' (aRbc X x.U fr) X.RBC
  rac : SegN μ' (aRac X x.U fr) X.RAC
  same : SameOn (fun c => c < fr ∨ aCls X x.U fr ≤ c) μ μ'

/-- The memory after the next two calls: the pairs, class after class, and the table of the chunks;
only cells between the array of the classes and aX, the first matrix of the instance that is handed
to the solver, have changed. -/
structure ClassMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  qi : SegN μ' (aQi X x.U fr) X.QI
  qj : SegN μ' (aQj X x.U fr) X.QJ
  cr : SegN μ' (aCr X x.U fr) (X.CT.map fun c => c.residue)
  cl : SegN μ' (aCl X x.U fr) (X.CT.map fun c => c.start)
  cw : SegN μ' (aCw X x.U fr) (X.CT.map fun c => c.len)
  same : SameOn (fun c => c < aCls X x.U fr ∨ aX X x.U fr ≤ c) μ μ'

/-- What residues needs, for a matrix below the free pointer and a destination between the table of
doubles and the end of the arrays. -/
theorem Ready.residuesPre (h : Ready lim d x X μ fr) {μ' : ℕ → ℤ} {src dst : ℕ} {l : List ℤ}
    (hdbl : Seg μ' fr (dblList X.p (bitLen x.U))) (hsrc : Seg μ' src l)
    (hlen : l.length = X.n * X.n) (hle : AbsLe l x.U) (hbelow : src + X.n * X.n ≤ fr)
    (hlow : fr + (bitLen x.U + 1) ≤ dst := by omega)
    (hhigh : dst + X.n * X.n < lim.space := by omega) :
    ResiduesPre lim μ' src dst (X.n * X.n) fr X.p (bitLen x.U) x.U l :=
  { hw := h.space
    prime := h.prime
    segDbl := hdbl
    segSrc := hsrc
    length := hlen
    le := hle
    lt := Nat.lt_size_self _
    spaceDbl := by omega
    spaceSrc := by omega
    spaceDst := by omega
    count := by omega
    apartSrc := by omega
    apartDbl := by omega
    word := h.word }

/-- **The table of doubles and the three lists of residues**, followed by the rest t of the text. -/
theorem resid_then {pDbl pResid pResidues : ℕ} (hDbl : P[pDbl]? = some dblTableBody)
    (hResid : P[pResid]? = some residBody) (hResidues : P[pResidues]? = some (residuesBody pResid))
    (hr : Ready lim d x X μ fr) {g s : ℤ} {t : Stmt} {T : ℕ} {Q : State → Prop}
    (h : ∀ res μ', ResidMem x X fr μ μ' → Ends lim P d t ⟨frame (locals x X fr g s 0 res), μ'⟩
      (T - (tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26)) Q)
    (hT : tDblTable (bitLen x.U) + 3 * tResidues (X.n * X.n) (bitLen x.U) + 26 ≤ T) :
    Ends lim P d
      (.call pDbl [v Free, v ThePrime, v Bits] Small ;;
        .call pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] Small ;;
        .call pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] Small ;;
        .call pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] Small ;; t)
      ⟨frame (locals x X fr g s 0 0), μ⟩ T Q := by
  have := hr.depth
  have := hr.top
  have := resid_places X x.U fr
  have lenAB := hr.lenAB
  have lenBC := hr.lenBC
  have lenAC := hr.lenAC
  have := hr.belowAB
  have := hr.belowBC
  have := hr.belowAC
  have hword : ((X.p * 2 ^ bitLen x.U : ℕ) : ℤ) ≤ lim.word := le_trans (by
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)))
    hr.word
  have : (dblList X.p (bitLen x.U)).length = bitLen x.U + 1 := by simp [dblList]
  have : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  -- Small := pDbl(Free, ThePrime, Bits)
  light_call (dblTable_meets (dst := fr) (p := X.p) (len := bitLen x.U) hDbl hr.space
    (by omega) hword) with r₁ μ₁ ⟨hdbl, same₁⟩
  rw [setLocal_res]
  -- Small := pResidues(AdrAB, ResAB, SizeSq, Free, Bits)
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRab X x.U fr) hdbl hr.segAB.keep hr.lenAB hr.leAB hr.belowAB)) with r₂ μ₂ ⟨hrab, same₂⟩
  rw [setLocal_res]
  -- Small := pResidues(AdrBC, ResBC, SizeSq, Free, Bits)
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRbc X x.U fr) hdbl.keep hr.segBC.keep hr.lenBC hr.leBC hr.belowBC))
    with r₃ μ₃ ⟨hrbc, same₃⟩
  rw [setLocal_res]
  -- Small := pResidues(AdrAC, ResAC, SizeSq, Free, Bits)
  light_call (residues_meets hResidues hResid (by omega) (hr.residuesPre
    (dst := aRac X x.U fr) hdbl.keep hr.segAC.keep hr.lenAC hr.leAC hr.belowAC))
    with r₄ μ₄ ⟨hrac, same₄⟩
  rw [setLocal_res]
  exact (h r₄ μ₄ ⟨hrab.keep, hrbc.keep, hrac, by light_keep⟩).mono (by simp; omega) fun _ hQ => hQ

/-- There are at most n² + p chunks. -/
theorem Ready.chunkCount_le (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap) :
    X.chunkCount ≤ X.n * X.n + X.p :=
  length_chunkTab_le_add hcap fun i hi => lt_of_mem_residList hr.prime (by
    rw [List.getD_eq_getElem _ _ (by rw [HostData.RAB, length_residList, hr.lenAB]; exact hi)]
    exact List.getElem_mem _)

/-- **The classes and the chunks**, followed by the rest t of the text. -/
theorem classes_then {pClasses pChunks : ℕ} (hClasses : P[pClasses]? = some classesBody)
    (hChunks : P[pChunks]? = some chunksBody) (hr : Ready lim d x X μ fr) (hcap : 1 ≤ X.cap)
    {μ₁ : ℕ → ℤ} (hrab : SegN μ₁ (aRab X x.U fr) X.RAB) {g s res : ℤ} {t : Stmt} {T : ℕ}
    {Q : State → Prop}
    (h : ∀ res' μ', ClassMem x X fr μ₁ μ' → Ends lim P d t
      ⟨frame (locals x X fr g s X.chunkCount res'), μ'⟩
      (T - (tClasses X.n X.p + tChunks X.p X.chunkCount + 17)) Q)
    (hT : tClasses X.n X.p + tChunks X.p X.chunkCount + 17 ≤ T) :
    Ends lim P d
      (.call pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] Small ;;
        .call pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks ;; t)
      ⟨frame (locals x X fr g s 0 res), μ₁⟩ T Q := by
  have hchunks : X.chunkCount = (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length := rfl
  rw [hchunks] at h hT
  have := hr.depth
  have := hr.prime
  have := hr.top
  have := class_places X x.U fr
  have lenRAB : X.RAB.length = X.n * X.n := (length_residList _ _).trans hr.lenAB
  have ltRAB : ∀ r ∈ X.RAB, r < X.p := fun r hmem => lt_of_mem_residList (by omega) hmem
  have hroom : (chunkTabOf X.p X.cap (classStarts X.n X.p X.RAB)).length ≤ X.n * X.n + X.p :=
    hr.chunkCount_le hcap
  -- Small := pClasses(ResAB, Size, ThePrime, Cls, Cur, Rows, Cols)
  refine Ends.callToThen (classes_meets hClasses hr.space
    { rab := aRab X x.U fr, n := X.n, p := X.p, cls := aCls X x.U fr, cur := aCur X x.U fr,
      qi := aQi X x.U fr, qj := aQj X x.U fr, RAB := X.RAB } μ₁
    { seg := hrab, len := lenRAB, lt := ltRAB }) ?_ (by simp)
  rintro r₁ μ₂ ⟨hcls, hqi, hqj, same₂⟩
  dsimp only at hcls hqi hqj same₂
  rw [setLocal_res]
  -- NumChunks := pChunks(Cls, ThePrime, Cap, TabR, TabL, TabW)
  refine Ends.callToThen (chunks_meets hChunks hr.space
    { cls := aCls X x.U fr, p := X.p, cap := X.cap, cr := aCr X x.U fr, cl := aCl X x.U fr,
      cw := aCw X x.U fr, R := X.n * X.n + X.p, B := X.n * X.n, C := classStarts X.n X.p X.RAB } μ₂
    { seg := hcls, len := length_classStarts X.n X.p X.RAB,
      le := fun y hy => le_of_mem_classStarts hy, room := hroom }) ?_ (by simp)
    (hT := by simp only [ChunksArgs.table]; light_time)
  rintro _ μ₃ ⟨rfl, hcr, hcl, hcw, same₃⟩
  simp only [ChunksArgs.table, ChunksArgs.Same] at hcr hcl hcw same₃ ⊢
  have : (sortedIdx X.n X.p X.RAB).length ≤ X.n * X.n := by
    rw [length_sortedIdx_eq]
    exact classStart_le_sq X.n X.RAB X.p
  have keep : ∀ {a : ℕ} {l : List ℕ}, SegN μ₂ a l → a + l.length ≤ aCr X x.U fr → SegN μ₃ a l := by
    intro a l hs hle
    refine Seg.congr hs fun i hi => same₃ _ ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
      (simp only [List.length_map] at hi; omega)
  refine (h r₁ μ₃ ⟨keep hqi (by simp only [HostData.QI, queryRows, List.length_map]; omega),
    keep hqj (by simp only [HostData.QJ, queryCols, List.length_map]; omega), hcr, hcl, hcw,
    fun c hc => ?_⟩).mono (by simp; omega) fun _ hQ => hQ
  exact (same₃ c ⟨by omega, by omega, by omega⟩).trans (same₂ c (by simp only [Outside]; omega))

/-- Where the arrays lie, for the addresses of et17. -/
theorem hostLay_of (hr : Ready lim d x X μ fr) (hchunks : X.chunkCount ≤ X.n * X.n + X.p) :
    HostLay X (hostAddr x X fr) := by
  light_facts hr
  have := host_places X x.U fr
  have : X.D * X.n = X.n * X.D := Nat.mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_⟩
  case refine_13 =>
    have := X.w_le_cap ht
    simp only [hostAddr]
    omega
  all_goals
    simp only [hostAddr]
    omega

/-- The arrays that the loop over the instances reads are in the memory. -/
theorem hostMem_of (hr : Ready lim d x X μ fr) {μ₁ μ₂ : ℕ → ℤ}
    (hresid : ResidMem x X fr μ μ₁) (hclass : ClassMem x X fr μ₁ μ₂) :
    HostMem X (hostAddr x X fr) μ₂ := by
  light_facts hr hresid hclass
  have := resid_places X x.U fr
  have : X.RAC.length = X.n * X.n := (length_residList _ _).trans hr.lenAC
  have : X.RBC.length = X.n * X.n := (length_residList _ _).trans hr.lenBC
  exact
    { segAB := hr.segAB.keep
      segBC := hr.segBC.keep
      segAC := hr.segAC.keep
      segRAC := hresid.rac.keep
      segRBC := hresid.rbc.keep
      segQI := hclass.qi
      segQJ := hclass.qj
      segCR := hclass.cr
      segCL := hclass.cl
      segCW := hclass.cw }

end Et17

end Light.Sec3
end
