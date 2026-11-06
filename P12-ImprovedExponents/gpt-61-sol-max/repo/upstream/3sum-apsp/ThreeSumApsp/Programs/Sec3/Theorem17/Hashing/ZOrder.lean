/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Auto
public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ZOrderFacts
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen

/-!
# Matrices over ℤ[x]/(x^p - 1) in Z-order: the table of places, and P and Q of Theorem 17's proof

spreadTable(dst, N2) writes the table of `spread`: the number with the binary digits of i, read in
base 4.  There is no division: a pointer j = ⌊i/2⌋ and the parity of i are carried along, and
dst[i] = 4 dst[j] + parity (`spreadStep_spec`, `spreadTable_spec`).

buildZ(dst, r, mort, n, N2, p, mx, my), with N2 = 2^K, writes an N2 × N2 matrix of vectors of length
p in Z-order, 4^K p cells in all, whose entry for the pair (x, y), x, y < n, is the unit vector with
its 1 at place r[x n + y], and whose other entries are zero vectors.  Here mort is the address of
the table that spreadTable has written, so that mort[x] = spread x.  The place of the pair (x, y) is
mx · spread x + my · spread y.  With (mx, my) = (2, 1) the pair is (row, column), which gives
"P[a,c] := x^{w(a,c) mod p}"; with (1, 2) it is (column, row), which gives
"Q[c,b] := x^{w(b,c) mod p}" from the residues of w(b,c) stored at b n + c.  (Inside the two quoted
formulas x is the paper's indeterminate, and P and Q are the paper's matrices; in the code `P` is
the program.)  The routine clears the matrix (`buildZClear_spec`) and marks one cell for each pair
(`buildZMark_spec`); `markList_eq_zList` identifies the marked list with the matrix.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The table of places -/


/-- dst[i] := 4 dst[j] + parity; then i, j and the parity go on to i + 1. -/
def spreadStep  :=
  .store (v 0 +' v 2) (k 4 *' M (v 0 +' v 3) +' v 4) ;;
  .ite (v 4 =' k 0) (.set 4 (k 1)) (.set 4 (k 0) ;; .set 3 (v 3 +' k 1)) ;;
  .set 2 (v 2 +' k 1)

/-- spreadTable(dst, N2). -/
def spreadTableBody : Stmt :=
  .ite (k 0 <' v 1) (
    .store (v 0) (k 0) ;;
    .set 2 (k 1) ;;
    .set 3 (k 0) ;;
    .set 4 (k 1) ;;
    .while (v 2 <' v 1) spreadStep)
    .skip

section

variable {μ μ' : Light.Memory} {dst N₂ : ℕ}

variable (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word)
    (hsq : ((N₂ * N₂ : ℕ) : ℤ) ≤ lim.word) (hdst : dst + N₂ ≤ lim.space)

include hw h4 hsq hdst in
/-- **One entry of the table.** -/
theorem spreadStep_spec  {i } (hi0 : 0 < i)
    (hi : i < N₂) (hseg : Seg μ' dst (spreadList i)) :
    Ends lim P d spreadStep ⟨frame [dst, N₂, i, (i / 2 : ℕ), (i % 2 : ℕ)], μ'⟩ 26 fun σ' =>
      σ' = ⟨frame [dst, N₂, (i + 1 : ℕ), ((i + 1) / 2 : ℕ), ((i + 1) % 2 : ℕ)],
        Function.update μ' (dst + i) (spread i : ℕ)⟩ := by
  have hcell : μ' (dst + i / 2) = (spread (i / 2) : ℕ) := seg_spreadList_get hseg (by omega)
  have  := spread_eq i
  have  := (spread_le_sq i).trans (Nat.mul_le_mul hi.le hi.le)
  have  : i % 2 = 0 → (i + 1) / 2 = i / 2 ∧ (i + 1) % 2 = 1 := by omega
  have hodd : i % 2 ≠ 0 → (i + 1) / 2 = i / 2 + 1 ∧ (i + 1) % 2 = 0 := by omega
  generalize i / 2 = j at *
  generalize i % 2 = b at *
  -- dst[i] := 4 dst[j] + parity
  light_store (dst + i) (spread i : ℕ) using hcell
  -- if parity = 0 then parity := 1 else parity := 0; j := j + 1
  -- i := i + 1
  refine Ends.iteThen (fun h0 => ?_) fun h0 => ?_
  · light_block []
  · have h0 := by simpa using h0
    rw [(hodd h0).1, (hodd h0).2]
    exact Ends.seqAssoc
      (Ends.setToThen (0 : ℕ) (Ends.setToThen (j + 1 : ℕ) (Ends.setTo (i + 1 : ℕ) rfl)))

include hw h4 hsq hdst in
/-- **spreadTable**: at most 30 N2 + 17 steps. -/
theorem spreadTable_spec  :
    Ends lim P d spreadTableBody ⟨frame [dst, N₂], μ⟩ (30 * N₂ + 17) fun σ' =>
      Seg σ'.mem dst (spreadList N₂) ∧ SameOutside μ σ'.mem dst N₂ := by
  -- if 0 < N2
  refine Ends.iteLast (fun hpos => ?_) fun hzero => ?_
  swap
  · obtain rfl : N₂ = 0 := by simpa using hzero
    exact Ends.skip ⟨by simp [spreadList], .refl⟩
  have  := by simpa using hpos
  -- dst[0] := 0; i := 1; j := 0; parity := 1
  light_store dst 0
  light_set (1 : ℕ)
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while i < N2; before round r the counter is r + 1
  refine Ends.whileConst (fun r σ => ∃ μ' : Light.Memory,
      σ = ⟨frame [dst, N₂, (r + 1 : ℕ), ((r + 1) / 2 : ℕ), ((r + 1) % 2 : ℕ)], μ'⟩ ∧
      Seg μ' dst (spreadList (r + 1)) ∧ SameOutside μ μ' dst N₂) (N₂ - 1) 26
    ?start ?round ?done (by light_time)
  case start =>
    refine ⟨_, rfl, fun i hi => ?_, SameOutside.refl.update ⟨le_rfl, by omega⟩ _⟩
    obtain rfl : i = 0 := by simpa [spreadList] using hi
    simp [spreadList, spread_zero]
  case done =>
    rintro _ ⟨μ', rfl, hseg, hrest⟩
    rw [show N₂ - 1 + 1 = N₂ by omega] at hseg ⊢
    exact ⟨by light_side, by light_side, hseg, hrest⟩
  case round =>
    rintro r _ hr ⟨μ', rfl, hseg, hrest⟩
    refine ⟨by light_side, by light_side,
      (spreadStep_spec hw h4 hsq hdst (Nat.succ_pos r) (by omega) hseg).mono le_rfl ?_⟩
    rintro _ rfl
    refine ⟨_, rfl, ?_, hrest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hseg.snoc (spread (r + 1) : ℕ)
    rw [length_spreadList] at hsnoc
    rwa [spreadList_succ]

end

/-- **spreadTable** as a procedure. -/
theorem spreadTable_meets {μ} {q dst N2} (hP : P[q]? = some spreadTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (h4 : (4 : ℤ) ≤ lim.word)
    (hsq : ((N2 * N2 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + N2 ≤ lim.space) :
    Meets lim P q d [dst, N2] μ (30 * N2 + 17) fun _ μ' =>
      Seg μ' dst (spreadList N2) ∧ SameOutside μ μ' dst N2 :=
  Meets.of_body hP (spreadTable_spec hw h4 hsq hdst)

/-! ## The matrices -/


/-- The N2 N2 p cells of the matrix are cleared. -/
def buildZClear  :=
  .set 8 (v 0) ;;
  .set 9 (v 0 +' v 4 *' v 4 *' v 5) ;;
  .while (v 8 <' v 9) (.store (v 8) (k 0) ;; .set 8 (v 8 +' k 1))

/-- The pair (x, y) marks its cell: dst[(mx mort[x] + my mort[y]) p + r[t]] := 1. -/
def buildZMark : Stmt :=
  .store
    (v 0 +' (v 6 *' M (v 2 +' v 12) +' v 7 *' M (v 2 +' v 13)) *' v 5
      +' M (v 1 +' v 11))
    (k 1)

/-- buildZ(dst, r, mort, n, N2, p, mx, my). -/
def buildZBody  :=
  buildZClear ;;
  .set 10 (v 3 *' v 3) ;;
  .set 12 (k 0) ;;
  .set 13 (k 0) ;;
  .for 11 (v 10) (buildZMark ;; nextPair 12 13 3)

/-- An upper bound on the number of steps of buildZ. -/
def buildZTime n N2 p := 11 * (N2 * N2 * p) + 50 * (n * n) + 40

/-- What buildZ needs: where the arrays lie, and what they hold.  The matrix has N2 = 2^K rows and
columns, so 4^K entries of p cells each, and R is the list of the n² residues that stand at r. -/
structure BuildZPre (lim : Limits) (μ : Light.Memory) (dst r mort n K p : ℕ) (R : List ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  res : IndexAt μ r R (n * n) p lim.space
  table : ListAt μ mort (spreadList (2 ^ K)) (2 ^ K) lim.space
  n_le : n ≤ 2 ^ K
  p_pos : 0 < p
  dst_le : dst + 4 ^ K * p < lim.space
  apartR : Apart dst (4 ^ K * p) r (n * n)
  apartM : Apart dst (4 ^ K * p) mort (2 ^ K)

/-! ### The pure side: a list of zeros in which places are marked one after the other -/

/-- The list of `len` zeros in which the places `idx 0, …, idx (t - 1)` have been set to 1. -/
def markList (len : ℕ) (idx : ℕ → ℕ) : ℕ → List ℤ
  | 0 => List.replicate len 0
  | t + 1 => (markList len idx t).set (idx t) 1

theorem length_markList len idx t : (markList len idx t).length = len := by
  induction t with
  | zero => simp [markList]
  | succ t ih => simp [markList, ih]


/-- An entry of the list is 1 if its place has been marked, and 0 if not. -/
theorem getD_markList {len } (idx ) (t ) {i } (hi : i < len) :
    (markList len idx t).getD i 0 = if ∃ s < t, idx s = i then 1 else 0 := by
  induction t with
  | zero => simp [markList, List.getD_eq_getElem?_getD, hi]
  | succ t ih =>
    rw [markList, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases h : idx t = i
    · ram_safe [length_markList]
    · rw [if_neg h, ← List.getD_eq_getElem?_getD, ih]
      refine if_congr ⟨fun ⟨s, hs, e⟩ => ⟨s, by omega, e⟩, fun ⟨s, hs, e⟩ => ⟨s, ?_, e⟩⟩ rfl rfl
      grind

theorem getD_vunit {p k s} (hs : s < p) : (vunit p k).getD s 0 = if s = k then 1 else 0 := by
  simp_all [vunit]

theorem getD_zeros p s : (zeros p).getD s 0 = 0 := by
  simp_all

/-- A unit vector and the zero vector have p entries. -/
theorem length_unitOrZero c [Decidable c] p k :
    (if c then vunit p k else zeros p).length = p := by
  ram_safe [vunit]

/-- **A matrix of unit vectors, by marking.**  The pairs are numbered by `t < m`; pair number `t`
stands in row `ρ t` and column `κ t`, and `τ` gives the number of the pair in a row and a column. -/
theorem markList_eq_zList {n K p m} (R : List ℕ) (ρ κ : ℕ → ℕ) (τ : Light.SolverTime)
    (hR : ∀ t < m, R.getD t 0 < p) (hcoords : ∀ t < m, ρ t < n ∧ κ t < n ∧ τ (ρ t) (κ t) = t)
    (hnumber : ∀ a < n, ∀ c < n, τ a c < m ∧ ρ (τ a c) = a ∧ κ (τ a c) = c) :
    markList (4 ^ K * p) (fun t => zIdx (ρ t) (κ t) * p + R.getD t 0) m
      = zList K fun a c => if a < n ∧ c < n then vunit p (R.getD (τ a c) 0) else zeros p := by
  have hlenM : ∀ a c,
      (if a < n ∧ c < n then vunit p (R.getD (τ a c) 0) else zeros p).length = p :=
    fun _ _ => length_unitOrZero _ _ _
  refine List.ext_getElem (by rw [length_markList, length_zList _ _ hlenM]) fun i hi₁ hi₂ => ?_
  have hi := by rwa [length_markList] at hi₁
  have hp : 0 < p := by
    grind
  rw [← List.getD_eq_getElem _ 0 hi₁, ← List.getD_eq_getElem _ 0 hi₂, getD_markList _ _ hi]

  have hs : i % p < p := Nat.mod_lt _ hp
  have hsplit := (Nat.div_add_mod' i p).symm
  have hget :
      (zList K fun a c => if a < n ∧ c < n then vunit p (R.getD (τ a c) 0) else zeros p).getD i 0 =
        (if zRow (i / p) < n ∧ zCol (i / p) < n then
          vunit p (R.getD (τ (zRow (i / p)) (zCol (i / p))) 0) else zeros p).getD (i % p) 0 := by
    conv_lhs => rw [hsplit]
    exact List.getD_flatMap_range _ (fun _ _ => hlenM _ _) (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)) hs 0
  rw [hget]
  have  : ∀ t < m, zIdx (ρ t) (κ t) * p + R.getD t 0 = i → zIdx (ρ t) (κ t) = i / p :=
    fun t ht e => by
      rw [← e, Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt (hR t ht), Nat.add_zero]
  by_cases hac : zRow (i / p) < n ∧ zCol (i / p) < n
  · obtain ⟨g1, g2, g3⟩ := hnumber _ hac.1 _ hac.2
    rw [if_pos hac, getD_vunit hs]
    refine if_congr ⟨?_, fun e => ⟨_, g1, ?_⟩⟩ rfl rfl
    · grind [zRow_zIdx, zCol_zIdx]
    · grind [zIdx_zRow_zCol]
  · rw [if_neg hac, getD_zeros, if_neg]
    rintro ⟨t, ht, e⟩
    grind [zRow_zIdx, zCol_zIdx]

/-- The first matrix of the proof of Theorem 17, P, by marking. -/
theorem markList_eq_matPList {n K p} R (hR : ∀ t < n * n, R.getD t 0 < p) :
    markList (4 ^ K * p) (fun t => (2 * spread (t / n) + 1 * spread (t % n)) * p + R.getD t 0)
      (n * n) = matPList n p K R := by
  have h := markList_eq_zList (K := K) (m := n * n) R (fun t => t / n) (fun t => t % n)
    (fun a c => a * n + c) hR
    (fun t ht => ⟨Nat.div_lt_of_lt_mul' ht, Nat.mod_lt_of_lt_mul ht, Nat.div_add_mod' _ _⟩)
      fun a ha c hc =>
      ⟨Nat.mul_add_lt_mul ha hc, Nat.mul_add_div_of_lt hc, Nat.mul_add_mod_of_lt hc⟩
  simpa only [zIdx, Nat.one_mul, matPList] using h

/-- The second matrix of the proof of Theorem 17, Q, by marking. -/
theorem markList_eq_matQList {n K p} R (hR : ∀ t < n * n, R.getD t 0 < p) :
    markList (4 ^ K * p) (fun t => (1 * spread (t / n) + 2 * spread (t % n)) * p + R.getD t 0)
      (n * n) = matQList n p K R := by
  have h := markList_eq_zList (K := K) (m := n * n) R (fun t => t % n) (fun t => t / n)
    (fun c b => b * n + c) hR
    (fun t ht => ⟨Nat.mod_lt_of_lt_mul ht, Nat.div_lt_of_lt_mul' ht, Nat.div_add_mod' _ _⟩)
    fun c hc b hb => ⟨Nat.mul_add_lt_mul hb hc, Nat.mul_add_mod_of_lt hc, Nat.mul_add_div_of_lt hc⟩
  simpa only [zIdx, Nat.one_mul, Nat.add_comm (spread (_ / n)), matQList] using h

/-! ### The program -/

section

variable {μ μ' : Light.Memory} {dst r mort n K p mx my : ℕ} {R : List ℕ}

namespace BuildZPre

variable (pre : BuildZPre lim μ dst r mort n K p R) (h : SameOutside μ μ' dst (4 ^ K * p))

include pre h in
/-- The residues lie outside the matrix, so they can be read at any time. -/
theorem readR
    {t} (ht : t < n * n) : μ' (r + t) = (R.getD t 0 : ℕ) := by
  light_facts pre
  exact pre.res.keep.read ht

include pre h in
/-- The table of places lies outside the matrix, so it can be read at any time. -/
theorem readM
    {x} (hx : x < n) : μ' (mort + x) = (spread x : ℕ) := by
  light_facts pre
  exact seg_spreadList_get pre.table.keep.seg (by omega)

end BuildZPre

/-- **The matrix is cleared.** -/
theorem buildZClear_spec (hw : (lim.space : ℤ) ≤ lim.word) {N₂ len : ℕ}
    (hlen : N₂ * N₂ * p = len) (hsq : N₂ * N₂ ≤ len) (hspace : dst + len < lim.space) :
    Ends lim P d buildZClear ⟨frame [dst, r, mort, n, N₂, p, mx, my], μ⟩ (11 * len + 14) fun σ' =>
      ∃ μ' : Light.Memory,
        σ' = ⟨frame [dst, r, mort, n, N₂, p, mx, my, (dst + len : ℕ), (dst + len : ℕ)], μ'⟩ ∧
        Seg μ' dst (List.replicate len 0) ∧ SameOutside μ μ' dst len := by
  have  : (N₂ : ℤ) * N₂ * p = len := mod_cast hlen
  -- ptr := dst; end := dst + N2 N2 p
  light_set (dst : ℕ)
  light_set (dst + len : ℕ)
  -- while ptr < end
  refine Ends.whileConst (fun i σ => ∃ μ' : Light.Memory,
      σ = ⟨frame [dst, r, mort, n, N₂, p, mx, my, (dst + i : ℕ), (dst + len : ℕ)], μ'⟩ ∧
      Seg μ' dst (List.replicate i 0) ∧ SameOutside μ μ' dst len) len 7
    ⟨μ, rfl, by simp, .refl⟩ ?round ?done (by light_time)
  case done =>
    simp_all
  case round =>
    rintro i _ hi ⟨μ', rfl, hseg, hrest⟩
    refine ⟨by light_side, by light_side, ?_⟩
    -- mem[ptr] := 0; ptr := ptr + 1
    light_store (dst + i) 0
    light_set (dst + i + 1 : ℕ)
    refine ⟨_, rfl, ?_, hrest.update ⟨by omega, by omega⟩ _⟩
    have hsnoc := hseg.snoc 0
    rw [List.length_replicate] at hsnoc
    rwa [List.replicate_succ']

variable (pre : BuildZPre lim μ dst r mort n K p R)
    (hplace : ∀ x < n, ∀ y < n, mx * spread x + my * spread y < 4 ^ K)

include pre hplace in
/-- **The pair number t marks its cell.** -/
theorem buildZMark_spec  {t : ℕ} (ht : t < n * n)
    (ptr e : ℤ) (hrest : SameOutside μ μ' dst (4 ^ K * p)) :
    Ends lim P d buildZMark
      ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my, ptr, e, (n * n : ℕ), t, (t / n : ℕ),
        (t % n : ℕ)], μ'⟩ 24 fun σ' =>
      σ' = ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my, ptr, e, (n * n : ℕ), t, (t / n : ℕ),
        (t % n : ℕ)], Function.update μ'
          (dst + ((mx * spread (t / n) + my * spread (t % n)) * p + R.getD t 0)) 1⟩ := by
  light_facts pre pre.res pre.table
  have hrow := Nat.div_lt_of_lt_mul' ht
  have hcol := Nat.mod_lt_of_lt_mul ht
  have hreadX := pre.readM hrest hrow
  have hreadY := pre.readM hrest hcol
  have hreadR := pre.readR hrest ht
  have hidx := Nat.mul_add_lt_mul (hplace _ hrow _ hcol) (pre.res.getD_lt ht)
  have  := hplace _ hrow _ hcol
  have  : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ pre.p_pos
  generalize R.getD t 0 = rho at *
  generalize t / n = x at *
  generalize t % n = y at *
  generalize spread x = sx at *
  generalize spread y = sy at *
  have  : ((mx : ℤ) * sx + my * sy) * p + rho < (4 ^ K * p : ℕ) := mod_cast hidx
  have  : (0 : ℤ) ≤ ((mx : ℤ) * sx + my * sy) * p := by positivity
  exact Ends.storeTo (dst + ((mx * sx + my * sy) * p + rho)) 1 rfl
    (by light_side [hreadX, hreadY, hreadR])

include pre hplace in
/-- **buildZ**, for any two multipliers that keep the places inside the matrix. -/
theorem buildZ_spec  :
    Ends lim P d buildZBody ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my], μ⟩
      (buildZTime n (2 ^ K) p) fun σ' =>
      Seg σ'.mem dst (markList (4 ^ K * p)
        (fun t => (mx * spread (t / n) + my * spread (t % n)) * p + R.getD t 0) (n * n)) ∧
        SameOutside μ σ'.mem dst (4 ^ K * p) := by
  light_facts pre pre.res pre.table
  have h44 : 2 ^ K * 2 ^ K = 4 ^ K := by rw [← mul_pow]; norm_num
  have  : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ pre.p_pos

  unfold buildZTime
  rw [h44]
  -- the matrix is cleared
  light_piece (buildZClear_spec pre.space_le (by rw [h44]) (by omega) pre.dst_le)
    with _ ⟨μ₁, rfl, hzero, hrest⟩
  -- nn := n n; x := 0; y := 0
  light_set (n * n : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- for t < nn
  refine Ends.for (fun t σ => ∃ μ' : Light.Memory,
      σ = ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, mx, my, (dst + 4 ^ K * p : ℕ),
        (dst + 4 ^ K * p : ℕ), (n * n : ℕ), t, (t / n : ℕ), (t % n : ℕ)], μ'⟩ ∧
      Seg μ' dst (markList (4 ^ K * p)
        (fun t => (mx * spread (t / n) + my * spread (t % n)) * p + R.getD t 0) t) ∧
      SameOutside μ μ' dst (4 ^ K * p)) (n * n) 38 ?start ?round ?done ?bound
  case start =>
    aesop
  case bound =>
    simp_all
  case done =>
    grind
  case round =>
    rintro t _ ht - ⟨μ', rfl, hseg, hr⟩

    have hidx :=
      Nat.mul_add_lt_mul (hplace _ (Nat.div_lt_of_lt_mul' ht) _ (Nat.mod_lt_of_lt_mul ht))
      (pre.res.getD_lt ht)
    refine Ends.next 24 ((buildZMark_spec pre hplace ht _ _ hr).mono le_rfl ?_)
    rintro _ rfl
    refine Ends.nextPair ?_ (Nat.pos_of_ne_zero fun e => by simp [e] at ht) (by omega) (by omega) rfl rfl rfl
    exact ⟨rfl, _, by rw [update_frame_setLocal]; rfl,
      hseg.update_in (by simp_all [length_markList]) 1,
      hr.update ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hidx _⟩ _⟩

/-- **buildZ with (mx, my) = (2, 1)**: the matrix P of the proof of Theorem 17 (not the program
`P`). -/
theorem buildZ_P_spec (pre : BuildZPre lim μ dst r mort n K p R) :
    Ends lim P d buildZBody ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, 2, 1], μ⟩
      (buildZTime n (2 ^ K) p) fun σ' =>
      Seg σ'.mem dst (matPList n p K R) ∧ SameOutside μ σ'.mem dst (4 ^ K * p) := by
  have h := buildZ_spec (P := P) (d := d) (mx := 2) (my := 1) pre fun x hx y hy => by
    have := zIdx_lt (K := K) (lt_of_lt_of_le hx pre.n_le) (lt_of_lt_of_le hy pre.n_le)
    simpa [zIdx] using this
  rwa [markList_eq_matPList R fun t ht => pre.res.getD_lt ht] at h

/-- **buildZ with (mx, my) = (1, 2)**: the matrix Q of the proof of Theorem 17. -/
theorem buildZ_Q_spec (pre : BuildZPre lim μ dst r mort n K p R) :
    Ends lim P d buildZBody ⟨frame [dst, r, mort, n, (2 ^ K : ℕ), p, 1, 2], μ⟩
      (buildZTime n (2 ^ K) p) fun σ' =>
      Seg σ'.mem dst (matQList n p K R) ∧ SameOutside μ σ'.mem dst (4 ^ K * p) := by
  have h := buildZ_spec (P := P) (d := d) (mx := 1) (my := 2) pre fun x hx y hy => by
    have := zIdx_lt (K := K) (lt_of_lt_of_le hy pre.n_le) (lt_of_lt_of_le hx pre.n_le)
    simp only [zIdx] at this
    omega
  rwa [markList_eq_matQList R fun t ht => pre.res.getD_lt ht] at h

end

/-- **buildZ** as a procedure, for the matrix P. -/
theorem buildZ_P_meets {μ} {q dst r mort n K p} {R}
    (hP : P[q]? = some buildZBody) (pre : BuildZPre lim μ dst r mort n K p R) :
    Meets lim P q d [dst, r, mort, n, (2 ^ K : ℕ), p, 2, 1] μ (buildZTime n (2 ^ K) p) fun _ μ' =>
      Seg μ' dst (matPList n p K R) ∧ SameOutside μ μ' dst (4 ^ K * p) :=
  Meets.of_body hP (buildZ_P_spec pre)

/-- **buildZ** as a procedure, for the matrix Q. -/
theorem buildZ_Q_meets {μ} {q dst r mort n K p} {R}
    (hP : P[q]? = some buildZBody) (pre : BuildZPre lim μ dst r mort n K p R) :
    Meets lim P q d [dst, r, mort, n, (2 ^ K : ℕ), p, 1, 2] μ (buildZTime n (2 ^ K) p) fun _ μ' =>
      Seg μ' dst (matQList n p K R) ∧ SameOutside μ μ' dst (4 ^ K * p) :=
  Meets.of_body hP (buildZ_Q_spec pre)

/-! ## The matrices P and Q as lists -/

/-- The matrix P has 4^K vectors of p numbers. -/
theorem length_matPList n p K R : (matPList n p K R).length = 4 ^ K * p :=
  length_zList _ _ fun _ _ => length_unitOrZero _ _ _

/-- The matrix Q has 4^K vectors of p numbers. -/
theorem length_matQList n p K R : (matQList n p K R).length = 4 ^ K * p :=
  length_zList _ _ fun _ _ => length_unitOrZero _ _ _

/-- The entries of a unit vector and of the zero vector are 0 or 1. -/
theorem absLe_unitOrZero c [Decidable c] p k :
    AbsLe (if c then vunit p k else zeros p) 1 := by
  intro x hx
  split_ifs at hx
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    split_ifs <;> simp
  · simp_all

/-- The entries of a matrix of unit vectors and zero vectors are 0 or 1. -/
theorem absLe_zList_unit K M (hM : ∀ a c, AbsLe (M a c) 1) :
    AbsLe (zList K M) 1 := by
  intro x hx
  obtain ⟨z, -, hz⟩ := List.mem_flatMap.1 hx
  exact hM _ _ x hz

/-- The entries of P are 0 or 1. -/
theorem absLe_matPList n p K R : AbsLe (matPList n p K R) 1 :=
  absLe_zList_unit _ _ fun _ _ => absLe_unitOrZero _ _ _

/-- The entries of Q are 0 or 1. -/
theorem absLe_matQList n p K R : AbsLe (matQList n p K R) 1 :=
  absLe_zList_unit _ _ fun _ _ => absLe_unitOrZero _ _ _

end Light.Sec3
