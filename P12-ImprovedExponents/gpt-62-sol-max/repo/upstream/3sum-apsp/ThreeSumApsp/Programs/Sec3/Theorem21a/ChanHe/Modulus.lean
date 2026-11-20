/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic
import Mathlib.Tactic.FinCases

public import ThreeSumApsp.Lang.Sequence

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory

/-!
# The reduction from 3SUM to Convolution-3SUM: the modulus of a node

For Theorem 21(a).  The modulus of a node of the recursion tree of
[CH20, Theorem 5.1] is the product of two primes up to m: p₁ is the least prime q such that the
three sets have few colliding pairs modulo q (`firstP`), and p₂ the least prime q such that few of
these pairs still collide modulo p₁ q (`secondP`).

* search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr) runs through the primes q in
  ascending order and returns the first one for which each of the three sets has at most bᵢ / np
  colliding pairs modulo mult · q (`Good`), and 1 if there is none (`search_spec`).  It always runs
  through all candidates.  A round makes three tests and records the candidate; that the first good element of the sorted list is
  the least good element of the set is `pick_filter`.
* modulus calls search twice, as in the definitions of the two primes, with three calls of coll in
  between, and returns the product; if there is no prime at all it returns 1 (`modulus_spec`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program}

namespace FirstGood

/-! ## The least good element of a set is the first good element of its sorted list -/

/-- First good element, or 1 if there is none (all prime candidates exceed 1). -/
def hit (good : ℕ → Prop) [DecidablePred good] (l : List ℕ) : ℕ :=
  (l.find? fun q => decide (good q)).getD 1

variable {good : ℕ → Prop} [DecidablePred good]

/-- Accumulating the first good element across one more candidate. -/
theorem hit_take_succ {l : List ℕ} (hl : ∀ x ∈ l, x ≠ 1) {t : ℕ} (ht : t < l.length) :
    hit good (l.take (t + 1)) = if hit good (l.take t) = 1 then (if good l[t] then l[t] else 1)
      else hit good (l.take t) := by
  rw [List.take_succ_eq_append_getElem ht, hit, List.find?_append]
  unfold hit
  cases h : (l.take t).find? (fun q => decide (good q)) <;>
    grind [List.mem_of_mem_take]

/-- Filtering a sorted list preserves the order, so its head minimizes the filtered set. -/
theorem pick_filter (Q : Finset ℕ) : pick {q ∈ Q | good q} = hit good (Q.sort (· ≤ ·)) := by
  let l := (Q.sort (· ≤ ·)).filter (fun q => decide (good q))
  have hset : l.toFinset = {q ∈ Q | good q} := by ext; simp [l]
  have hs : (filter good Q).sort (· ≤ ·) = l := by
    rw [← hset]
    exact (List.toFinset_sort (· ≤ ·) ((Q.sort_nodup _).filter _)).2
      ((Q.pairwise_sort _).filter _)
  rw [hit, ← List.head?_filter]
  change _ = l.head?.getD 1
  rw [← hs]
  unfold pick
  split_ifs with h
  · rw [min'_eq_sorted_zero (h := h), List.head?_eq_getElem?, List.getElem?_eq_getElem]
    rfl
  · simp [not_nonempty_iff_eq_empty.mp h]

/-- The least element of a set of primes up to m, or 1, lies between 1 and m. -/
theorem pick_bounds {m : ℕ} (hm : 1 ≤ m) {T : Finset ℕ} (hT : T ⊆ Nat.primesLE m) :
    1 ≤ pick T ∧ pick T ≤ m := by
  unfold pick
  split_ifs with h
  · have := Nat.mem_primesLE.1 (hT (Finset.min'_mem T h))
    exact ⟨this.2.one_le, this.1⟩
  trivial

end FirstGood

open FirstGood

/-! ## One test of a candidate -/

namespace Search

/-- The local variables of search: the arguments mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr,
cnt, fr; the number of the candidate; the first good candidate found so far (1 if none); the modulus
mult · q; and a number of colliding pairs. Found is 1 until a candidate passes every test.
Local 0 also takes the result. -/
registers [Mult / Result]
registers from 10 [NumPrimes, Primes, Count, Free, Idx, Found, Modulus, Pairs]

end Search

open Search in
/-- Test one slot: compute its collision count and discard the candidate if the count is too large. -/
def checkStmt (pColl : ℕ) (i : Fin 3) : Stmt :=
  .call pColl [v (2 * i.val + 2), v (2 * i.val + 1), v Modulus, v Count, v Free] Pairs ;;
  .ite (v (7 + i.val) <' v Pairs *' v NumPrimes) (.set Found (k 1)) .skip

def searchChecks (pColl : ℕ) : Stmt := Stmt.chain (checkStmt pColl) [0, 1, 2]

open Search in
/-- Test the next candidate only if no earlier one passed. Each failed test resets Found to 1. -/
def searchRound (pColl : ℕ) : Stmt :=
  .ite (v Found =' k 1)
    (.set Found (M (v Primes +' v Idx)) ;;
     .set Modulus (v Mult *' v Found) ;;
     searchChecks pColl) .skip

open Search in
def searchBody (pColl : ℕ) : Stmt :=
  .set Found (k 1) ;; .for Idx (v NumPrimes) (searchRound pColl) ;; .set Result (v Found)

section search

variable {d pColl : ℕ} {x : SearchArgs} {μ : ℕ → ℤ}

/-- There are at most m² + 1 primes up to m.  (This is the shape y ≤ M + 1 that `mul_le_word` asks
for, with M = m².) -/
theorem Env.Ok.np_le {e : Env} (h : e.Ok μ) : e.np ≤ e.m * e.m + 1 := by
  have hcard := h.primes.1 ▸ Nat.card_primesLE_le e.m
  nlinarith

/-- What is allowed for search covers what coll needs one level of calls further down. -/
theorem collNeed_ok_of_search {fr n V m l Mo : ℕ} (hok : (searchNeed n V m).Ok lim fr d)
    (hl : l ≤ n) (hMo : Mo ≤ m * m) : (collNeed l V Mo).Ok lim fr (d + 1) :=
  hok.mono (wordNeed_mono hl hMo) (by simp only [collNeed, searchNeed]; omega)
    (by rfl)

/-- The time of the three tests of a candidate. -/
def tChecks (x : SearchArgs) : ℕ :=
  45 + (tColl (x.slot 0).len x.V + tColl (x.slot 1).len x.V + tColl (x.slot 2).len x.V)

/-- The candidates of search: the primes up to m, in ascending order. -/
abbrev SearchArgs.candidates (x : SearchArgs) : List ℕ := (Nat.primesLE x.m).sort (· ≤ ·)

/-- **search** returns the first prime passing the three collision tests. -/
theorem search_spec {p : ℕ} (hP : P[p]? = some (searchBody pColl)) (hColl : CollSpec lim P pColl) :
    SearchSpec lim P p := by
  intro x μ hN hmult_pos hmult_le d hok
  refine .of_body hP ?_
  let ps := x.candidates
  have hlen : ps.length = x.np := by simp [ps, ← hN.envOk.primes.1]
  have hprime : ∀ q ∈ ps, q.Prime ∧ q ≤ x.m := fun q hq => by
    rw [Finset.mem_sort, Nat.mem_primesLE] at hq
    exact ⟨hq.2, hq.1⟩
  have hone : ((1 : ℕ) : ℤ) ≤ lim.word := le_word_of_le hok.word (by omega)
  have hnp : (x.np : ℤ) ≤ lim.word := le_word_of_le hok.word hN.envOk.np_le
  let S (t : ℕ) (z : ℤ × ℤ × ℤ) (ν : ℕ → ℤ) : State :=
    ⟨frame (x.vals ++ [(t : ℤ), z.1, z.2.1, z.2.2]), ν⟩
  let I (t : ℕ) (z : ℤ × ℤ × ℤ) (ν : ℕ → ℤ) := Kept μ ν x.fr ∧ z.1 = (hit x.Good (ps.take t) : ℕ)
  refine Ends.setToThen 1 ?_ (hT := by simp [tSearch])
  refine Ends.next _ (Ends.forShape S I x.np (tChecks x + 22) (1, 0, 0) ⟨.refl, rfl⟩ ?_ ?_
    (first := by rw [update_frame_setLocal, ← frame_append_zeros _ 2]; rfl)
    (bound := by intros; light_side [S]) (counter := by intros; rfl)
    (next := by intros; simp only [S, update_frame_setLocal]; rfl)
    (hT := le_rfl)) (by simp [tSearch, tChecks]; ring_nf; omega)
  · rintro t ⟨f, y, z⟩ μ' ht ⟨kept, hf⟩
    change f = (hit x.Good (ps.take t) : ℕ) at hf
    subst f
    have hN' := hN.kept kept
    have htl : t < ps.length := by omega
    let q := ps[t]
    obtain ⟨hqp, hqm⟩ := hprime q (List.getElem_mem htl)
    have hread : μ' (x.pr + t) = (q : ℕ) := SegN.getElem hN'.envOk.primes.2 htl
    have hsucc := hit_take_succ (good := x.Good) (fun q hq => (hprime q hq).1.ne_one) htl
    have hMo : x.mult * q ≤ x.m * x.m := Nat.mul_le_mul hmult_le hqm
    have hM1 : 1 ≤ x.mult * q := Nat.mul_pos hmult_pos hqp.one_le
    have hMw : (x.mult : ℤ) * q ≤ lim.word := by
      exact_mod_cast le_word_of_le (y := x.mult * q) hok.word (by omega)
    have hw := hok.space
    have hcells := hok.cells
    have hpr := hN.envOk.belowPr
    unfold searchRound
    refine Ends.iteIffLast (hit x.Good (ps.take t) = 1) (fun hf => ?_) (fun hf => ?_) (by light_side [S])
    · light_set q using S, hread
      light_set (x.mult * q : ℕ) using S
      let C (i : Fin 3) := coll (x.slot i).set (x.mult * q)
      let step (z : ℤ × ℤ) (i : Fin 3) : ℤ × ℤ :=
        (C i, if C i * x.np ≤ x.bound i then z.2 else 1)
      let R (z : ℤ × ℤ) (σ : State) := Kept μ' σ.mem x.fr ∧
        σ.loc = (S t (z.2, (x.mult * q : ℕ), z.1) σ.mem).loc
      refine (Ends.chain [0, 1, 2] (checkStmt pColl) (fun i => 15 + tColl (x.slot i).len x.V)
        step R ?_ (a := (z, q)) ⟨.refl, rfl⟩).mono (by simp [tChecks]; omega) ?_
      · rintro i - u ⟨_, ν⟩ ⟨hk, hloc⟩
        dsimp only [S] at hloc
        subst hloc
        have hN'' := hN'.kept hk
        have hi := hN''.slotOk i
        have hc : C i ≤ (x.slot i).len ^ 2 := hi.set.card ▸ coll_le_sq _ _
        have hl := hi.le
        have hp : (C i : ℤ) * x.np ≤ lim.word := by
          simpa using mul_le_word (z := 1) hok.word (hc.trans (Nat.pow_le_pow_left (by omega) 2))
            hN.envOk.np_le (by omega)
        have hp0 : (0 : ℤ) ≤ (C i : ℤ) * x.np := by positivity
        have hneed := collNeed_ok_of_search hok hl hMo
        have hd := hneed.depth
        unfold checkStmt
        refine Ends.callToThen (hColl (d + 1) _ _ _ _ _ _ _ _ ν (hi.bucket hN''.envOk hM1 hMo) hneed) ?_
          (by fin_cases i <;> simp) (by omega)
        rintro _ ν' ⟨rfl, hk'⟩
        refine Ends.iteIffLast (¬ C i * x.np ≤ x.bound i) (fun h => ?_) (fun h => ?_)
          (by fin_cases i <;> simp [C] at hp hp0 ⊢ <;> omega)
        · exact Ends.setLast ⟨hk.trans hk', by simp only [step, if_neg h, S, update_frame_setLocal]; rfl⟩
        · exact Ends.skip ⟨hk.trans hk', by simp only [step, if_pos (not_not.mp h), S]; rfl⟩
      · rintro ⟨loc, ν⟩ ⟨hk, hloc⟩
        let u := ([0, 1, 2] : List (Fin 3)).foldl step (z, q)
        refine ⟨(u.2, (x.mult * q : ℕ), u.1), ν, by cases hloc; rfl, kept.trans hk, ?_⟩
        change u.2 = (hit x.Good (ps.take (t + 1)) : ℕ)
        simp only [hsucc, hf, if_pos, Nat.cast_ite, Nat.cast_one, u, List.foldl_cons, List.foldl_nil, step]
        rw [← ite_and, ← ite_and]
        apply if_congr _ rfl rfl
        simp only [SearchArgs.Good, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, C, q]
        tauto
    · exact Ends.skip ⟨(↑(hit x.Good (ps.take t)), y, z), μ', rfl, kept, by simp [hsucc, hf]⟩
  · rintro ⟨f, y, z⟩ ν ⟨kept, hf⟩
    change f = (hit x.Good (ps.take x.np) : ℕ) at hf
    rw [← hlen, List.take_length] at hf
    exact Ends.setTo f ⟨by simpa [pick_filter, ps] using hf, kept⟩
      (hT := by simp [tSearch, tChecks]; ring_nf; omega)

end search

/-! ## The modulus -/

namespace Modulus

/-- The local variables of modulus: the arguments s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr; the
two primes; and the numbers of colliding pairs of the three sets modulo the first prime.  Local 0
also takes the result. -/
registers [Set1 / Result, Len1, Set2, Len2, Set3, Len3, Digits, NumPrimes, Primes, Count, Free,
  Prime1, Prime2, Pairs1, Pairs2, Pairs3]

end Modulus

open Modulus in
/-- Compute the collision count of one slot modulo the first prime. -/
def modulusColl (pColl : ℕ) (i : Fin 3) : Stmt :=
  .call pColl [v (2 * i.val + 1), v (2 * i.val), v Prime1, v Count, v Free] (Pairs1 + i.val)

def modulusColls (pColl : ℕ) : Stmt := Stmt.chain (modulusColl pColl) (List.finRange 3)

open Modulus in
/-- The two searches of modulus, with the three calls of coll between them, and the product. -/
def modulusMain (pSearch pColl : ℕ) : Stmt :=
  .call pSearch
    [k 1, v Set1, v Len1, v Set2, v Len2, v Set3, v Len3,
      k 3 *' v Digits *' v Len1 *' v Len1,
      k 3 *' v Digits *' v Len2 *' v Len2,
      k 3 *' v Digits *' v Len3 *' v Len3,
      v NumPrimes, v Primes, v Count, v Free] Prime1 ;;
  modulusColls pColl ;;
  .call pSearch
    [v Prime1, v Set1, v Len1, v Set2, v Len2, v Set3, v Len3,
      k 3 *' v Digits *' v Pairs1,
      k 3 *' v Digits *' v Pairs2,
      k 3 *' v Digits *' v Pairs3,
      v NumPrimes, v Primes, v Count, v Free] Prime2 ;;
  .set Result (v Prime1 *' v Prime2)

open Modulus in
/-- modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns 1 if there is no prime, and the
product of the two primes otherwise. -/
def modulusBody (pSearch pColl : ℕ) : Stmt :=
  .ite (v NumPrimes =' k 0) (.set Result (k 1)) (modulusMain pSearch pColl)

section modulus

variable {d Λ pSearch pColl : ℕ} {a : NodeArgs} {μ : ℕ → ℤ}

/-- The arguments of the first search: the moduli are the primes, and the bounds are 3 Λ lᵢ². -/
@[simp] def NodeArgs.firstSearch (a : NodeArgs) (Λ : ℕ) : SearchArgs :=
  ⟨a, 1, fun i => 3 * Λ * (a.slot i).len * (a.slot i).len⟩

/-- The arguments of the second search, from the collision counts modulo `p₁`. -/
@[simp] def NodeArgs.secondSearch (a : NodeArgs) (Λ p₁ : ℕ) : SearchArgs :=
  ⟨a, p₁, fun i => 3 * Λ * coll (a.slot i).set p₁⟩

section words

variable {n V m : ℕ}

/-- The bounds that are handed to search fit in a word: 3 Λ x for x up to (n + 1)². -/
theorem three_lam_mul_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {x : ℕ} (hx : x ≤ (n + 1) ^ 2) : 0 ≤ 3 * (Λ : ℤ) * x ∧ 3 * (Λ : ℤ) * x ≤ lim.word := by
  have h := mul_le_word (y := 1) (z := 3 * Λ) hword hx (by omega) (by omega)
  push_cast at h
  exact ⟨by positivity, by linarith⟩

/-- The same for a length and its square. -/
theorem three_lam_sq_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {l : ℕ} (hl : l ≤ n) : (0 ≤ 3 * (Λ : ℤ) * l ∧ 3 * (Λ : ℤ) * l ≤ lim.word) ∧
      0 ≤ 3 * (Λ : ℤ) * l * l ∧ 3 * (Λ : ℤ) * l * l ≤ lim.word := by
  have hsq : l * l ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h := three_lam_mul_le hword hΛ hsq
  push_cast at h
  rw [← mul_assoc] at h
  exact ⟨three_lam_mul_le hword hΛ ((Nat.le_mul_self l).trans hsq), h⟩

/-- The same for a number of colliding pairs. -/
theorem three_lam_coll_le (hword : ((wordNeed n V (m * m) : ℕ) : ℤ) ≤ lim.word) (hΛ : Λ ≤ V + 2)
    {s l M : ℕ} {S : Finset ℤ} (hS : SetAt μ s l S) (hl : l ≤ n) :
    0 ≤ 3 * (Λ : ℤ) * coll S M ∧ 3 * (Λ : ℤ) * coll S M ≤ lim.word :=
  three_lam_mul_le hword hΛ ((coll_le_sq S M).trans (hS.card ▸ Nat.pow_le_pow_left (by omega) 2))

end words

/-- coll, called for a set of a node. -/
theorem Slot.Ok.coll_meets {e : Env} {X : Slot} {M : ℕ} (h : X.Ok μ e) (he : e.Ok μ)
    (hColl : CollSpec lim P pColl) (hM : 1 ≤ M) (hMm : M ≤ e.m * e.m)
    (hok : (collNeed X.len e.V M).Ok lim e.fr d) :
    Meets lim P pColl d [X.len, X.addr, M, e.cnt, e.fr] μ (tColl X.len e.V) fun r μ' =>
      r = (coll X.set M : ℤ) ∧ Kept μ μ' e.fr :=
  hColl d _ _ _ _ _ _ _ _ μ (h.bucket he hM hMm) hok

/-- **The three calls of coll** between the two searches leave the numbers of colliding pairs modulo
p₁ in Pairs1, Pairs2, Pairs3 and change no cell below the free pointer. -/
theorem modulusColls_ends (hColl : CollSpec lim P pColl) (hN : NodeMem μ a)
    (hok : (modulusNeed a.n a.V a.m).Ok lim a.fr d) {p₁ : ℕ} (hp₁_pos : 1 ≤ p₁)
    (hp₁_le_sq : p₁ ≤ a.m * a.m) :
    Ends lim P d (modulusColls pColl) ⟨frame (a.modulusVals Λ ++ [(p₁ : ℤ)]), μ⟩
      (21 + (tColl (a.slot 0).len a.V + tColl (a.slot 1).len a.V + tColl (a.slot 2).len a.V)) fun σ' =>
      ∃ μ', Kept μ μ' a.fr ∧ σ' = ⟨frame (a.modulusVals Λ ++
        [(p₁ : ℤ), 0, coll (a.slot 0).set p₁, coll (a.slot 1).set p₁, coll (a.slot 2).set p₁]), μ'⟩ := by
  have hdepth := hok.depth
  simp only [modulusNeed] at hdepth
  have hokC : ∀ {l : ℕ}, l ≤ a.n → (collNeed l a.V p₁).Ok lim a.fr (d + 1) := fun hl =>
    hok.mono (wordNeed_mono hl hp₁_le_sq) (by simp only [collNeed, modulusNeed]; omega)
      (by simp only [collNeed, modulusNeed]; omega)
  let frameAt (k : ℕ) := a.modulusVals Λ ++ [(p₁ : ℤ), 0] ++ List.ofFn fun i : Fin 3 =>
    if i.val < k then (coll (a.slot i).set p₁ : ℤ) else 0
  let R (k : ℕ) (σ : State) := Kept μ σ.mem a.fr ∧ σ.loc = frame (frameAt k)
  have hstart : frame (frameAt 0) = frame (a.modulusVals Λ ++ [(p₁ : ℤ)]) :=
    by simpa [frameAt, List.ofFn_succ, List.append_assoc] using frame_append_zeros (a.modulusVals Λ ++ [(p₁ : ℤ)]) 4
  rw [← hstart]
  refine (Ends.chainFin (modulusColl pColl) (fun i => 7 + tColl (a.slot i).len a.V) R
    ?_ ⟨.refl, rfl⟩).mono (by simp [List.finRange_succ]; omega) ?_
  · rintro i ⟨_, μ'⟩ ⟨hk, rfl⟩
    have hm := hN.kept hk
    have hi := hm.slotOk i
    have hneed := hokC hi.le
    have hd := hneed.depth
    unfold modulusColl
    refine Ends.callTo (hi.coll_meets hm.envOk hColl hp₁_pos hp₁_le_sq hneed) ?_
      (by fin_cases i <;> simp [frameAt, List.ofFn_succ]) (by omega) (by light_time)
    rintro _ μ'' ⟨rfl, hk'⟩
    refine ⟨hk.trans hk', ?_⟩
    fin_cases i <;> rfl
  · rintro ⟨_, μ'⟩ ⟨hk, rfl⟩
    exact ⟨μ', hk, rfl⟩

/-- The modulus, in a program that holds modulus and search, from the specification of coll. -/
theorem modulusSpec_of {p : ℕ} (hP : P[p]? = some (modulusBody pSearch pColl))
    (hPs : P[pSearch]? = some (searchBody pColl)) (hColl : CollSpec lim P pColl) :
    ModulusSpec lim P p := by
  have hSearch := search_spec hPs hColl
  intro a Λ μ hN hΛ d hok
  refine .of_body hP ?_
  have hone : ((1 : ℕ) : ℤ) ≤ lim.word := le_word_of_le hok.word (by omega)
  have hcard := hN.envOk.primes.1
  -- if np = 0
  refine Ends.iteLast (fun hnone => ?_) (fun hsome => ?_) (hT := by simp [tModulus])
  · -- return 1
    have hempty : Nat.primesLE a.m = ∅ := Finset.card_eq_zero.1 (by
      have hnp : a.np = 0 := by simpa using hnone
      omega)
    exact Ends.setTo 1 ⟨by simp [modulus, firstP, secondP, pick, hempty], .refl⟩
      (hT := by simp [tModulus])
  · have hm : 1 ≤ a.m := by
      have hpos : 0 < #(Nat.primesLE a.m) := by
        have hnp : ¬ a.np = 0 := by simpa using hsome
        omega
      obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
      exact (Nat.prime_of_mem_primesLE hq).one_le.trans (Nat.le_of_mem_primesLE hq)
    have hdepth : d + 4 ≤ lim.depth := hok.depth
    have hokS : (searchNeed a.n a.V a.m).Ok lim a.fr (d + 1) :=
      hok.mono le_rfl le_rfl (by simp only [searchNeed, modulusNeed]; omega)
    let Q := Nat.primesLE a.m
    let p₁ := firstP Q Λ (a.slot 0).set (a.slot 1).set (a.slot 2).set
    let p₂ := secondP Q Λ (a.slot 0).set (a.slot 1).set (a.slot 2).set p₁
    obtain ⟨hp₁_pos, hp₁_le⟩ : 1 ≤ p₁ ∧ p₁ ≤ a.m := pick_bounds hm (Finset.filter_subset _ _)
    have hp₂_le : p₂ ≤ a.m := (pick_bounds hm (Finset.filter_subset _ _)).2
    have hc (i : Fin 3) := (hN.slotOk i).set.card
    have hfirst : pick {q ∈ (a.firstSearch Λ).m.primesLE | (a.firstSearch Λ).Good q} = p₁ := by
      simp [p₁, Q, firstP, SearchArgs.Good, Fin.forall_fin_succ, ← hcard, hc, sq, mul_assoc]
    have hsecond : pick {q ∈ (a.secondSearch Λ p₁).m.primesLE | (a.secondSearch Λ p₁).Good q} = p₂ := by
      simp [p₂, Q, secondP, SearchArgs.Good, Fin.forall_fin_succ, ← hcard]
    -- The words that are formed: 3, 3 Λ, 3 Λ lᵢ, 3 Λ lᵢ², 3 Λ cᵢ and p₁ p₂.
    have hthree := three_lam_mul_le (Λ := 1) hok.word (by omega) (x := 1)
      (Nat.one_le_pow _ _ (by omega))
    have hlam := three_lam_mul_le hok.word hΛ (x := 1) (Nat.one_le_pow _ _ (by omega))
    have hlen (i : Fin 3) := three_lam_sq_le hok.word hΛ (hN.slotOk i).le
    have hcoll (i : Fin 3) := three_lam_coll_le (M := p₁) hok.word hΛ (hN.slotOk i).set (hN.slotOk i).le
    have := hlen 0; have := hlen 1; have := hlen 2
    have := hcoll 0; have := hcoll 1; have := hcoll 2
    have hprod : 0 ≤ (p₁ : ℤ) * p₂ ∧ (p₁ : ℤ) * p₂ ≤ lim.word := ⟨by positivity, by
      exact_mod_cast le_word_of_le (y := p₁ * p₂) hok.word
        ((Nat.mul_le_mul hp₁_le hp₂_le).trans (by omega))⟩
    simp only [tModulus]
    -- p₁ := search(1, s₁, l₁, s₂, l₂, s₃, l₃, 3 Λ l₁², 3 Λ l₂², 3 Λ l₃², np, pr, cnt, fr)
    light_call (hSearch (a.firstSearch Λ) μ hN le_rfl hm _ hokS) with _ μ₁ ⟨rfl, kept₁⟩
    rw [hfirst]
    -- the numbers cᵢ of colliding pairs modulo p₁
    light_piece (modulusColls_ends hColl (hN.kept kept₁) hok hp₁_pos
      (hp₁_le.trans (Nat.le_mul_self a.m))) with _ ⟨μ₂, kept₂, rfl⟩
    -- p₂ := search(p₁, s₁, l₁, s₂, l₂, s₃, l₃, 3 Λ c₁, 3 Λ c₂, 3 Λ c₃, np, pr, cnt, fr)
    light_call (hSearch (a.secondSearch Λ p₁) μ₂ (hN.kept (kept₁.trans kept₂))
      hp₁_pos hp₁_le _ hokS) with _ μ₃ ⟨rfl, kept₃⟩
    rw [hsecond]
    -- return p₁ * p₂
    light_step
    refine ⟨?_, kept₁.trans (kept₂.trans kept₃)⟩
    simp [modulus, p₁, p₂, Q]

end modulus

end Light.Sec3.ChanHe
