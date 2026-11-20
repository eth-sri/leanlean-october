/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import Mathlib.Data.Finset.Sort
import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.FrontFacts

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! On a sorted copy of the input, a solution with a repeated value uses an adjacent pair.
For three equal values (necessarily zero), require the third index to be after that pair.
A two-pointer scan decides existence of such a witness in linear time. -/

private def RepeatAt (L : List ℤ) (i j : ℕ) : Prop :=
  i + 1 < L.length ∧ L.getD i 0 = L.getD (i + 1) 0 ∧
    2 * L.getD i 0 + L.getD j 0 = 0 ∧ (L.getD i 0 ≠ 0 ∨ i + 1 < j)

private def RepeatRect (L : List ℤ) (i j : ℕ) : Prop :=
  ∃ a ≥ i, ∃ b < j, RepeatAt L a b

private theorem sorted_getD {L : List ℤ} (h : L.Pairwise (· ≤ ·)) {i j : ℕ}
    (hij : i ≤ j) (hj : j < L.length) : L.getD i 0 ≤ L.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (hij.trans_lt hj), List.getD_eq_getElem _ _ hj]
  rcases hij.eq_or_lt with rfl | hlt
  · rfl
  · exact h.rel_getElem_of_lt _ _ hlt

private theorem RepeatRect.left {L : List ℤ} {i j : ℕ}
    (h : ∀ b < j, ¬ RepeatAt L i b) : RepeatRect L i j ↔ RepeatRect L (i + 1) j := by
  unfold RepeatRect
  grind

private theorem RepeatRect.right {L : List ℤ} {i j : ℕ}
    (h : ∀ a ≥ i, ¬ RepeatAt L a (j - 1)) : RepeatRect L i j ↔ RepeatRect L i (j - 1) := by
  unfold RepeatRect
  grind

private theorem repeatRect_iff {n : ℕ} {L : List ℤ} (hlen : L.length = n)
    (hs : L.Pairwise (· ≤ ·)) : RepeatRect L 0 n ↔ Degenerate (vecOf n L) := by
  let x := vecOf n L
  change RepeatRect L 0 n ↔ Degenerate x
  constructor
  · rintro ⟨i, _, j, hj, hi, he, hsum, hh⟩
    let a : Fin n := ⟨i, by omega⟩
    let b : Fin n := ⟨i + 1, by omega⟩
    let c : Fin n := ⟨j, hj⟩
    change 2 * x a + x c = 0 at hsum
    change x a = x b at he
    have hab : a ≠ b := by simp [Fin.ext_iff, a, b]
    by_cases h0 : x a = 0
    · have hlt := hh.resolve_left (fun h => h h0)
      have hneq : a ≠ c ∧ b ≠ c := by simp [Fin.ext_iff, a, b, c]; omega
      exact .inr (two_lt_card.mpr ⟨a, by simpa, b, by simpa [← he], c,
        by simp; omega, hab, hneq.1, hneq.2⟩)
    · exact .inl ⟨x a, h0, one_lt_card.mpr ⟨a, by simp, b, by simp [← he], hab⟩, c, by omega⟩
  · have select (y : ℤ) {m : ℕ} (h : m ≤ #{i | x i = y}) :
        ∃ e : Fin m ↪o Fin n, ∀ i, x (e i) = y :=
      ⟨_, fun i => (mem_filter.mp (orderEmbOfCardLe_mem _ h i)).2⟩
    have witness (i j k : Fin n) (hij : i < j) (he : x i = x j)
        (hsum : 2 * x i + x k = 0) (ht : x i ≠ 0 ∨ j < k) : RepeatRect L 0 n := by
      have hi : i.val + 1 ≤ j.val := hij
      have hb : i.val + 1 < L.length := by omega
      have hl := sorted_getD hs (show i.val ≤ i.val + 1 from Nat.le_succ _) hb
      have hr := sorted_getD hs hi (hlen ▸ j.isLt)
      change L.getD i 0 = L.getD j 0 at he
      exact ⟨i, Nat.zero_le _, k, k.isLt, hb, by omega, hsum, ht.imp_right (by omega)⟩
    rintro (⟨y, hy, hc, k, hk⟩ | h0)
    · obtain ⟨e, he⟩ := select y hc
      refine witness (e 0) (e 1) k (e.strictMono (by decide)) (by rw [he, he]) ?_
        (.inl (by simpa only [he]))
      rw [he, hk]
      ring
    · obtain ⟨e, he⟩ := select 0 h0
      exact witness (e 0) (e 1) (e 2) (e.strictMono (by decide)) (by rw [he, he])
        (by simp [he]) (.inr (e.strictMono (by decide)))

private theorem degenerate_perm {n : ℕ} {L X : List ℤ} (hp : L.Perm X) (hx : X.length = n) :
    Degenerate (vecOf n L) ↔ Degenerate (vecOf n X) := by
  have hl := hp.length_eq.trans hx
  have exists_val (Y : List ℤ) (hY : Y.length = n) (y : ℤ) :
      (∃ k, vecOf n Y k = y) ↔ y ∈ Y.toFinset := by
    rw [toFinset_eq_image hY]
    simp
  simp only [Degenerate, ← count_eq_card hl, hp.count_eq, count_eq_card hx,
    exists_val L hl, exists_val X hx, List.toFinset_eq_of_perm _ _ hp]

/-! ### The two-pointer loop -/

namespace Repeated

registers [Len, Src, Left, Right, Ans]

abbrev atOffset (i : Expr) : Expr := M (v Src +' i)
abbrev advance : Stmt := .set Left (v Left +' k 1)
abbrev accept : Stmt := .set Ans (k 1) ;; .set Left (v Len)
abbrev total : Expr := k 2 *' atOffset (v Left) +' atOffset (v Right -' k 1)
abbrev more : Cond := v Left +' k 1 <' v Len

def step : Stmt :=
  .ite (v Right =' k 0) (.set Left (v Len))
    (.ite (atOffset (v Left) =' atOffset (v Left +' k 1))
      (.ite (total <' k 0) advance
        (.ite (k 0 <' total) (.set Right (v Right -' k 1))
          (.ite (v Left +' k 2 <' v Right) accept
            (.ite (atOffset (v Left) =' k 0) advance accept)))) advance)

end Repeated

open Repeated

/-- Decide whether a solution uses a repeated value in an already sorted array. -/
def repeatedBody : Stmt :=
  .set Right (v Len) ;; .set Ans (k 0) ;; .while more step ;; .set Len (v Ans)

private abbrev scanLocals (L : List ℤ) (src i j : ℕ) (b : Bool) : List ℤ :=
  [L.length, src, i, j, if b then 1 else 0]

private def ScanInv (L : List ℤ) (src : ℕ) (μ : ℕ → ℤ) (fuel : ℕ) (σ : State) : Prop :=
  ∃ (i j : ℕ) (b : Bool), i ≤ L.length ∧ j ≤ L.length ∧ fuel = L.length - i + j ∧
    σ = ⟨frame (scanLocals L src i j b), μ⟩ ∧
    (b = true → i = L.length) ∧ ((b = true ∨ RepeatRect L i j) ↔ RepeatRect L 0 L.length)

/-- A loop with an invariant indexed by a decreasing amount of work. -/
private theorem whileFuel {lim : Limits} {P : Program} {d : ℕ} {c : Cond} {s : Stmt}
    {Q : State → Prop} (I : ℕ → State → Prop) (b : ℕ)
    (safe : ∀ k σ, I k σ → c.Safe lim σ) (stop : ∀ k σ, I k σ → ¬ c.Holds σ → Q σ)
    (next : ∀ k σ, I k σ → c.Holds σ → Ends lim P d s σ b (fun σ' => ∃ j < k, I j σ'))
    {n : ℕ} {σ : State} (h : I n σ) :
    Ends lim P d (.while c s) σ (n * (c.cost + 1 + b) + c.cost + 1) Q := by
  induction n using Nat.strong_induction_on generalizing σ with
  | h n ih =>
    have hs := safe n σ h
    by_cases hc : c.Holds σ
    · obtain ⟨σ', t, ht, hb, j, hj, hI⟩ := next n σ h hc
      obtain ⟨σ'', u, hu, hb', hQ⟩ := ih j hj hI
      refine ⟨σ'', _, .whileTrue hs hc ht hu, ?_, hQ⟩
      have hm := Nat.mul_le_mul_right (c.cost + 1 + b) (Nat.succ_le_of_lt hj)
      rw [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hm
      omega
    · exact ⟨σ, _, .whileFalse hs hc, by omega, stop n σ h hc⟩

/-- The linear scan decides the degenerate case and does not write to memory. -/
theorem repeated_meets {lim : Limits} {P : Program} {p d n V src : ℕ} {μ : ℕ → ℤ} {L X : List ℤ}
    (hp : P[p]? = some repeatedBody) (hlen : X.length = n) (hperm : L.Perm X)
    (hord : L.Pairwise (· ≤ ·)) (hb : AbsLe L V) (hseg : Seg μ src L)
    (hsp : src + n ≤ lim.space) (hsw : (lim.space : ℤ) ≤ lim.word)
    (hw : (n : ℤ) + 4 * V + 8 ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src] μ (tRepeated n) fun res μ' =>
      res = flag (Degenerate (vecOf n X)) ∧ μ' = μ := by
  have hL := hperm.length_eq.trans hlen
  have hmeaning := (repeatRect_iff hL hord).trans (degenerate_perm hperm hlen)
  subst n
  rw [← hL] at hmeaning hsp hw ⊢
  refine .of_body hp ?_
  unfold repeatedBody tRepeated
  light_steps
  light_piece (whileFuel (c := more) (s := step) (ScanInv L src μ) 80 ?_ ?_ ?_
    (n := 2 * L.length) (Q := fun σ => ∃ i j b,
      σ = ⟨frame (scanLocals L src i j b), μ⟩ ∧ (b = true ↔ RepeatRect L 0 L.length)) ?_)
    with _ ⟨i, j, b, rfl, hb'⟩
  · rintro f _ ⟨i, j, b, hi, hj, hf, rfl, hs, hr⟩
    light_side
  · rintro f _ ⟨i, j, b, hi, hj, hf, rfl, hs, hr⟩ hc'
    have hnot : ¬ RepeatRect L i j := by
      simp at hc'
      rintro ⟨a, ha, q, hq, hlt, _⟩
      omega
    exact ⟨i, j, b, rfl, by simpa [hnot] using hr⟩
  · rintro _ _ ⟨i, j, b, hi, hj, rfl, rfl, hstop, hscan⟩ hc
    have hi' : i + 1 < L.length := by simp at hc; omega
    obtain rfl : b = false := by cases b <;> simp_all <;> omega
    simp only [Bool.false_eq_true, false_or] at hscan
    let Q σ' := ∃ f' < L.length - i + j, ScanInv L src μ f' σ'
    change Ends lim P d step _ 80 Q
    have continueAt {u v : ℕ} (hu : u ≤ L.length) (hv : v ≤ L.length)
        (fuel : L.length - u + v < L.length - i + j) (ok : RepeatRect L u v ↔ RepeatRect L 0 L.length) :
        Q ⟨frame (scanLocals L src u v false), μ⟩ :=
      ⟨_, fuel, u, v, false, hu, hv, rfl, rfl, by simp, by simpa⟩
    have advance_ok (no : ∀ q < j, ¬ RepeatAt L i q) {T : ℕ} (hT : 4 ≤ T := by light_time) :
        Ends lim P d (advance ;; .skip) ⟨frame (scanLocals L src i j false), μ⟩ T Q := by
      light_set (i + 1 : ℕ)
      exact continueAt (by omega) hj (by omega) ((RepeatRect.left no).symm.trans hscan)
    have accept_ok (h : RepeatAt L i (j - 1)) (hj' : 0 < j) {T : ℕ} (hT : 4 ≤ T) :
        Ends lim P d (accept ;; .skip) ⟨frame (scanLocals L src i j false), μ⟩ T Q := by
      have hf := hscan.1 ⟨i, le_rfl, j - 1, by omega, h⟩
      unfold accept
      light_steps
      exact ⟨_, by omega, L.length, j, true, le_rfl, hj, rfl, rfl, by simp, by simp [hf]⟩
    unfold step
    light_if h0 h0' : j = 0
    · light_set L.length
      have hn : ¬ RepeatRect L 0 L.length := by simpa [RepeatRect, h0] using hscan.symm
      exact continueAt le_rfl hj (by omega) (by simpa [RepeatRect, h0] using hn)
    have read (q : ℕ) (hq : q < L.length) : μ (src + q) = L.getD q 0 ∧
        -(V : ℤ) ≤ (L[q]?.getD 0) ∧ (L[q]?.getD 0) ≤ V := by
      exact ⟨hseg.getD hq 0, by simpa [hq] using abs_le.mp (hb _ (List.getElem_mem hq))⟩
    obtain ⟨hA, _, _⟩ := read i (by omega)
    obtain ⟨hB, _, _⟩ := read (i + 1) hi'
    obtain ⟨hC, _, _⟩ := read (j - 1) (by omega)
    have hB' : ((src : ℤ) + ((i : ℤ) + 1)).toNat = src + (i + 1) := by omega
    have hC' : ((src : ℤ) + ((j : ℤ) - 1)).toNat = src + (j - 1 : ℕ) := by omega
    light_if he hne : L.getD i 0 = L.getD (i + 1) 0 using hA, hB, hB'
    · light_if ht hn : 2 * L.getD i 0 + L.getD (j - 1) 0 < 0 using hA, hC, hC'
      · apply advance_ok (fun q hq hit => ?_) 
        have := sorted_getD hord (show q ≤ j - 1 by omega) (show j - 1 < L.length by omega)
        exact (by unfold RepeatAt at hit; omega)
      · light_if ht' hn' : 0 < 2 * L.getD i 0 + L.getD (j - 1) 0 using hA, hC, hC'
        · have hkeep : RepeatRect L i (j - 1) ↔ RepeatRect L 0 L.length := by
            refine (RepeatRect.right (fun q hq hit => ?_)).symm.trans hscan
            have hq' : q < L.length := by unfold RepeatAt at hit; omega
            have := sorted_getD hord hq hq'
            unfold RepeatAt at hit
            omega
          light_set (j - 1 : ℕ)
          exact continueAt hi (by omega) (by omega) hkeep
        · have hsum : 2 * L.getD i 0 + L.getD (j - 1) 0 = 0 := by omega
          light_if hafter hbefore : i + 2 < j
          · exact accept_ok ⟨hi', he, hsum, Or.inr (by omega)⟩ (by omega) (by light_time)
          · light_if hz hnz : L.getD i 0 = 0 using hA
            · exact advance_ok (fun q hq hit => by unfold RepeatAt at hit; omega)
            · exact accept_ok ⟨hi', he, hsum, Or.inl hnz⟩ (by omega) (by light_time)
    · exact advance_ok (fun q _ hit => hne hit.2.1)
  · exact ⟨0, L.length, false, Nat.zero_le _, le_rfl, by omega, rfl, by simp, by simp⟩
  · light_step
    exact ⟨by cases b <;> simp_all [flag_of, flag_of_not], rfl⟩

end Light.Sec3.ChanHe
