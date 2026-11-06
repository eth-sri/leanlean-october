/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Round

/-!
# 3SUM from Convolution-3SUM: the core of the host

Theorem 21(a), after [CH20, Theorem 5.1].  core(n, V, x, b), with V = 2U,
decides 3SUM for the n numbers of absolute value at most U at x.  It has six parts.

* coreSetup computes the parameters and fills the arrays of the memory map (`coreSetup_ends`).
* coreAddr computes the addresses of the arrays that the rest uses (`coreAddr_runs`).
* coreSplit runs through the splittings (`coreSplit_ends`).
* coreDoubles and coreZero form and decide the two three-set inputs for the solutions that repeat a
  value (`coreDoubles_ends`, `coreZero_ends`).
* coreAnswer adds up the three answers (`coreAnswer_runs`).

That the three answers decide 3SUM is `threeSum_iff_trees`.  The routines that the three middle
parts call write only to the cells for the three sets of a splitting, to the cells for the doubles,
and behind the arrays; so the arrays that they read are still there at each call (`Core.Arrays`,
`Core.Arrays.of_sameOn`), and each three-set input lies in the memory as the recursive procedure
wants it (`Core.Placed`, `Core.Arrays.nodesPre`).
-/


open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {U : ℕ}

/-! ## The three answers, and the time -/

/-- 3SUM, through the three kinds of three-set inputs. -/
theorem threeSum_iff_trees {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ThreeSum x ↔
      (∃ β < Lam (2 * U), ∃ β' < Lam (2 * U), ∃ v,
        SplitYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (univ.image x) β β' v) ∨
      TreeYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (twiceSet x) {0} (univ.image x) ∨
      TreeYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (zeroSet x) {0} {0} := by
  rw [instances_correct n U hn x hx]
  unfold instances allNodes SplitYes TreeYes reduction
  simp only [List.mem_map, List.mem_append, List.mem_flatMap]
  grind

/-- A sum of three answers is positive if and only if one of them is yes. -/
theorem ChCore.flag_sum_pos (a b c : Prop) : 0 < flag a + flag b + flag c ↔ a ∨ b ∨ c := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;>
    simp [flag_of, flag_of_not, ha, hb, hc]

/-- The steps of the routine are within the time of the host. -/
theorem ChCore.time_le (T : ℕ → ℕ → ℕ) (n V : ℕ) :
    tParams n V + tPrep n (Lam V) (mPar n V)
        + tGrid T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) (Lam V) + tTwice n
        + tTree T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) + tZeroThree n
        + tTree T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) + 126 ≤ coreTime T n V := by
  set m := mPar n V
  set np := #(Nat.primesLE m)
  set Λ := Lam V
  set tt := tTree T n V m np _ with htt
  have htree : tt = callsB n * nodeOwn n V m np + callsB n * T (8 * m ^ 2) (60 * V + 40) := by
    grind [tTree, tNodes_eq, callsB]
  have hgrid : tGrid T n V m np (fuel n) Λ
      = Λ ^ 2 * (6 * tPick n + 2 * tt + 320) + 80 * Λ + 40 := by
    grind [tGrid, tRow, tRound]
  have hcore : coreTime T n V = tParams n V + tPrep n Λ m
      + Λ ^ 2 * (6 * tPick n + 2 * tt + 320) + 280 * Λ ^ 2 + 2 * tt + 6 * tPick n + 600
      + tTwice n + tZeroThree n + 400 := by
    grind [coreTime, coreOwn, coreCalls, inputsB, tSetup]
  have hsq : Λ ≤ Λ ^ 2 := by nlinarith
  omega

/-! ## The program -/

namespace Core

/- The locals of core; each is assigned once.  The arguments: n, V, x and the free pointer b.  Then
a local for a result that is not read; the parameters Λ, m and f, which params has written to the
three cells from b; the base b + 3 of the arrays; the number of distinct values; the addresses of
the sorted copy, the values, their multiplicities, the table of digits, the three sets, the doubles
and the cell that holds 0, and the free pointer behind the arrays.  Then the answer for the
splittings, the number of doubles and the answer for them, and the length of the set for a triple
zero and the answer for it. -/
slots Len Bound Src Free Unread Digits PrimeBound Levels Base NumValues Sorted Val Mul Table Sets Doubles Zero Top AnsSplit NumDoubles AnsDoubles NumZero AnsZero

end Core

open Core in
/-- The parameters, and the arrays. -/
def coreSetup (pParams pPrep : ℕ) : Stmt :=
  .call pParams [v Len, v Bound, v Free] Unread ;;
  .set Digits (M (v Free)) ;;
  .set PrimeBound (M (v Free +' k 1)) ;;
  .set Levels (M (v Free +' k 2)) ;;
  .set Base (v Free +' k 3) ;;
  .call pPrep [v Len, v Bound, v Digits, v PrimeBound, v Src, v Base] NumValues

open Core in
/-- The addresses of the arrays from the sorted copy on. -/
def coreAddr : Stmt :=
  .set Sorted (v Base +' k 6 +' v PrimeBound +' v PrimeBound *' v PrimeBound) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Mul (v Val +' v Len) ;;
  .set Table (v Mul +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Doubles (v Sets +' k 3 *' v Len) ;;
  .set Zero (v Doubles +' v Len) ;;
  .set Top (v Zero +' k 1)

open Core in
/-- The loop over the splittings. -/
def coreSplit (pGrid : ℕ) : Stmt :=
  .call pGrid [v NumValues, v Val, v Table, v Digits, v Sets, v Len, v Levels, v Base, v Top]
    AnsSplit

open Core in
/-- The three-set input for the solutions a + a + c = 0 with a ≠ 0: the doubles of the repeated
values, {0}, and the values. -/
def coreDoubles (pTwice pNodes : ℕ) : Stmt :=
  .call pTwice [v NumValues, v Val, v Mul, v Doubles] NumDoubles ;;
  .call pNodes [v Levels, v Doubles, v NumDoubles, v Zero, k 1, v Val, v NumValues, v Base, v Top]
    AnsDoubles

open Core in
/-- The three-set input for the solution 0 + 0 + 0 = 0: {0} if 0 occurs three times and the empty
set if not, {0}, and {0}. -/
def coreZero (pZero pNodes : ℕ) : Stmt :=
  .call pZero [v NumValues, v Val, v Mul] NumZero ;;
  .call pNodes [v Levels, v Zero, v NumZero, v Zero, k 1, v Zero, k 1, v Base, v Top] AnsZero

open Core in
/-- The answer: 1 if one of the three answers is 1. -/
def coreAnswer : Stmt :=
  .ite (k 0 <' v AnsSplit +' v AnsDoubles +' v AnsZero) (.set Len (k 1)) (.set Len (k 0))

/-- core(n, V, x, b), over the procedures pParams, pPrep, pGrid, pTwice, pZero, pNodes. -/
def coreBody (pParams pPrep pGrid pTwice pZero pNodes : ℕ) : Stmt :=
  coreSetup pParams pPrep ;;
  coreAddr ;;
  coreSplit pGrid ;;
  coreDoubles pTwice pNodes ;;
  coreZero pZero pNodes ;;
  coreAnswer

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Core

/-- The locals after coreSetup: a is the memory map, f the number of levels, nd the number of
distinct values. -/
abbrev setupFrame (a : Map) (V f nd : ℕ) (x b unread : ℤ) : List ℤ :=
  [a.n, V, x, b, unread, a.Λ, a.m, f, a.b, nd]

/-- The locals after coreAddr. -/
abbrev addrFrame (a : Map) (V f nd : ℕ) (x b unread : ℤ) : List ℤ :=
  setupFrame a V f nd x b unread ++ [(a.srt : ℤ), a.val, a.mul, a.bt, a.A, a.tw, a.one, a.top]

end Core

open Core

/-! ## The addresses -/

/-- `coreAddr` takes 42 steps. -/
theorem coreAddr_cost : coreAddr.blockCost = 42 := rfl

/-- coreAddr computes the addresses. -/
theorem coreAddr_runs (a : Map) (V f nd : ℕ) (x b unread : ℤ) (μ : ℕ → ℤ)
    (htop : (a.top : ℤ) ≤ lim.word) (hword : (6 : ℤ) ≤ lim.word := by omega) :
    coreAddr.Runs lim ⟨frame (setupFrame a V f nd x b unread), μ⟩
      (· = ⟨frame (addrFrame a V f nd x b unread), μ⟩) := by
  have hmap := a.layout
  exact ⟨by light_side [coreAddr],
    by simp [coreAddr, update_frame_setLocal, Map.top, Map.one, Map.tw, Map.A, Map.bt, Map.mul,
      Map.val, Map.srt, Map.cnt, Map.pr]⟩

/-! ## The arrays, and a three-set input in the memory -/

namespace Core

/-- The parameters are those of the reduction. -/
structure Par (a : Map) (V f : ℕ) : Prop where
  len_pos : 1 ≤ a.n
  bound_pos : 1 ≤ V
  primeBound : a.m = mPar a.n V
  digits : a.Λ = Lam V
  levels : f = fuel a.n

/-- There is a prime up to m. -/
theorem Par.primes_nonempty {a : Map} {V f : ℕ} (h : Par a V f) : (Nat.primesLE a.m).Nonempty := by
  have hcard := wPar_le_card_primesLE a.n V
  rw [← h.primeBound] at hcard
  have hpos : 1 ≤ wPar a.n V :=
    Nat.mul_pos (by bound) (Nat.succ_pos _)
  grind [Finset.card_pos]

/-- The bound on the primes is positive. -/
theorem Par.primeBound_pos {a : Map} {V f : ℕ} (h : Par a V f) : 1 ≤ a.m :=
  (Finset.card_pos.2 h.primes_nonempty).trans_le (Nat.card_primesLE_le a.m)

/-- The cells that no routine called after coreAddr writes: those below the three sets of a
splitting, and the cell that holds 0. -/
abbrev Fixed (a : Map) (q : ℕ) : Prop := q < a.A ∨ q = a.one

/-- The arrays that the parts after coreAddr read: the distinct values D, how often they occur, the
block of parameters, the primes, the zeros of the count table, and the cell that holds 0. -/
structure Arrays (a : Map) (V : ℕ) (D C : List ℤ) (ν : ℕ → ℤ) : Prop where
  val : Seg ν a.val D
  mul : Seg ν a.mul C
  ctx : CtxAt ν a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt
  primes : PrimesAt ν a.pr #(Nat.primesLE a.m) a.m
  zero : ZeroAt ν a.cnt (a.m * a.m)
  one : ν a.one = 0
  val_le : D.length ≤ a.n
  mul_le : C.length ≤ a.n

section

variable {a : Map} {V : ℕ} {D C : List ℤ} {μ ν : ℕ → ℤ}

/-- The arrays are still there if the fixed cells have not changed. -/
theorem Arrays.of_sameOn (h : Arrays a V D C μ) (hs : SameOn (Fixed a) μ ν) :
    Arrays a V D C ν := by
  have hmap := a.layout
  have hval := h.val_le
  have hmul := h.mul_le
  have hcard := a.m.card_primesLE_le
  exact
    ⟨h.val.of_sameOn hs fun i hi => by omega, h.mul.of_sameOn hs fun i hi => by omega, h.ctx.of_sameOn hs fun i hi => by grind, ⟨rfl, h.primes.2.of_sameOn hs fun i hi => Or.inl (by
        grind [List.length_map, Finset.length_sort])⟩, fun q hq => (hs _ (by omega)).trans (h.zero q hq), (hs _ (Or.inr rfl)).trans h.one, hval, hmul⟩

/-- A set of at most n numbers of absolute value at most V, in the l cells from s, which lie among
the arrays from the values on. -/
structure Placed (a : Map) (V : ℕ) (ν : ℕ → ℤ) (s l : ℕ) (S : Finset ℤ) : Prop where
  set : SetAt ν s l S
  le : l ≤ a.n
  bdd : Bdd V S
  from_val : a.val ≤ s
  below : s + l ≤ a.top

/-- The set of the distinct values. -/
theorem Arrays.placed_val (h : Arrays a V D C ν) (hD : D.Nodup) (hb : Bdd V D.toFinset) :
    Placed a V ν a.val D.length D.toFinset := by
  have hmap := a.layout
  have hval := h.val_le
  exact ⟨⟨D, rfl, h.val, hD, rfl⟩, hval, hb, le_rfl, by omega⟩

/-- The set {0}. -/
theorem Arrays.placed_zero (h : Arrays a V D C ν) (hn : 1 ≤ a.n) : Placed a V ν a.one 1 {0} := by
  have hmap := a.layout
  exact ⟨⟨[0], rfl, by simpa [seg_cons] using h.one, by simp, by simp⟩, hn, bdd_zero V, by omega,
    by omega⟩

variable {s₁ s₂ l₁ s₃ l₃ l₂ : ℕ} {S₁ S₂ S₃ : Finset ℤ}

/-- Three sets among the arrays are a three-set input as the recursive procedure wants it. -/
theorem Arrays.nodesPre {r : ℕ → ℕ → Need} {f : ℕ}
    (h : Arrays a V D C ν) (hpar : Par a V f) (p₁ : Placed a V ν s₁ l₁ S₁)
    (p₂ : Placed a V ν s₂ l₂ S₂) (p₃ : Placed a V ν s₃ l₃ S₃)
    (hok : (nodesNeed r a.n V a.m f).Ok lim a.top d) :
    NodesPre lim r ν ⟨⟨a.top, a.n, V, a.m, #(Nat.primesLE a.m), a.pr, a.cnt⟩, ⟨s₁, l₁, S₁⟩,
      ⟨s₂, l₂, S₂⟩, ⟨s₃, l₃, S₃⟩⟩ a.Λ a.cx f d := by
  have hmap := a.layout
  have hcard := a.m.card_primesLE_le
  light_facts p₁ p₂ p₃
  exact
    ⟨⟨⟨h.primes, h.zero, by grind, by linarith,
            by grind⟩, ⟨p₁.set, p₁.le, p₁.bdd, p₁.below, by grind⟩, ⟨p₂.set, p₂.le, p₂.bdd, p₂.below, by grind⟩, ⟨p₃.set, p₃.le, p₃.bdd, p₃.below, by grind⟩⟩, h.ctx, by grind, by grind, hpar.bound_pos, hpar.primeBound_pos, hpar.digits, hpar.primes_nonempty, hok⟩

/-- The recursive procedure, called for three sets among the arrays. -/
theorem Arrays.nodes_meets {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {pNodes f : ℕ}
    (hNodes : NodesSpec lim P pNodes T r) (h : Arrays a V D C ν)
    (hpar : Par a V f) (p₁ : Placed a V ν s₁ l₁ S₁) (p₂ : Placed a V ν s₂ l₂ S₂)
    (p₃ : Placed a V ν s₃ l₃ S₃) (hok : (nodesNeed r a.n V a.m f).Ok lim a.top d) :
    Meets lim P pNodes d [(f : ℤ), s₁, l₁, s₂, l₂, s₃, l₃, a.cx, a.top] ν
      (tNodes T a.n V a.m #(Nat.primesLE a.m) (treeCalls (Nat.primesLE a.m) a.Λ f S₁ S₂ S₃))
      fun res μ' => res = flag (TreeYes a.m a.Λ f V S₁ S₂ S₃) ∧ Kept ν μ' a.top :=
  hNodes f _ a.Λ a.cx ν d (h.nodesPre hpar p₁ p₂ p₃ hok)

end

end Core

/-! ## The three answers -/

namespace Core

/-- What the parts after coreAddr assume: the parameters, the values of the input X, the arrays in
the memory μ, and what the limits must allow. -/
structure Ctx (lim : Limits) (r : ℕ → ℕ → Need) (d : ℕ) (a : Map) (V f : ℕ) (X D C : List ℤ)
    (μ : ℕ → ℤ) : Prop where
  par : Par a V f
  values : Values a.n X D C
  arrays : Arrays a V D C μ
  bddVal : Bdd V D.toFinset
  bddDoubles : Bdd V (twiceSet (vecOf a.n X))
  space : (lim.space : ℤ) ≤ lim.word
  cells : a.top + (nodesNeed r a.n V a.m f).cells ≤ lim.space
  word : ((nodesNeed r a.n V a.m f).word : ℤ) + 8 * V + 4 * a.n + 64 ≤ lim.word
  depth : d + (nodesNeed r a.n V a.m f).depth + 4 ≤ lim.depth

section

variable {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}

/-- The limits allow for a call of nodes. -/
theorem Ctx.okNodes (K : Ctx lim r d a V f X D C μ) :
    (nodesNeed r a.n V a.m f).Ok lim a.top (d + 1) :=
  ⟨by have := K.word; omega, K.cells, K.space, by have := K.depth; omega⟩

/-- The limits allow for a call of grid. -/
theorem Ctx.okGrid (K : Ctx lim r d a V f X D C μ) :
    (gridNeed r a.n V a.m f 2).Ok lim a.top (d + 1) :=
  ⟨by have := K.word; grind [gridNeed], K.cells, K.space,
    by have := K.depth; grind [gridNeed]⟩

/-- The recursive procedure stays within the time for a tree with f levels. -/
theorem tNodes_le_tTree (T : ℕ → ℕ → ℕ) (n V m np Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃) ≤ tTree T n V m np f :=
  Nat.mul_le_mul_right _ (by grind [ChRound.treeCalls_le_pow])

/-- The set for a triple zero lies in the cell that holds 0; its length is the answer of
zeroThree. -/
theorem Ctx.placed_zeroSet (K : Ctx lim r d a V f X D C μ) (h : Arrays a V D C ν) :
    ∃ l : ℕ, flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) = (l : ℤ) ∧
      Placed a V ν a.one l (zeroSet (vecOf a.n X)) := by
  have hmap := a.layout
  have hzero := h.placed_zero K.par.len_pos
  by_cases h3 : 3 ≤ #{i | vecOf a.n X i = 0}
  · refine ⟨1, by rw [flag_of (K.values.zeroThree.2 h3)]; rfl, ?_⟩
    grind [zeroSet]
  · refine ⟨0, by rw [flag_of_not (mt K.values.zeroThree.1 h3)]; rfl, ?_⟩
    rw [zeroSet, if_neg h3]
    exact ⟨⟨[], rfl, Seg.nil, by simp, by simp⟩, Nat.zero_le _, by tauto,
      by omega, by omega⟩

end

end Core

section parts

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}
  {x b unread : ℤ}

variable {pGrid : ℕ}

/-- grid, called for the arrays of a map. -/
theorem grid_meets_of_map (hGrid : GridSpec lim P pGrid T r)
    (hF : FrontMem μ (a.front V D)) (H : GridPre lim r (a.front V D) f 2 d) :
    Meets lim P pGrid d [(D.length : ℤ), a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.top] μ
      (tGrid T a.n V a.m #(Nat.primesLE a.m) f a.Λ) fun res μ' =>
      res = flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, SplitYes a.m a.Λ f V D.toFinset β β' v) ∧
        KeptBut μ μ' a.top a.A (3 * a.n) :=
  hGrid _ f μ hF d H

/-- coreSplit decides whether some splitting gives a yes-instance. -/
theorem coreSplit_ends (hGrid : GridSpec lim P pGrid T r)
    (K : Ctx lim r d a V f X D C μ)
    (hF : FrontMem μ (a.front V D)) :
    Ends lim P d (coreSplit pGrid) ⟨frame (addrFrame a V f D.length x b unread), μ⟩
      (tGrid T a.n V a.m #(Nat.primesLE a.m) f a.Λ + 11) fun σ' => ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame (addrFrame a V f D.length x b unread ++
          [flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, SplitYes a.m a.Λ f V D.toFinset β β' v)]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have hmap := a.layout
  have hdepth := K.depth
  -- ansSplit := grid(numValues, val, table, digits, sets, len, levels, base, top)
  light_call (grid_meets_of_map hGrid hF ⟨K.par.bound_pos, K.par.primeBound_pos, K.par.digits,
    K.par.primes_nonempty, K.okGrid⟩) with _ μ' ⟨rfl, hkept⟩
  exact ⟨μ', rfl, hkept.mono fun q hq => by omega⟩

variable {pNodes : ℕ}

/-- coreDoubles decides the three-set input for the solutions that use a value other than 0
twice. -/
theorem coreDoubles_ends {pTwice : ℕ} (hTwice : TwiceSpec lim P pTwice)
    (hNodes : NodesSpec lim P pNodes T r) (K : Ctx lim r d a V f X D C μ)
    (hν : SameOn (Fixed a) μ ν) (ans : ℤ) :
    Ends lim P d (coreDoubles pTwice pNodes)
      ⟨frame (addrFrame a V f D.length x b unread ++ [ans]), ν⟩
      (tTwice a.n + tTree T a.n V a.m #(Nat.primesLE a.m) f + 17) fun σ' =>
        ∃ (len : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (addrFrame a V f D.length x b unread ++ [ans, len,
          flag (TreeYes a.m a.Λ f V (twiceSet (vecOf a.n X)) {0} D.toFinset)]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have hmap := a.layout
  have hval := K.arrays.val_le
  light_facts K
  have hlenC : C.length = D.length := by rw [K.values.counts, List.length_map]
  have harr := K.arrays.of_sameOn hν
  have htime : tTwice D.length ≤ tTwice a.n := by grind [tTwice]
  have htree := tNodes_le_tTree T a.n V a.m #(Nat.primesLE a.m) a.Λ f
    (twiceSet (vecOf a.n X)) {0} D.toFinset
  -- numDoubles := twice(numValues, val, mul, doubles)
  light_call (hTwice _ a.val a.mul a.tw V D C ν
    ⟨hlenC, fun y hy => by aesop, harr.val, harr.mul, by omega, by omega, by omega, by omega, by omega, K.space, by omega⟩) with _ ν₁ ⟨rfl, hdoubles, hsame⟩
  have hν₁ : SameOn _ μ ν₁ := hν.trans (by grind [SameOn.mono])
  have harr₁ := K.arrays.of_sameOn hν₁
  have hplaced : Placed a V ν₁ a.tw (twiceList D C).length _ :=
    ⟨⟨_, rfl, hdoubles, K.values.twice.1, K.values.twice.2⟩,
      by grind [length_twiceList_le], K.bddDoubles, by omega,
      by grind [length_twiceList_le]⟩
  -- ansDoubles := nodes(levels, doubles, numDoubles, zero, 1, val, numValues, base, top)
  light_call (harr₁.nodes_meets hNodes K.par hplaced (harr₁.placed_zero K.par.len_pos)
    (harr₁.placed_val K.values.nodup K.bddVal) K.okNodes) with _ μ' ⟨rfl, hkept⟩
  exact ⟨_, μ', rfl, hν₁.trans (hkept.mono fun q hq => by omega)⟩

/-- coreZero decides the three-set input for the solution that uses 0 three times. -/
theorem coreZero_ends {pZero : ℕ} (hZero : ZeroThreeSpec lim P pZero)
    (hNodes : NodesSpec lim P pNodes T r) (K : Ctx lim r d a V f X D C μ)
    (hν : SameOn (Fixed a) μ ν) (ans₁ len ans₂ : ℤ) :
    Ends lim P d (coreZero pZero pNodes)
      ⟨frame (addrFrame a V f D.length x b unread ++ [ans₁, len, ans₂]), ν⟩
      (tZeroThree a.n + tTree T a.n V a.m #(Nat.primesLE a.m) f + 16) fun σ' =>
        ∃ (len' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (addrFrame a V f D.length x b unread ++ [ans₁, len,
          ans₂, len', flag (TreeYes a.m a.Λ f V (zeroSet (vecOf a.n X)) {0} {0})]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have hmap := a.layout
  light_facts K K.arrays
  have hlenC : C.length = D.length := by rw [K.values.counts, List.length_map]
  have harr := K.arrays.of_sameOn hν
  have htime : tZeroThree D.length ≤ tZeroThree a.n := by grind [tZeroThree]
  have htree := tNodes_le_tTree T a.n V a.m #(Nat.primesLE a.m) a.Λ f
    (zeroSet (vecOf a.n X)) {0} {0}
  obtain ⟨l, hflag, hplaced⟩ := K.placed_zeroSet harr
  have hzero := harr.placed_zero K.par.len_pos
  -- numZero := zeroThree(numValues, val, mul)
  light_call (hZero _ a.val a.mul D C ν hlenC harr.val harr.mul (by omega)
    (by omega) K.space (by omega)) with _ ν₁ ⟨rfl, hν₁⟩
  rw [hν₁, hflag]
  -- ansZero := nodes(levels, zero, numZero, zero, 1, zero, 1, base, top)
  light_call (harr.nodes_meets hNodes K.par hplaced hzero hzero K.okNodes)
    with _ μ' ⟨rfl, hkept⟩
  exact ⟨_, μ', rfl, hν.trans (hkept.mono fun q hq => by omega)⟩

/-- `coreAnswer` takes 10 steps. -/
theorem coreAnswer_cost : coreAnswer.blockCost = 10 := rfl

/-- coreAnswer returns 1 if one of the three answers is yes, and 0 if not. -/
theorem coreAnswer_runs (G₁ G₂ G₃ : Prop) (nd : ℕ) (len₂ len₃ : ℤ) (hword : (6 : ℤ) ≤ lim.word := by omega) :
    coreAnswer.Runs lim
      ⟨frame (addrFrame a V f nd x b unread ++ [flag G₁, len₂, flag G₂, len₃, flag G₃]), μ⟩
      fun σ' => σ'.loc 0 = flag (G₁ ∨ G₂ ∨ G₃) ∧ σ'.mem = μ := by
  have h₁ := flag_mem G₁
  have h₂ := flag_mem G₂
  have h₃ := flag_mem G₃
  have hpos := ChCore.flag_sum_pos G₁ G₂ G₃
  by_cases h : G₁ ∨ G₂ ∨ G₃
  · exact ⟨by light_side [coreAnswer], by simp_all [coreAnswer, flag_of]⟩
  · exact ⟨by light_side [coreAnswer], by simp_all [coreAnswer, flag_of_not]⟩

end parts

/-! ## The parameters and the arrays -/

namespace Core

/-- What coreSetup leaves in the memory μ': the arrays for the values D of the input X, with how
often they occur; nothing below the free pointer b has changed. -/
structure Setup (a : Map) (V b : ℕ) (X D C : List ℤ) (μ μ' : ℕ → ℤ) : Prop where
  values : Values a.n X D C
  mul : Seg μ' a.mul C
  one : μ' a.one = 0
  front : FrontMem μ' (a.front V D)
  kept : Kept μ μ' b

end Core

variable {pParams pPrep : ℕ}

/-- coreSetup computes the parameters and fills the arrays. -/
theorem coreSetup_ends (hParams : ParamsSpec lim P pParams)
    (hPrep : PrepSpec lim P pPrep) {r : ℕ → ℕ → Need} {a : Map} {V f x b : ℕ} {X : List ℤ}
    {μ : ℕ → ℤ} (hpar : Par a V f) (hb : a.b = b + 3) (hlen : X.length = a.n) (hX : AbsLe X V)
    (hseg : Seg μ x X) (hxb : x + a.n ≤ b) (hok : (coreNeed r a.n V).Ok lim b d) :
    Ends lim P d (coreSetup pParams pPrep) ⟨frame [a.n, V, x, b], μ⟩
      (tParams a.n V + tPrep a.n a.Λ a.m + 30) fun σ' =>
        ∃ (unread : ℤ) (D C : List ℤ) (μ' : ℕ → ℤ),
          σ' = ⟨frame (setupFrame a V f D.length x b unread), μ'⟩ ∧ Setup a V b X D C μ μ' := by
  have hmap := a.layout
  have hspace := hok.space
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits]
    at hcells hword hdepth
  light_call (hParams _ a.n V b μ (by omega) hspace
    (by rw [← hpar.primeBound]; grind) (by omega)) with unread μ₁ ⟨hcellsP, hsame₁⟩
  rw [← hpar.primeBound, ← hpar.digits, ← hpar.levels] at hcellsP
  have hdigits : μ₁ b = a.Λ := by simpa using hcellsP 0 (by simp)
  have hprime : μ₁ (b + 1) = a.m := by aesop
  have hlevels : μ₁ (b + 2) = f := by aesop
  have haddr₁ : ((b : ℤ) + 1).toNat = b + 1 := by omega
  have haddr₂ : ((b : ℤ) + 2).toNat = b + 2 := by omega
  -- digits := mem[free]; primeBound := mem[free + 1]; levels := mem[free + 2]; base := free + 3
  light_set a.Λ using hdigits
  light_set a.m using haddr₁, hprime
  light_set f using haddr₂, hlevels
  light_set a.b using hb
  -- numValues := prep(len, bound, digits, primeBound, src, base)
  light_call (hPrep _ a V x X μ₁
    ⟨hlen, hX, by omega, hpar.bound_pos, hpar.digits, ⟨by simp [prepNeed]; grind, by grind [prepNeed], hspace,
        by grind [prepNeed]⟩⟩ (hseg.of_sameOutside hsame₁ (by omega)))
    with _ μ₂ ⟨⟨D, C, rfl, hvalues, hmul, hone, hfront⟩, hkept₂⟩
  exact ⟨unread, D, C, μ₂, rfl, hvalues, hmul, hone, hfront,
    fun q hq => (hkept₂ q (by omega)).trans (by aesop)⟩

/-- After coreSetup the other parts find what they assume. -/
theorem Core.Setup.ctx {r : ℕ → ℕ → Need} {a : Map} {b : ℕ} {X D C : List ℤ} {μ μ' : ℕ → ℤ}
    (S : Setup a (2 * U) b X D C μ μ') (hpar : Par a (2 * U) (fuel a.n)) (hb : a.b = b + 3)
    (hx : ∀ i, |vecOf a.n X i| ≤ (U : ℤ)) (hok : (coreNeed r a.n (2 * U)).Ok lim b d) :
    Ctx lim r d a (2 * U) (fuel a.n) X D C μ' := by
  have hmap := a.layout
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits] at hcells hword hdepth
  exact
    ⟨hpar, S.values, ⟨S.front.segVal, S.mul, S.front.ctx, S.front.primes, S.front.zero, S.one, S.values.length_le, by rw [S.values.counts, List.length_map]; exact S.values.length_le⟩, S.front.bdd, bdd_twiceSet hx, hok.space, by omega, by omega, by omega⟩

variable {pTwice pNodes pGrid pZero : ℕ}

/-! ## The routine -/

/-- The six parts one after the other, for the memory map a with the base b + 3. -/
theorem coreBody_ends {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hTwice : TwiceSpec lim P pTwice)
    (hZero : ZeroThreeSpec lim P pZero) (hNodes : NodesSpec lim P pNodes T r) {a : Map}
    {x b : ℕ} {X : List ℤ} {μ : ℕ → ℤ} (hpar : Par a (2 * U) (fuel a.n)) (hb : a.b = b + 3)
    (hlen : X.length = a.n) (hx : ∀ i, |vecOf a.n X i| ≤ (U : ℤ)) (hX : AbsLe X (2 * U : ℕ))
    (hseg : Seg μ x X) (hxb : x + a.n ≤ b) (hok : (coreNeed r a.n (2 * U)).Ok lim b d) :
    Ends lim P d (coreBody pParams pPrep pGrid pTwice pZero pNodes)
      ⟨frame [a.n, ((2 * U : ℕ) : ℤ), x, b], μ⟩ (coreTime T a.n (2 * U)) fun σ' =>
        σ'.loc 0 = flag (ThreeSum (vecOf a.n X)) ∧ Kept μ σ'.mem b := by
  have hmap := a.layout
  have hfinal := threeSum_iff_trees hpar.len_pos _ hx
  have htime := ChCore.time_le T a.n (2 * U)
  rw [← hpar.primeBound, ← hpar.digits] at hfinal htime
  have hcostAddr := coreAddr_cost
  have hcostAnswer := coreAnswer_cost
  light_piece (coreSetup_ends hParams hPrep hpar hb hlen hX hseg hxb hok)
    with _ ⟨unread, D, C, μ₁, rfl, S⟩
  rw [← S.values.values] at hfinal
  have K := S.ctx hpar hb hx hok
  light_facts K
  -- coreAddr
  refine Ends.next _ (Ends.block ((coreAddr_runs a _ _ D.length x b unread μ₁
    (by omega)).mono ?_) le_rfl)
  rintro _ rfl
  -- coreSplit
  light_piece (coreSplit_ends hGrid K S.front) with _ ⟨μ₂, rfl, hμ₂⟩
  -- coreDoubles
  light_piece (coreDoubles_ends hTwice hNodes K hμ₂ _) with _ ⟨len₂, μ₃, rfl, hμ₃⟩
  -- coreZero
  light_piece (coreZero_ends hZero hNodes K hμ₃ _ _ _) with _ ⟨len₃, μ₄, rfl, hμ₄⟩
  -- coreAnswer
  refine Ends.block ((coreAnswer_runs _ _ _ _ _ _).mono ?_)
  rintro σ' ⟨hres, hmem⟩
  exact ⟨by simp_all, fun q hq => by
    rw [hmem, hμ₄ q (by omega), S.kept q hq]⟩

/-- **core meets its specification**, in every program that holds its body and meets the
specifications of the routines that it calls. -/
theorem core_spec {p : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hP : P[p]? = some (coreBody pParams pPrep pGrid pTwice pZero pNodes))
    (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hTwice : TwiceSpec lim P pTwice)
    (hZero : ZeroThreeSpec lim P pZero) (hNodes : NodesSpec lim P pNodes T r) :
    CoreSpec lim P p T r := by
  intro d n U x b X μ hlen hXU hseg hxb hn hU hok
  have hx : ∀ i, |vecOf n X i| ≤ U := fun i => by
    simp [vecOf]
    aesop
  exact ⟨_, hP, coreBody_ends hParams hPrep hGrid hTwice hZero hNodes
    (a := ⟨b + 3, n, Lam _, mPar n _⟩) ⟨hn, by omega, rfl, rfl, rfl⟩ rfl hlen hx
    (fun y hy => (hXU y hy).trans (by omega)) hseg hxb hok⟩
