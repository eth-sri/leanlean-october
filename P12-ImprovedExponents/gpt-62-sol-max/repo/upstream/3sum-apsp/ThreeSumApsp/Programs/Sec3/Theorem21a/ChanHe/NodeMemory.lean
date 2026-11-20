/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Recursion

/-!
# The reduction from 3SUM to Convolution-3SUM: the memory of a node, and what fits in a word

What the routines below the recursion tree of [CH20, Theorem 5.1] share (for
Theorem 21(a)).

* A set in the memory (`SetAt`), the memory of a node (`NodeMem`) and the block of parameters
  (`CtxAt`) only depend on cells below the free pointer (`SetAt.kept`, `NodeMem.kept`,
  `CtxAt.kept`).
* Each of the three sets, with the count table, is what coll and heavy ask for (`Slot.Ok.bucket`).
* A child of a node has the heavy elements of one of the three sets in place of that set
  (`NodeArgs.child`, `NodeMem.child`).
* The bound `wordNeed` on the words is monotone in n and M (`wordNeed_mono`) and covers every
  product of a number up to (n + 1)², a number up to M + 1 and a number up to 64 (V + 1)
  (`mul_le_wordNeed`; `mul_le_word` and `le_word_of_le` are the forms that the routines use).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

theorem slot_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  omega

/-! ## The memory -/

section memory

variable {μ μ' : ℕ → ℤ} {fr V m np pr cnt s len : ℕ} {S : Finset ℤ} {e : Env} {X : Slot}
  {a : NodeArgs}

/-- A set is preserved if the cells holding it are preserved. -/
theorem SetAt.of_sameOn {R : ℕ → Prop} (h : SetAt μ s len S) (hk : SameOn R μ μ')
    (hR : ∀ i < len, R (s + i)) : SetAt μ' s len S := by
  obtain ⟨L, rfl, hs, hn, ht⟩ := h
  exact ⟨L, rfl, hs.of_sameOn hk hR, hn, ht⟩

/-- A set below the free pointer is still there if no cell below the free pointer has changed. -/
theorem SetAt.kept (h : SetAt μ s len S) (hb : s + len ≤ fr) (hk : Kept μ μ' fr) :
    SetAt μ' s len S := h.of_sameOn hk fun i hi => by omega

/-- The length of a set in the memory is its number of elements. -/
theorem SetAt.card (h : SetAt μ s len S) : #S = len := by
  obtain ⟨L, hL, -, hn, ht⟩ := h
  rw [← ht, List.toFinset_card_of_nodup hn, hL]

/-- A set of length 0 is empty. -/
theorem SetAt.eq_empty (h : SetAt μ s len S) (h0 : len = 0) : S = ∅ :=
  Finset.card_eq_zero.1 (h.card.trans h0)

/-- There are at most as many heavy elements as elements. -/
theorem card_heavy_le (h : SetAt μ s len S) (M : ℕ) : #(ChanHe.heavy S M) ≤ len :=
  h.card ▸ Finset.card_le_card (heavy_subset S M)

/-- The primes and the count table only depend on the cells below the free pointer. -/
theorem Env.Ok.kept (h : e.Ok μ) (hk : Kept μ μ' e.fr) : e.Ok μ' :=
  { h with
    primes := ⟨h.primes.1, h.primes.2.congr fun i hi => hk _ (by
      have hbelow := h.belowPr
      have hnp := h.primes.1
      simp_all <;> omega)⟩
    zero := fun r hr => (hk _ (by have := h.belowCnt; omega)).trans (h.zero r hr) }

/-- A set of a node only depends on the cells below the free pointer. -/
theorem Slot.Ok.kept (h : X.Ok μ e) (hk : Kept μ μ' e.fr) : X.Ok μ' e :=
  { h with set := h.set.kept h.below hk }

/-- What a node needs in the memory only depends on the cells below the free pointer. -/
theorem NodeMem.kept (h : NodeMem μ a) (hk : Kept μ μ' a.fr) : NodeMem μ' a :=
  ⟨h.envOk.kept hk, fun i => (h.slotOk i).kept hk⟩

/-- A set of a node with the count table, as coll and heavy want them. -/
theorem Slot.Ok.bucket (h : X.Ok μ e) (he : e.Ok μ) {M : ℕ} (hM : 1 ≤ M) (hMm : M ≤ e.m * e.m) :
    BucketMem μ e.fr e.V M X.addr X.len e.cnt (e.m * e.m) X.set :=
  ⟨hM, hMm, h.bdd, h.set, he.zero, h.below, he.belowCnt, h.apart⟩

/-! ### The children of a node

A child has the heavy elements of one of the three sets in place of that set.  They are written at
the free pointer, which moves on by the length of the set. -/

/-- What the routines share, after `len` cells from the free pointer have been taken. -/
@[simp] def Env.push (e : Env) (len : ℕ) : Env := { e with fr := e.fr + len }

/-- The heavy elements of a set modulo `M`, at the address `fr`. -/
@[simp] def Slot.heavy (X : Slot) (fr M : ℕ) : Slot :=
  ⟨fr, #(ChanHe.heavy X.set M), ChanHe.heavy X.set M⟩

/-- A node, after `len` cells from the free pointer have been taken. -/
@[simp] def NodeArgs.push (a : NodeArgs) (len : ℕ) : NodeArgs :=
  { a with toEnv := a.toEnv.push len }

/-- A child replaces one set by its heavy elements. -/
def NodeArgs.child (a : NodeArgs) (i : Fin 3) (M : ℕ) : NodeArgs :=
  ⟨a.toEnv.push (a.slot i).len, Function.update a.slot i ((a.slot i).heavy a.fr M)⟩

/-- The primes and the count table are not touched when cells from the free pointer on are
written. -/
theorem Env.Ok.push (h : e.Ok μ) (hk : KeptBut μ μ' (e.fr + len) e.fr len) : (e.push len).Ok μ' :=
  { h.kept (hk.mono fun b hb => by omega) with
    belowPr := h.belowPr.trans (Nat.le_add_right _ _)
    belowCnt := h.belowCnt.trans (Nat.le_add_right _ _) }

/-- A set of a node is not touched when cells from the free pointer on are written. -/
theorem Slot.Ok.push (h : X.Ok μ e) (hk : KeptBut μ μ' (e.fr + len) e.fr len) :
    X.Ok μ' (e.push len) :=
  { h.kept (hk.mono fun b hb => by omega) with below := h.below.trans (Nat.le_add_right _ _) }

/-- A node is not touched when cells from the free pointer on are written. -/
theorem NodeMem.push (h : NodeMem μ a) (hk : KeptBut μ μ' (a.fr + len) a.fr len) :
    NodeMem μ' (a.push len) :=
  ⟨h.envOk.push hk, fun i => (h.slotOk i).push hk⟩

/-- The heavy elements of a set of a node, written at the free pointer, are a set of the child. -/
theorem Slot.Ok.heavy (h : X.Ok μ e) (he : e.Ok μ) {M : ℕ}
    (hs : SetAt μ' e.fr #(ChanHe.heavy X.set M) (ChanHe.heavy X.set M)) :
    (X.heavy e.fr M).Ok μ' (e.push X.len) where
  set := hs
  le := (card_heavy_le h.set M).trans h.le
  bdd := h.bdd.mono (heavy_subset _ _)
  below := Nat.add_le_add_left (card_heavy_le h.set M) _
  apart := Or.inr he.belowCnt

/-- The new set lies in the space just allocated and the other sets are preserved. -/
theorem NodeMem.child (h : NodeMem μ a) (i : Fin 3) {M : ℕ}
    (hk : KeptBut μ μ' (a.fr + (a.slot i).len) a.fr (a.slot i).len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy (a.slot i).set M) (ChanHe.heavy (a.slot i).set M)) :
    NodeMem μ' (a.child i M) := by
  refine ⟨h.envOk.push hk, fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    simpa [NodeArgs.child] using (h.slotOk i).heavy h.envOk hs
  · simpa [NodeArgs.child, Function.update_of_ne hji] using (h.slotOk j).push hk

theorem CtxAt.kept {cx Λ : ℕ} (h : CtxAt μ cx V m Λ np pr cnt) (hb : cx + 6 ≤ fr)
    (hk : Kept μ μ' fr) : CtxAt μ' cx V m Λ np pr cnt :=
  Seg.congr h fun i hi => hk _ (by grind)

end memory

/-! ## Words -/

/-- A product of three factors that fits in the words of the routines below the tree. -/
theorem mul_le_wordNeed {x y z n V M : ℕ} (hx : x ≤ (n + 1) ^ 2) (hy : y ≤ M + 1)
    (hz : z ≤ 64 * (V + 1)) : x * y * z ≤ wordNeed n V M :=
  calc x * y * z ≤ (n + 1) ^ 2 * (M + 1) * (64 * (V + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
    _ = wordNeed n V M := by unfold wordNeed; ring

/-- The same for the limits: the product fits in a word. -/
theorem mul_le_word {lim : Limits} {x y z n V M : ℕ} (h : ((wordNeed n V M : ℕ) : ℤ) ≤ lim.word)
    (hx : x ≤ (n + 1) ^ 2) (hy : y ≤ M + 1) (hz : z ≤ 64 * (V + 1)) :
    (x : ℤ) * y * z ≤ lim.word :=
  le_trans (by exact_mod_cast mul_le_wordNeed hx hy hz) h

/-- A number up to M + 1 fits in a word. -/
theorem le_word_of_le {lim : Limits} {y n V M : ℕ} (h : ((wordNeed n V M : ℕ) : ℤ) ≤ lim.word)
    (hy : y ≤ M + 1) : (y : ℤ) ≤ lim.word := by
  simpa using mul_le_word (x := 1) (z := 1) h (Nat.one_le_pow _ _ (by omega)) hy (by omega)

/-- Larger sets and larger moduli need larger words. -/
theorem wordNeed_mono {n n' V M M' : ℕ} (hn : n ≤ n') (hM : M ≤ M') :
    wordNeed n V M ≤ wordNeed n' V M' := by
  unfold wordNeed
  gcongr

end Light.Sec3.ChanHe
