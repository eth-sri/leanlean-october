/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.GradedMatching

/-! # Projected finite-template extension systems

Exact labels belong to independent source and target template types. Compatibility is a
separate relation, not equality of these labels. Matching receipts retain finite covers and
selectors, so tuples may repeat coordinates or be empty. Extension retains the entire root
cover literally. Only the BF comparison, not an isomorphism, is concluded.
-/

@[expose] public section

namespace VaughtConjecture.ModelTheory

open FirstOrder Language

universe u v w w' r s t

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- Ranked receipts up to a specified budget, with explicit atomic and extension evidence.
No seed is built into the laws: the comparison theorem requires an actual initial receipt. -/
structure RankedMatchingFamily (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L.IsRelational] [L.Structure M] [L.Structure N] (height : Ordinal) where
  Receipt : Ordinal → (n : ℕ) → (Fin n → M) → (Fin n → N) → Type r
  atomic : ∀ {n a b}, Receipt 0 n a b → SameAtomicType (L := L) a b
  lower : ∀ {α β n a b}, β ≤ α → α ≤ height → Receipt α n a b →
    Nonempty (Receipt β n a b)
  forth : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b → ∀ x : M,
    ∃ y : N, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y))
  back : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b → ∀ y : N,
    ∃ x : M, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y))

namespace RankedMatchingFamily

/-- A receipt family compares its explicitly matched tuples at the requested budget.
The library owns the ordinal induction; the local family supplies its laws and seed. -/
theorem bfEquiv_of_nonempty {height : Ordinal}
    (F : RankedMatchingFamily.{u, v, w, w', r} L M N height)
    {α : Ordinal} (hα : α ≤ height) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (seed : Nonempty (F.Receipt α n a b)) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_nonempty_gradedReceipt F.Receipt F.atomic F.lower F.forth F.back hα seed

/-- The data-valued seed form of the comparison theorem. -/
theorem bfEquiv {height : Ordinal}
    (F : RankedMatchingFamily.{u, v, w, w', r} L M N height)
    {α : Ordinal} (hα : α ≤ height) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (seed : F.Receipt α n a b) : BFEquiv (L := L) α n a b :=
  F.bfEquiv_of_nonempty hα ⟨seed⟩





