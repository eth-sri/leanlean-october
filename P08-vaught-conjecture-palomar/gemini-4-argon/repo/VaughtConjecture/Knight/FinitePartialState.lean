/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteTupleGeometry
public import VaughtConjecture.TypeTower.RealizationExtension

/-! # Finite partial diagrams and literal master installation

Fresh one-point and arbitrarily padded extensions preserve consistency and all old
master labels, including invisible faces. No request census or infinite run is imported. -/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd
universe w
namespace FixedHeight
open KnightRealization
variable {M : Type w} {β : LimitStage}

/-! ### 4. The minimal partial state -/

/-- `A'` **extends** `A`: every evaluation of `A` is an evaluation of `A'` (labels never
change, only `none` becomes `some`).  The order of the ω-step (shape shared with
`origin/e7/partial-density`). -/
def Extends (A A' : KnightRealization β M) : Prop :=
  Realization.Extends A A'

/-- The points a partial state has touched. -/
def UsedPoints (A : KnightRealization β M) : Set M :=
  {x | ∃ (n : ℕ) (s : Fin n ↪ M), ((A.eval s).isSome ∧ x ∈ Set.range s)}

/-- `y` is **fresh** for `A`: on no evaluated tuple. -/
def FreshFor (A : KnightRealization β M) (y : M) : Prop :=
  y ∉ UsedPoints A

/-- **The minimal partial state** of the fixed-height lane: exactly consistent where
defined, finitely many used points.  Nothing else — no receipt, failure certificate, Karp
trace, or source link (the #47 independence contract), and no source/lift stratum (contrast
`origin/e7/partial-density`'s `PartialCandidate`). -/
structure IsPartialState (A : KnightRealization β M) : Prop where
  /-- Exactly consistent where defined. -/
  consistent : A.IsExactParentConsistent
  /-- Finitely many used points (so a fresh occurrence always exists, `exists_fresh`). -/
  finite : (UsedPoints A).Finite

/-- **A fresh occurrence always exists** over a finite partial state on an infinite carrier:
the ω-step chooses the occurrence jointly with the request. -/
theorem exists_fresh [Infinite M] {A : KnightRealization β M}
    (hfin : (UsedPoints A).Finite) {n : ℕ} (t : Fin n ↪ M) :
    ∃ y : M, y ∉ Set.range t ∧ FreshFor A y := by
  obtain ⟨y, hy⟩ := (hfin.union (Set.finite_range t)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hy
  exact ⟨y, hy.2, hy.1⟩

/-! ### The one-event extension

Adapted from `origin/e7/partial-density` (the factor-through-`w` closure), WITHOUT the
source/lift stratum: here overlaps between the new faces and the old commitments are
excluded by freshness of the occurrence, not arbitrated by a source. -/

/-! ### The freshness preservation theorem

One coface event at a fresh occurrence preserves the partial state.  In
`origin/e7/partial-density` the analogous preservation is arbitrated by the source; here
there is no source, and every overlap between the new faces and the old commitments is
excluded by freshness: a face of the new tuple avoiding the fresh point is a face of the old
base `t`, where `A`'s own exact consistency at `t` supplies the identical value. -/

/-- **Master discipline**: every evaluated tuple of the state factors through the single
master tuple (the shape a master-relative run maintains — the seed satisfies it vacuously,
and a `stepMaster` chain preserves it for the new master). -/
def MasteredBy (A : KnightRealization β M) {N : ℕ} (w : Fin N ↪ M) : Prop :=
  ∀ ⦃n : ℕ⦄ (s : Fin n ↪ M), (A.eval s).isSome → ∃ f : Fin n ↪ Fin N, f.trans w = s

/-- Under master discipline every used point is on the master. -/
theorem usedPoints_subset_of_masteredBy {A : KnightRealization β M} {N : ℕ}
    {w : Fin N ↪ M} (hM : MasteredBy A w) : UsedPoints A ⊆ Set.range w := by
  rintro x ⟨n, s, hs, i, hi⟩
  obtain ⟨f, rfl⟩ := hM s hs
  exact ⟨f i, hi⟩
