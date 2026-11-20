/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.Basic
public import VaughtConjecture.Knight.Reduction

@[expose] public section

namespace VaughtConjecture.Knight

/-- The **limit stages**: the limit ordinals, the index set of Knight's type spaces
(Def. 3.1.1), ordered as ordinals. -/
def LimitStage : Type 1 := {α : Ordinal.{0} // Order.IsSuccLimit α}

namespace LimitStage

noncomputable instance : LinearOrder LimitStage :=
  inferInstanceAs (LinearOrder {α : Ordinal.{0} // Order.IsSuccLimit α})

/-- The underlying ordinal of a limit stage. -/
abbrev toOrdinal (α : LimitStage) : Ordinal.{0} := α.1

end LimitStage

/-- Knight's stage types as a type tower over the limit stages: `Ty α n := S α n`,
`pull := typeMap` (partial: defined on the visible faces), `reduce := reduceType` (labels
truncated, semantics fixed).  The paper-faithful A4 instance (#88, #89). -/
noncomputable def knightTower : TypeTower.{1} LimitStage where
  Ty α n := S α.1 n
  pull f t := typeMap f t
  reduce {α _} h := reduceType α.2 h
  pull_refl := typeMap_refl
  pull_trans f g r q h := (typeMap_trans g f r q h).symm
  reduce_refl {α _} := reduceType_refl α.2
  reduce_trans {α β _} hαβ hβγ {_} r := reduceType_trans α.2 β.2 hαβ hβγ r
  pull_reduce {α _} h {_ _} f q := typeMap_reduceType_comm α.2 h f q

@[simp] theorem knightTower_pull {α : LimitStage} {m n : ℕ} (f : Fin m ↪ Fin n) (t : S α.1 n) :
    knightTower.pull f t = typeMap f t := rfl

/-- The Knight tower has **permutation-total pull**: the range of a permutation is the whole
domain, which is a visible face of every plan (`IsPlan.domain_mem`).  Hence, for Knight
realizations, generic covering and the paper's initial-segment covering (Def. 3.2.1(3)) agree
under visible-face (a fortiori exact) consistency:
`TypeTower.Realization.IsCovering.toInitialSegment knightTower_permTotal` and
`IsInitialSegmentCovering.isCovering` (#38). -/
theorem knightTower_permTotal : knightTower.PermTotal := by
  intro α n σ q
  refine typeMap_isSome_of_mem _ q ?_
  rw [Equiv.coe_toEmbedding, Finset.image_univ_equiv]
  exact q.scheme.scheme.isPlan.domain_mem

end VaughtConjecture.Knight
