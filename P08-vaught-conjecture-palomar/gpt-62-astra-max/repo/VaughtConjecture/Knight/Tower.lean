/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.Basic
public import VaughtConjecture.Knight.Reduction

/-! # The Knight instance of the type tower, over limit stages

New here (no Knight-VC counterpart; Knight-VC states `typeMap_id`, `typeMap_comp`,
`typeMap_truncateType_comm` but has no abstract tower).  Knight's stage types `S α n`
(`Knight.Type`: the paper's `S^α_n` in record form — labels strictly bounded, the associated
semantics of the scheme, faithful respect) with horizontal restriction `typeMap` (`pull`) and
vertical reduction `reduceType` (`reduce`, `Knight.Reduction`: labels truncated, semantics
fixed) form a `TypeTower` over the **limit stages** `LimitStage` (Def. 3.1.1: "α a limit
ordinal"; the faithful transport of respect under reduction, `RespectsSemantics.truncate`, needs
`Order.IsSuccLimit α`, #89).  This is the graduation test of experiment A4 (`docs/DESIGN.md`
§4, §6): the instance is the five laws of `Knight.Type`/`Knight.Reduction`, nothing more, and it
is now the **paper-faithful** tower (#88 (2/2)): the legacy layer (stage-bounded rows truncated
under reduction, Knight-VC's respect predicate) has been retired. -/

@[expose] public section

namespace VaughtConjecture.Knight

/-- The **limit stages**: the limit ordinals, the index set of Knight's type spaces
(Def. 3.1.1), ordered as ordinals. -/
def LimitStage : Type 1 := {α : Ordinal.{0} // Order.IsSuccLimit α}

namespace LimitStage

noncomputable instance : LinearOrder LimitStage :=
  inferInstanceAs (LinearOrder {α : Ordinal.{0} // Order.IsSuccLimit α})

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
  reduce_refl {α _} := fun t => StageType.ext rfl (heq_of_eq (funext fun d => Value.truncExt_id_of_bound (t.label_bound d)))
  reduce_trans {α β _} hαβ hβγ {_} r := StageType.ext rfl (heq_of_eq (funext fun d => Value.truncExt_compose hαβ (r.label d)))
  pull_reduce {α _} h {_ _} f q := typeMap_reduceType_comm α.2 h f q

@[simp] theorem knightTower_pull {α : LimitStage} {m n : ℕ} (f : Fin m ↪ Fin n) (t : S α.1 n) :
    knightTower.pull f t = typeMap f t := rfl

end VaughtConjecture.Knight
