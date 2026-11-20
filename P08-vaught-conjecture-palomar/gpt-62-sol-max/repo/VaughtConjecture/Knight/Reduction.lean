/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Type

@[expose] public section

namespace VaughtConjecture.Knight

open Value Transform

variable {α β γ : Ordinal.{0}} {m n : ℕ}

/-- **Vertical reduction** of a stage type from stage `β` to a limit stage `α ≤ β` (Knight,
Def. 3.1.2 / 5.1.1; Knight-VC `truncateType`, there for `α < β` and with the rows truncated
too): the same domain with its associated semantics (rows **fixed**), every label strictly
truncated at `α` (`truncExt α`; the strict bound of the result is `truncExt_bound`), respect
transported by `RespectsSemantics.truncate` (Lemma 3.1.3, reduction half).  This is the
`reduce` of the Knight `TypeTower` instance. -/
noncomputable def reduceType (hα : Order.IsSuccLimit α) (_h : α ≤ β) (t : S β n) : S α n where
  scheme := t.scheme
  label d := truncExt α (t.label d)
  label_bound d := truncExt_bound α (t.label d)
  respects := t.respects.truncate hα

/-- Reduction to the stage of the type is the identity: labels are already strictly bounded
at `α` (`< ofOrd α` or `⊤`), and `truncExt α` fixes them (`truncExt_id_of_bound`). -/
theorem reduceType_refl (hα : Order.IsSuccLimit α) (t : S α n) : reduceType hα le_rfl t = t :=
  StageType.ext rfl (heq_of_eq (funext fun d => truncExt_id_of_bound (t.label_bound d)))

/-- Reductions compose (`truncExt_compose`). -/
theorem reduceType_trans (hα : Order.IsSuccLimit α) (hβ : Order.IsSuccLimit β)
    (hαβ : α ≤ β) (hβγ : β ≤ γ) (t : S γ n) :
    reduceType hα hαβ (reduceType hβ hβγ t) = reduceType hα (hαβ.trans hβγ) t :=
  StageType.ext rfl (heq_of_eq (funext fun d => truncExt_compose hαβ (t.label d)))

/-- Reduction commutes with horizontal restriction, including definedness (Knight-VC
`typeMap_truncateType_comm`): reduction does not change the scheme, so a face is visible in
`reduceType hα h t` iff it is visible in `t`, and on a visible face the two operations
commute on the nose. -/
theorem typeMap_reduceType_comm (hα : Order.IsSuccLimit α) (h : α ≤ β) (f : Fin m ↪ Fin n)
    (t : S β n) : typeMap f (reduceType hα h t) = (typeMap f t).map (reduceType hα h) := by
  by_cases hr : Finset.univ.image f ∈ t.scheme.scheme.plan
  · rw [typeMap_eq_some f t hr, typeMap_eq_some f (reduceType hα h t) hr, Option.map_some]
    rfl
  · rw [typeMap_eq_none f t hr, typeMap_eq_none f (reduceType hα h t) hr, Option.map_none]

end VaughtConjecture.Knight
