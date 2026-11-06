/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ScopeReplicationCharts

/-! # The auxiliary part of mixed extension, with individual cap receipts

At each target auxiliary use the prescription's actual copy of the same
prototype at the prescribed mixed scope. Literal retention follows from
nested copy equality. For cap retention, compare both occurrences to their
common target-scope copy in the actual ambient. No field readout determines
an unused rung's value, and no hidden-original lawfulness is assumed.
This is the auxiliary part only, not a theorem of whole extension lawfulness.
-/

namespace VaughtConjecture.Knight.ScopeReplicationAuxExtension
open     ScopeReplicationCarrier ScopeReplicationSemantics
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c , D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

local notation "scheme₀" => scheme D B C

def replica {U} {j} (hU : U ∈ D.plan)
    (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    c (hc : D.scope c = A) (hg : D.grade c ≤ j) :
    (scheme₀).below (U, j) :=
  ⟨atScope D B C U hU hm c hc (hg.trans hj),
    (atScope_index D B C U hU hm c hc (hg.trans hj)) ▸ ⟨le_rfl, hg⟩⟩

local notation "replica₀" => replica D B C

theorem replica_index {U j} (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c) (hc) (hg) :
    (scheme₀).cell (replica₀ hU hm hj c hc hg).1 = (U, D.grade c) :=
  atScope_index D B C U hU hm c hc (hg.trans hj)

local notation "erase₀" => erase D B C

theorem erase_replica {U j} (hU : U ∈ D.plan) (hm : U = A ∨ Mixed B C U) (hj : j ≤ U.card)
    (c) (hc) (hg) : erase₀ (replica₀ hU hm hj c hc hg).1 = c :=
  erase_atScope D B C U hU hm c hc (hg.trans hj)

variable {U V : Finset ι} {j : ℕ}
  (hU : U ∈ D.plan) (hmU : U = A ∨ Mixed B C U) (hjU : j ≤ U.card)

def value (p : (scheme₀).below (U, j) → ExtOrd)
    (z : (scheme₀).below (V, j)) (hz : D.scope (erase₀ z.1) = A) :=
  p (replica₀ hU hmU hjU (erase₀ z.1) hz
    ((erase_grade D B C z.1).le.trans z.2.2))

/-- Any auxiliary under the target equals its own target-scope copy, in an
arbitrary lawful target-local section. -/
theorem eq_target_copy (hV : V ∈ D.plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
    {q}
    (hq : RespectsSemanticsBelow (rows hcover sem) (V, j) q)
    (z : (scheme₀).below (V, j)) (hz : D.scope (erase₀ z.1) = A) :
    q z = q (replica₀ hV hmV hjV (erase₀ z.1) hz
      ((erase_grade D B C z.1).le.trans z.2.2)) :=
  copy_eq hq
    (by
      change (scheme₀).scope z.1 ⊆ ((scheme₀).cell _).1
      rw [replica_index]; exact z.2.1)
    (erase_replica D B C hV hmV hjV _ _ _).symm

local notation "scheme₀₀" => scheme D B C

/-- Every auxiliary keeps its own old cap, including unused rungs and tips.
Only the actual prescription's cap equations and target lawfulness are used. -/
theorem cap (hV : V ∈ D.plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
    (hUV : U ⊆ V) (p : (scheme₀₀).below (U, j) → ExtOrd)
    {q : (scheme₀₀).below (V, j) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows hcover sem) (V, j) q)
    {γ : ExtOrd} (hag : ∀ d, min (q (CellScheme.below.mono
      (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) d)) γ = min (p d) γ)
    (z : (scheme₀₀).below (V, j)) (hz : D.scope (erase D B C z.1) = A) :
    min (value D B C hU hmU hjU p z hz) γ = min (q z) γ := by 
  let core2 := erase D B C z.1
  let core1 := erase_grade D B C z.1
  let u := replica₀ hU hmU hjU core2 hz
    (core1.le.trans z.2.2)
  let v := replica₀ hV hmV hjV core2 hz
    (core1.le.trans z.2.2)
  let u' := CellScheme.below.mono  (show GradedLe (U, j) (V, j)
    from ⟨hUV, le_rfl⟩) u
  have huq : q u' = q v := copy_eq hq
    (by
      change ((scheme₀₀).cell u.1).1 ⊆ ((scheme₀₀).cell v.1).1
      rw [replica_index, replica_index]; exact hUV)
    ((erase_replica D B C hU hmU hjU core2 hz
      (core1.le.trans z.2.2)).trans
      (erase_replica D B C hV hmV hjV core2 hz
        (core1.le.trans z.2.2)).symm)
  have hzq  := eq_target_copy D B C hcover sem hV hmV hjV hq z hz
  exact (hag u).symm.trans (congrArg (fun x => min x γ) (huq.trans hzq.symm))

