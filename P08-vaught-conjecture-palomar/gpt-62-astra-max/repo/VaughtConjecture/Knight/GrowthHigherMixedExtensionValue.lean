/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthHigherMixedRestriction

/-! # Concrete mixed extension values on a fixed final growth carrier

Originals use the lawful grade-dependent boundary projection. Every relevant
auxiliary uses its own actual prescribed copy; no auxiliary is reconstructed
from complete-field readouts. Values above the observed cutoff are irrelevant.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower frame t ht
local notation "D" => carrier frame t ht
local notation "Rows" => rows frame t ht
local notation "Pt" => RelativeLadderLayer.Point
  

theorem original_injective : Function.Injective (original frame t ht) :=
  ((P).base_mono.comp
    (SourceLayerCarrier.old_order I.boundary Pt 1 Nat.one_pos (by omega))).injective

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  (p : CellScheme.below (carrier frame t ht) (U, j) → ExtOrd)

def boundaryValue (d : Cell I.boundary) : ExtOrd :=
  min (shadowSup frame t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
    (height frame t ht U j p (I.boundary.grade d))

def nativeValue (c : Cell (P).carrier) : ExtOrd := by
  classical
  exact if ho : ∃ d, c = original frame t ht d then
    boundaryValue frame t ht U hU hm j hj hj0 p ho.choose
  else if ha : (P).carrier.scope c = A ∧ (P).carrier.grade c ≤ j then
    p (place frame t ht U hU hm j hj c ha.1 ha.2)
  else ⊥

theorem native_original (d : Cell I.boundary) :
    nativeValue frame t ht U hU hm j hj hj0 p (original frame t ht d) =
      boundaryValue frame t ht U hU hm j hj hj0 p d := by
  classical
  unfold nativeValue
  split_ifs with ho
  · exact congrArg (boundaryValue frame t ht U hU hm j hj hj0 p)
      (original_injective frame t ht ho.choose_spec.symm)
  all_goals simp_all

theorem native_full (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) :
    nativeValue frame t ht U hU hm j hj hj0 p c =
      p (place frame t ht U hU hm j hj c hc hg) := by
  classical
  unfold nativeValue
  split_ifs with ho ha
  · obtain ⟨d, rfl⟩ := ho
    exact (GrowthOrderedBase.proper I frame.leftProper frame.rightProper d
      ((congrArg Prod.fst (original_index frame t ht d)).symm.trans hc)).elim
  · rfl
  simp_all

def value {V : Finset ι} (z : (D).below (V, j)) : ExtOrd :=
  nativeValue frame t ht U hU hm j hj hj0 p (erase frame t ht z.1)

theorem literal (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    {V : Finset ι} (hUV : U ⊆ V) (z : (D).below (U, j)) :
    value frame t ht U hU hm j hj hj0 p
      (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) z) = p z := by
  change nativeValue frame t ht U hU hm j hj hj0 p
    (erase frame t ht z.1) = p z
  rcases original_or_full frame t ht (erase frame t ht z.1) with
      ⟨d, hd⟩ | hz
  · rw [hd, native_original]
    exact (projection_readback frame t ht U hU hm j hj hj0 hp hjt z d hd).symm
  · rw [native_full frame t ht U hU hm j hj hj0 p _ hz
      ((ScopeReplicationCarrier.erase_grade (P).carrier B C z.1).le.trans z.2.2)]
    exact (GrowthReplicatedRows.copy_eq P hp z _
      (z.2.1.trans (congrArg Prod.fst
        (place_index frame t ht U hU hm j hj _ _ _)).symm.le)
      (erase_place frame t ht U hU hm j hj _ _ _).symm).symm

end
end VaughtConjecture.Knight.GrowthHigherMixed
