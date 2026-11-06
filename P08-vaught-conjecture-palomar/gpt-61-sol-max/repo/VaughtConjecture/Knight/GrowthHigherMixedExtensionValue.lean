/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthHigherMixedRestriction

/-! # Concrete mixed extension values on a fixed final growth carrier

Originals use the lawful grade-dependent boundary projection. Every relevant
auxiliary uses its own actual prescribed copy; no auxiliary is reconstructed
from complete-field readouts. Values above the observed cutoff are irrelevant.
-/

namespace VaughtConjecture.Knight.GrowthHigherMixed
open     Growth 
open GrowthPaddedContract 
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht

local notation "original₀" => original I X T hA hB hC t ht

theorem original_injective : Function.Injective (original₀) :=
  ((P).base_mono.comp
    (SourceLayerCarrier.old_order)).injective

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  (p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd)

def boundaryValue d :=
  min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
    (height I X T hA hB hC t ht U j p (I.boundary.grade d))

local notation "boundaryValue₀" => boundaryValue I X T hA hB hC t ht U hU hm j hj hj0

def nativeValue c :=  if ho : ∃ d, c = original₀ d then
    boundaryValue₀ p ho.choose
  else if ha : (P).carrier.scope c = A ∧ (P).carrier.grade c ≤ j then
    p (place I X T hA hB hC t ht U hU hm j hj c ha.1 ha.2)
  else ⊥

local notation "nativeValue₀" => nativeValue I X T hA hB hC t ht U hU hm j hj hj0

theorem native_original d :
    nativeValue₀ p (original₀ d) =
      boundaryValue₀ p d := by
  
  unfold nativeValue
  split_ifs with ho
  · exact congrArg (boundaryValue₀ p)
      (original_injective I X T hA hB hC t ht ho.choose_spec.symm)
  all_goals exact (ho ⟨d, rfl⟩).elim

variable {I X T hA hB hC t ht U j} in
theorem native_full c (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) :
    nativeValue₀ p c =
      p (place I X T hA hB hC t ht U hU hm j hj c hc hg) := by
  
  unfold nativeValue
  split_ifs with ho ha
  · obtain ⟨d, rfl⟩ := ho
    exact (GrowthOrderedBase.proper hB hC d
      ((congrArg Prod.fst (original_index T hA hB hC ht d)).symm.trans hc)).elim
  · rfl
  · exact (ha ⟨hc, hg⟩).elim

local notation "erase₀" => erase I X T hA hB hC t ht

variable {I X T hA hB hC t ht U j} in
def value {V} (z : (D).below (V, j)) :=
  nativeValue₀ p (erase₀ z.1)

theorem literal (hp : RespectsSemanticsBelow Rows (U, j) p) (hjt : j ≤ t + 2)
    {V} (hUV : U ⊆ V) z :
    value hU hm hj hj0 p
      (CellScheme.below.mono (show GradedLe (U, j) (V, j) from ⟨hUV, le_rfl⟩) z) = p z := by
  change nativeValue₀ p
    (erase₀ z.1) = p z
  rcases original_or_full (erase₀ z.1) with
      ⟨d, hd⟩ | hz
  · rw [hd, native_original]
    exact (projection_readback hU hm hj hj0 hp hjt z d hd).symm
  · rw [native_full hU hm hj hj0 p _ hz
      ((ScopeReplicationCarrier.erase_grade (P).carrier B C z.1).le.trans z.2.2)]
    exact (GrowthReplicatedRows.copy_eq P hp
      (z.2.1.trans (congrArg Prod.fst
        (place_index hU hm hj _ _ _)).symm.le)
      (erase_place hU hm hj _ _ _).symm).symm

