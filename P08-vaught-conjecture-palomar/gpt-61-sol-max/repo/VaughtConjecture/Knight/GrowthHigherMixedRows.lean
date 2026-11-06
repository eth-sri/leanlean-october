/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
import VaughtConjecture.Knight.GrowthReplicatedRows
import VaughtConjecture.Knight.ScopeReplicationCharts
import VaughtConjecture.Knight.GrowthLeafRecognition

/-! # Higher-owner columns on the actual replicated growth carrier

The final build and observation cutoff are independent. Every inherited higher
owner has its own birth provenance, and the entire padded base has named copies
at the observed mixed scope. No lawful extension is used to obtain these rows.
-/

namespace VaughtConjecture.Knight.GrowthHigherMixed
open     Growth 
open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)

abbrev tower := build I X T hA hB hC t ht
local notation "tower₀" => tower I X T hA hB hC t ht

abbrev carrier := GrowthReplicatedRows.carrier (tower₀)
abbrev rows := GrowthReplicatedRows.rows (tower₀)
abbrev erase := GrowthReplicatedRows.erase (tower₀)

local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)

def original d :=
  (P).baseMap (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)

variable {I X t} in
theorem original_index d : (P).carrier.cell
    (original I X T hA hB hC t ht d) = I.boundary.cell d :=
  ((P).base_index _).trans (RelativeLadderLayer.old_index d)

variable {I X T hA hB hC t ht} in
abbrev ladder (v : Pt) : Cell (P).carrier :=
  GrowthPaddedNativeRows.ladder I X T hA hB hC t ht v

variable {I X t} in
theorem ladder_index v : (P).carrier.cell
    (ladder v) = (A, 1) :=
  GrowthPaddedNativeRows.ladder_index I X T hA hB hC t ht v

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card)

def place c (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ j) : (D).below (U, j) :=
  ⟨ScopeReplicationCarrier.atScope (P).carrier B C U
      (by rw [GrowthPaddedIteration.build_plan]; exact hU) hm c hc (hg.trans hj),
    by rw [ScopeReplicationCarrier.atScope_index]; exact ⟨le_rfl, hg⟩⟩

local notation "place₀" => place I X T hA hB hC t ht U hU hm j hj

variable {I X T hA hB hC t ht U j} in
theorem place_index (c) (hc) (hg) : (D).cell
    (place₀ c hc hg).1 = (U, (P).carrier.grade c) :=
  ScopeReplicationCarrier.atScope_index (P).carrier B C U _ hm c hc (hg.trans hj)

variable {I X T hA hB hC t ht U j} in
theorem erase_place (c) (hc) (hg) : erase I X T hA hB hC t ht
    (place₀ c hc hg).1 = c :=
  ScopeReplicationCarrier.erase_atScope (P).carrier B C U _ hm c hc (hg.trans hj)

variable (hj0 : 1 ≤ j)

def ladderAt v :=
  place₀ (ladder v)
    (congrArg Prod.fst (ladder_index T hA hB hC ht v))
    ((congrArg Prod.snd (ladder_index T hA hB hC ht v)).le.trans hj0)

local notation "ladderAt₀" => ladderAt I X T hA hB hC t ht U hU hm j hj hj0

theorem ladderAt_index v : (D).cell
    (ladderAt₀ v).1 = (U, 1) :=
  (place_index hU hm hj _ _ _).trans
    (congrArg (fun k => (U, k)) (congrArg Prod.snd (ladder_index T hA hB hC ht v)))

theorem erase_ladderAt v : erase I X T hA hB hC t ht
    (ladderAt₀ v).1 =
      ladder v :=
  erase_place hU hm hj _ _ _

def shadowSup (p : (D).below (U, j) → ExtOrd) (f : Fld) :=
  Finset.univ.sup fun a =>
    p (ladderAt₀ (shadow a f))

