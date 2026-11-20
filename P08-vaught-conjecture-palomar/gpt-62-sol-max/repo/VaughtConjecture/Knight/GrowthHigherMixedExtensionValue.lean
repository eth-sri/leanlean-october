/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedRestriction

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

local notation "Pt" => RelativeLadderLayer.Point
  (X := Field G.I.right.scheme G.I.left.scheme) (Q := Catalogue G.X 1)

theorem original_injective : Function.Injective (original G) :=
  ((P).base_mono.comp
    (SourceLayerCarrier.old_order G.I.boundary Pt 1 Nat.one_pos G.pos)).injective

variable {G} (W : Cut G)
  (p : CellScheme.below (carrier G) W.index → ExtOrd)

def boundaryValue (d : Cell G.I.boundary) : ExtOrd :=
  min (shadowSup W p (GrowthOrderedBase.field G.I d))
    (height W p (G.I.boundary.grade d))

def nativeValue (c : Cell (P).carrier) : ExtOrd := by
  classical
  exact if ho : ∃ d, c = original G d then
    boundaryValue W p ho.choose
  else if ha : (P).carrier.scope c = A ∧ (P).carrier.grade c ≤ W.grade then
    p (place W c ha.1 ha.2)
  else ⊥

theorem native_original (d : Cell G.I.boundary) :
    nativeValue W p (original G d) =
      boundaryValue W p d := by
  classical
  unfold nativeValue
  split_ifs with ho
  · exact congrArg (boundaryValue W p)
      (original_injective G ho.choose_spec.symm)
  all_goals solve_by_elim

theorem native_full (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ W.grade) :
    nativeValue W p c =
      p (place W c hc hg) := by
  classical
  unfold nativeValue
  split_ifs with ho ha
  · obtain ⟨d, rfl⟩ := ho
    exact (GrowthOrderedBase.proper G.I G.leftProper G.rightProper d
      ((congrArg Prod.fst (original_index G d)).symm.trans hc)).elim
  all_goals simp_all

def value {V : Finset ι} (z : (D).below (V, W.grade)) : ExtOrd :=
  nativeValue W p (erase G z.1)

theorem literal (hp : RespectsSemanticsBelow Rows W.index p)
    {V : Finset ι} (hUV : W.scope ⊆ V) (z : (D).below W.index) :
    value W p
      (CellScheme.below.mono (show GradedLe W.index (V, W.grade) from ⟨hUV, le_rfl⟩) z) = p z := by
  change nativeValue W p
    (erase G z.1) = p z
  rcases original_or_full G (erase G z.1) with
      ⟨d, hd⟩ | hz
  · rw [hd, native_original]
    exact (projection_readback W hp z d hd).symm
  · rw [native_full W p _ hz
      ((ScopeReplicationCarrier.erase_grade (GrowthReplicatedRows.frame P) z.1).le.trans z.2.2)]
    exact (GrowthReplicatedRows.copy_eq P hp z _
      (z.2.1.trans (congrArg Prod.fst
        (place_index W _ _ _)).symm.le)
      (erase_place W _ _ _).symm).symm

end

end VaughtConjecture.Knight.GrowthHigherMixed
