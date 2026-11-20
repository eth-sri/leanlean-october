/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedOwnerProvenance
public import VaughtConjecture.Knight.GrowthReplicatedRows
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.GrowthLeafRecognition

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

abbrev carrier := GrowthReplicatedRows.carrier (G.tower)

abbrev rows := GrowthReplicatedRows.rows (G.tower)

abbrev erase := GrowthReplicatedRows.erase (G.tower)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Fld" => Field G.I.right.scheme G.I.left.scheme

local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue G.X 1)

def original (d : Cell G.I.boundary) : Cell (P).carrier :=
  (P).baseMap (RelativeLadderLayer.old G.I.boundary G.pos d)

theorem original_index (d : Cell G.I.boundary) : (P).carrier.cell
    (original G d) = G.I.boundary.cell d :=
  ((P).base_index _).trans (RelativeLadderLayer.old_index _ _ d)

abbrev ladder (v : Pt) : Cell (P).carrier :=
  GrowthPaddedNativeRows.ladder G v

theorem ladder_index (v : Pt) : (P).carrier.cell
    (ladder G v) = (A, 1) :=
  GrowthPaddedNativeRows.ladder_index G v

/-- A positive cutoff on an installed mixed scope of the replicated tower. -/
structure Cut (G : GrowthPaddedIteration.BuildContext A B C R m n J) where
  scope : Finset ι
  grade : ℕ
  member : scope ∈ R
  mixed : scope = A ∨ ScopeReplicationCarrier.Mixed B C scope
  card : grade ≤ scope.card
  pos : 1 ≤ grade
  installed : grade ≤ G.depth + 2

namespace Cut

variable {G} (W : Cut G)

abbrev index : Finset ι × ℕ := (W.scope, W.grade)

theorem plan : W.scope ∈ (G.tower).carrier.plan := by
  rw [GrowthPaddedIteration.build_plan]
  exact W.member

theorem gradeOne : GradedLe (W.scope, 1) W.index := ⟨le_rfl, W.pos⟩

def one : Cut G :=
  ⟨W.scope, 1, W.member, W.mixed, W.pos.trans W.card, le_rfl, by omega⟩

def raise (V : Finset ι) (hV : V ∈ R) (hm : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
    (h : W.scope ⊆ V) : Cut G :=
  ⟨V, W.grade, hV, hm, W.card.trans (Finset.card_le_card h), W.pos, W.installed⟩

end Cut

variable {G} (W : Cut G)

def place (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ W.grade) : (D).below W.index :=
  ScopeReplicationCarrier.replica (GrowthReplicatedRows.frame P) W.plan W.mixed W.card c hc hg

theorem place_index (c) (hc) (hg) : (D).cell
    (place W c hc hg).1 = (W.scope, (P).carrier.grade c) :=
  ScopeReplicationCarrier.replica_index (GrowthReplicatedRows.frame P) W.plan W.mixed W.card _ _ _

theorem erase_place (c) (hc) (hg) : erase G
    (place W c hc hg).1 = c :=
  ScopeReplicationCarrier.erase_replica (GrowthReplicatedRows.frame P) W.plan W.mixed W.card _ _ _

def ladderAt (v : Pt) : (D).below W.index :=
  place W (ladder G v)
    (congrArg Prod.fst (ladder_index G v))
    ((congrArg Prod.snd (ladder_index G v)).le.trans W.pos)

theorem ladderAt_index (v : Pt) : (D).cell
    (ladderAt W v).1 = (W.scope, 1) :=
  (place_index W _ _ _).trans
    (congrArg (fun k => (W.scope, k)) (congrArg Prod.snd (ladder_index G v)))

theorem erase_ladderAt (v : Pt) : erase G
    (ladderAt W v).1 =
      ladder G v :=
  erase_place W _ _ _

def shadowSup (p : (D).below W.index → ExtOrd) (f : Fld) : ExtOrd :=
  Finset.univ.sup fun a : Catalogue G.X 1 =>
    p (ladderAt W (shadow a f))

end

end VaughtConjecture.Knight.GrowthHigherMixed
