/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedIteration
public import VaughtConjecture.Knight.PaddedSourceTable

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedNativeRows

open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : BuildContext A B C R m n J)

local notation "P" => G.tower
local notation "Fld" => Field G.I.right.scheme G.I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue G.X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields G.X 1)

abbrev ceiling {I : WholeDonorBoundary.Input A B C R m (n + 1) J} (t : ℕ) : ExtOrd :=
  CanonicalFieldLayer.ceiling (t + 2) (Field I.right.scheme I.left.scheme)

abbrev ladder (v : Pt) := (P).baseMap (RelativeLadderLayer.added G.I.boundary G.pos v)

theorem ladder_index (v : Pt) : (P).carrier.cell (ladder G v) = (A, 1) :=
  ((P).base_index _).trans (RelativeLadderLayer.added_index G.I.boundary _ v)

theorem anchor_ranks (a : Catalogue G.X (G.depth + 2)) (f : Fld) :
    ranks₁ ((P).baseAnchor a) f = LadderScalarRendering.fieldRank (fields G.X (G.depth + 2) a) f :=
  (P).anchor_ranks a f

theorem source_ladder (a : Catalogue G.X (G.depth + 2)) (v : Pt) :
    (P).source a (ladder G v) = SupportLadderRows.image ranks₁ ((P).baseAnchor a)
      (LadderScalarRendering.level (LadderScalarRendering.values (fields G.X (G.depth + 2) a))
        (ceiling (I := G.I) G.depth)) v :=
  ((P).source_base a _).trans
    (RelativeLadderLayer.renderWith_added G.I.boundary _ (field G.I) (fields G.X 1) _ _ _ v)

/-- Complete fields, including hidden/future fields, are actual shadow maxima. -/
theorem source_shadow_sup (a : Catalogue G.X (G.depth + 2)) (f : Fld) :
    (Finset.univ : Finset (Catalogue G.X 1)).sup (fun b =>
      (P).source a (ladder G (SupportLadderRows.shadow b f))) = fields G.X (G.depth + 2) a f := by
  classical
  have he := SupportLadderRows.readout_image (H := RelativeLadderLayer.rungs (X := Fld))
    (fun b f => le_of_lt (RelativeLadderLayer.rank_bound (fields G.X 1) b f))
    ((P).baseAnchor a)
    (LadderScalarRendering.level_mono (LadderScalarRendering.values_bound (anchor_bound G.X a))) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue G.X 1) = (inferInstance : Fintype (Catalogue G.X 1))
    from Subsingleton.elim _ _] at he
  simp only [source_ladder]
  rw [he, anchor_ranks G a f, LadderScalarRendering.field_readback]

theorem source_spare (a : Catalogue G.X (G.depth + 2)) :
    (P).source a (ladder G (SupportLadderRows.leaf (Nat.succ_pos _) ((P).baseAnchor a))) =
      ceiling (I := G.I) G.depth :=
  ((P).source_base a _).trans
    (RelativeLadderLayer.renderWith_leaf G.I.boundary _ (field G.I) (fields G.X 1) _ _ _)

end

end VaughtConjecture.Knight.GrowthPaddedNativeRows
