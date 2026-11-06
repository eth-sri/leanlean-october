
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedSuccessor
import VaughtConjecture.Knight.RelativeLadderTableDecode

/-! # Incoming rendering on the installed padded LOW successor

A proper state admitted at a cutoff at least two is normalized downward into
the fixed grade-two catalogue, rendered by its actual source row, and decoded
with fixed outer grid and ceiling. The entire retained padded table is read
back directly. Long old rows are not subjected to a short-source composition
assumption; only the native grade-two leaf rows use that composition theorem.

This is a renderer contract on the unchanged first successor, not a lifting
theorem or an assertion that independent construction grades restrict equally.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedRendering
open     LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedSuccessor SourcePrefixRows SharpWitnessComposition
open PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "carrier₀" => carrier I F hroot hA hB hC

local notation "input₀" => input I F hroot hA hB hC

/-- Native upper sources are short through two, even though the retained
grade-one semantic rows include long tips. -/
theorem source_short a d :
    Short 2 (source I F hroot hA hB hC a d) := by
  let J := input₀
  rcases LowOnlyPaddedSuccessor.cell_cases d with ⟨x, rfl⟩ | ⟨b, rfl⟩
  · change Short 2 (J.source a (J.old x))
    rw [J.source_old]
    rcases RelativeLadderLayer.renderWith_supported I.boundary J.one (field I)
        (F.fields 1) x with hz | ⟨f, hf⟩ | hh
    · exact Or.inl hz
    · exact (congrArg (Short 2) hf).mpr (LowOnlyRecursiveCharts.anchor_short F a f)
    · exact (congrArg (Short 2) hh).mpr
        (CanonicalFieldLayer.grid_short (sourceGrid_endpoint le_rfl))
  · rw [source_leaf]
    exact CanonicalFieldLayer.grid_short
      (cut_mem (sourceGrid_bot) _ _)

variable {j : ℕ} (hj : 2 ≤ j) (S : State I.left I.right)
  (hS : F.Admissible j S) (hp : AvoidsValue S.profile ⊤)

def anchor :=
  LowOnlyRecursiveCoverage.normalizedAnchor F (by decide) hj hS hp

local notation "anchor₀" => anchor I F hj S hS hp

theorem anchor_fields : F.fields 2 (anchor₀) =
    PairedSlotEncoding.normalize 2 S.profile :=
  LowOnlyRecursiveCoverage.normalizedAnchor_fields F (by decide) hj hS hp

theorem birth_ranks d :
    RelativeLadderLayer.ranks (F.fields 1) (baseAnchor F (anchor₀)) d =
      LadderScalarRendering.fieldRank S.profile d := by
  rw [baseAnchor_ranks, anchor_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize hp

local notation "decode₀" => PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile)

def render G H d :=
  decode₀ G H
    (source I F hroot hA hB hC (anchor₀) d)

def baseRender (H : ExtOrd) : Cell (input₀).lower → ExtOrd :=
  RelativeLadderLayer.renderWith I.boundary (input₀).one
    (field I) (F.fields 1) (baseAnchor F (anchor₀)) S.profile H

variable {G : Finset ExtOrd} {H : ExtOrd}

local notation "old₀" => old I F hroot hA hB hC

local notation "render₀" => render I F hroot hA hB hC hj S hS hp

local notation "SelfVis₀" => SelfVis 2 H

local notation "BoundedBy₀" => BoundedBy S.profile H

theorem render_old (hG : VisibleOn 2 G) (hH : SelfVis₀)
    (hb : BoundedBy₀) d :
    render₀ G H (old₀ d) =
      baseRender I F hroot hA hB hC hj S hS hp H d := by
  let J := input₀
  have he := congrArg (decode₀ G H)
    (J.source_old (anchor₀) d)
  refine he.trans ?_
  change decode₀ G H
    (RelativeLadderLayer.renderWith I.boundary J.one (field I) (F.fields 1)
      (baseAnchor F (anchor₀)) (F.fields 2 (anchor₀)) J.ceiling d) = _
  rw [anchor_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized _ hp hG hH (decode_reserved_ceiling hH hb) d

theorem baseRender_lawful (hH : SelfVis₀) (hb : BoundedBy₀) :
    RespectsSemanticsBelow (input₀).lowerRows (A, j)
      (fun d => baseRender I F hroot hA hB hC hj S hS hp H d.1) :=
  RelativeLadderLayer.renderWith_respects I.boundary I.rows
    (input₀).one (field I) (F.fields 1) (proper hB hC)
    _ _ (birth_ranks I F hj S hS hp) hb
    (LowOnlyRecursiveCharts.profile_visible_one F (by omega) hS)
    (hH.mono (by decide)) (LowOnlyOrderedSources.boundary_lawful_at I F hroot hS)

theorem render_below_old (hG : VisibleOn 2 G) (hH : SelfVis₀)
    (hb : BoundedBy₀) c
    (hc : GradedLe ((input₀).lower.cell c) (A, j)) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC)
      ((carrier₀).cell (old₀ c))
      (fun d => render₀ G H d.1) := by
  let J := input₀
  apply (WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
    (SeparatedSourceLayerCarrier.old_not_full _ _ J.separation)).mpr
  apply (SeparatedSourceLayerCarrier.base_respects_iff J.separation J.lowerRows c _).mpr
  have hl := (baseRender_lawful I F hroot hA hB hC hj S hS hp hH hb).mono hc
  simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
    render_old I F hroot hA hB hC hj S hS hp hG hH hb, CellScheme.below.mono] using hl

theorem render_lawful_two (hG : VisibleOn 2 G) (hH : SelfVis₀)
    (hb : BoundedBy₀) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)
      (fun d => render I F hroot hA hB hC hj S hS hp G H d.1) := by
  let J := input I F hroot hA hB hC
  let a := anchor I F hj S hS hp
  have hr := source_lawful I F hroot hA hB hC a
  have hν := PairedSlotDecoder.decode_witness (S := PairedSlotEncoding.values S.profile) hG hH
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have hd : (carrier I F hroot hA hB hC).grade d.1 ≤ 2 := d.2.2
    have he := hν.clause5 (source I F hroot hA hB hC a d.1)
      ((carrier I F hroot hA hB hC).grade d.1)
      (le_top.trans_eq (gTop_of_le hd).symm)
      ((carrier I F hroot hA hB hC).grade d.1) le_rfl
    exact (congrArg (decode₀ G H) (hr.orderly d)).trans he
  · intro c
    rcases LowOnlyPaddedSuccessor.cell_cases c.1 with
      ⟨x, hx⟩ | ⟨b, hc⟩
    · have hxc : GradedLe (J.lower.cell x) (A, j) := by
        have hg  := by
          simpa only [hx, CellScheme.grade, SourceLayerCarrier.cell_toCell,
            SourceLayerCarrier.index] using c.2.2
        exact ⟨J.lower.scope_subset x, hg.trans hj⟩
      have hl := render_below_old I F hroot hA hB hC hj S hS hp hG hH hb x hxc
      rcases c with ⟨c, h⟩
      dsimp only at hx
      subst c
      exact hl.locality ⟨old I F hroot hA hB hC x, GradedLe.refl _⟩
    · rcases c with ⟨c, h⟩
      dsimp only at hc
      subst c
      exact map_capped_locality
        (grade := fun d : (carrier I F hroot hA hB hC).below
          ((carrier I F hroot hA hB hC).cell (leaf I F hroot hA hB hC b)) =>
          (carrier I F hroot hA hB hC).grade d.1)
        (E := (rows I F hroot hA hB hC).E (leaf I F hroot hA hB hC b))
        (c := (⟨leaf I F hroot hA hB hC b, GradedLe.refl _⟩ :
          (carrier I F hroot hA hB hC).below
            ((carrier I F hroot hA hB hC).cell (leaf I F hroot hA hB hC b))))
        (p := fun d => source I F hroot hA hB hC a d.1)
        (fun d => d.2.2)
        (by simp only [CellScheme.grade, leaf_index, le_refl])
        (fun d => by
          simpa only [CellScheme.grade, leaf_index] using
            (congrArg (Short 2) (leaf_row I F hroot hA hB hC b d)).mpr
              (source_short I F hroot hA hB hC b d.1))
        (hr.orderly ⟨leaf I F hroot hA hB hC b, h⟩).symm
        (hr.locality ⟨leaf I F hroot hA hB hC b, h⟩) hν
  · intro c t hs hg
    obtain ⟨w, hw, hle⟩ := hr.availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩

/-- The original owners above grade two are read literally and use their own
lawful domains. No upper-grade commutation of the grade-two decoder is needed. -/
theorem render_lawful (hG : VisibleOn 2 G) (hH : SelfVis₀)
    (hb : BoundedBy₀) :
    RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, j)
      (fun d => render₀ G H d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  rcases LowOnlyPaddedSuccessor.cell_cases c.1 with
    ⟨x, hx⟩ | ⟨a, ha⟩
  · have hxc : GradedLe ((input₀).lower.cell x) (A, j) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    rcases c with ⟨c, hc⟩
    dsimp  at hx
    subst c
    exact render_below_old I F hroot hA hB hC hj S hS hp hG hH hb x hxc
  · have he : (carrier₀).cell c.1 = (A, 2) :=
      (congrArg (carrier₀).cell ha).trans (leaf_index a)
    exact GradeCutLayerRows.cast_respects he.symm
      (render_lawful_two I F hroot hA hB hC hj S hS hp hG hH hb)

theorem render_bound (hH : SelfVis₀) (hb : BoundedBy₀)
    d :
    render₀ G H d ≤ H := by
  apply PairedSlotDecoder.decode_le hH
  intro v hv
  obtain ⟨x, hx⟩ := PairedSlotEncoding.mem_values.mp hv
  simpa only [hx] using hb x

theorem render_supported {l} (hl : 2 ≤ l) (hH : H ∈ G)
    d :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile
      (render₀ G H d) :=
  PairedSlotDecoder.decode_supported hl hH _

/-- Whole-coordinate agreement at fixed outer parameters, not equality of
independently rendered sections at different construction grades. -/
theorem render_prefix {T} (hT : F.Admissible j T)
    (ht : AvoidsValue T.profile ⊤) {h}
    (hG : VisibleOn 2 G) (hH : SelfVis₀)
    (hh : h ∈ G) (hhH : h ≤ H) (hag : Agree S.profile T.profile h) :
    Agree (render₀ G H)
      (render I F hroot hA hB hC hj T hT ht G H) h := by
  obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ :=
    exists_common_cut hG hH hH hh hhH hhH hp ht hag
  have he' : Agree (F.fields 2 (anchor₀))
      (F.fields 2 (anchor I F hj T hT ht)) e := by
    rw [anchor_fields, anchor_fields]
    exact he
  have hs := source_prefix I F hroot hA hB hC
    (anchor₀) (anchor I F hj T hT ht) heG he'
  exact Agree.decode hs (PairedSlotDecoder.decode_witness hG hH).mono
    (PairedSlotDecoder.decode_witness hG hH).mono hpe hqe (fun _ _ => hcompare _)

theorem render_ceiling (hH : SelfVis₀) (hb : BoundedBy₀) :
    render₀ G H
      (leaf I F hroot hA hB hC (anchor₀)) = H := by
  unfold render
  rw [source_ceiling]
  exact decode_reserved_ceiling hH hb

/-- The retained padded base has its own actual full-scope ceiling occurrence. -/
theorem render_base_ceiling (hG : VisibleOn 2 G) (hH : SelfVis₀)
    (hb : BoundedBy₀) :
    ∃ c ,
      (carrier₀).cell c = (A, 1) ∧
      render₀ G H c = H := by
  let J := input₀
  let a := baseAnchor F (anchor₀)
  let v := SupportLadderRows.leaf
    (H := RelativeLadderLayer.rungs (X := Field I.left I.right))
    (X := Field I.left I.right) (by unfold RelativeLadderLayer.rungs; omega) a
  let c := RelativeLadderLayer.added I.boundary J.one v
  refine ⟨old₀ c, ?_, ?_⟩
  · exact (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans
      (RelativeLadderLayer.added_index I.boundary J.one v)
  · rw [render_old I F hroot hA hB hC hj S hS hp hG hH hb]
    change LadderScalarRendering.level (LadderScalarRendering.values S.profile) H
      (RelativeLadderLayer.rankIndex I.boundary J.one (field I) (F.fields 1) a c) = H
    rw [RelativeLadderLayer.rankIndex_added, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl]
    exact ite_eq_left (by
      have := LadderScalarRendering.values_card_le S.profile
      unfold RelativeLadderLayer.rungs
      omega)

