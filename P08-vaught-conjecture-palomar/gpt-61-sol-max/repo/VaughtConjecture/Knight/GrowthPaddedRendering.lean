
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedSuccessor
import VaughtConjecture.Knight.RelativeLadderTableDecode

/-! # Rendering on the actual second growth layer

An admitted proper vector at any later cutoff is normalized downward into the
fixed grade-two catalogue. Its installed source is decoded once. Exact whole-
base table decoding handles long rung rows and original owners; only higher
auxiliary rows use short-source composition.

This recovers lawfulness at every present original grade, whole-coordinate
fixed-parameter agreement, support, and actual grade-one/two ceilings. It does
not identify independently rendered grades or supply arbitrary-ambient lifts.
The proof follows the checked padded LOW renderer on the growth catalogue.
-/

namespace VaughtConjecture.Knight.GrowthPaddedRendering
open    Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedSuccessor SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (attach : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "carrier₀" => carrier I X attach hA hB hC

local notation "input₀" => input I X attach hA hB hC

/-- Native upper sources are short through two, even though the retained
grade-one semantic rows include long tips. -/
theorem source_short a d :
    Short 2 (source I X attach hA hB hC a d) := by
  let J := input₀
  rcases GrowthPaddedSuccessor.cell_cases d with ⟨x, rfl⟩ | ⟨b, rfl⟩
  · change Short 2 (J.source a (J.old x))
    rw [J.source_old]
    rcases RelativeLadderLayer.renderWith_supported I.boundary J.one (field I)
        (fields X 1) x with hz | ⟨f, hf⟩ | hh
    · exact Or.inl hz
    · exact (congrArg (Short 2) hf).mpr (anchor_short X a f)
    · exact (congrArg (Short 2) hh).mpr
        (CanonicalFieldLayer.grid_short
          (sourceGrid_endpoint le_rfl))
  · rw [source_leaf]
    exact CanonicalFieldLayer.grid_short
      (cut_mem (sourceGrid_bot) _ _)

variable {j : ℕ} (hj : 2 ≤ j) (S : State I.right.scheme I.left.scheme)
  (hS : Admitted X j S) (hp : AvoidsValue S.profile ⊤)

def anchor :=
  GrowthHigherSources.normalized X (by decide) hj S hS hp

local notation "anchor₀" => anchor I X hj S hS hp

theorem anchor_fields : fields X 2 (anchor₀) =
    PairedSlotEncoding.normalize 2 S.profile :=
  GrowthHigherSources.normalized_fields X

theorem birth_ranks d :
    RelativeLadderLayer.ranks (fields X 1) (baseAnchor X (anchor₀)) d =
      LadderScalarRendering.fieldRank S.profile d := by
  rw [baseAnchor_ranks, anchor_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize hp

local notation "decode₀" => PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile)

def render G H d :=
  decode₀ G H
    (source I X attach hA hB hC (anchor₀) d)

def baseRender (H : ExtOrd) : Cell (input₀).lower → ExtOrd :=
  RelativeLadderLayer.renderWith I.boundary (input₀).one
    (field I) (fields X 1) (baseAnchor X (anchor₀)) S.profile H

variable {G : Finset ExtOrd} {H : ExtOrd}

local notation "render₀" => render I X attach hA hB hC hj S hS hp G H

variable (hG : VisibleOn 2 G) (hH : SelfVis 2 H) (hb : BoundedBy S.profile H)

local notation "old₀" => old I X attach hA hB hC

include hG hH hb in
theorem render_old  
     d :
    render₀ (old₀ d) =
      baseRender I X attach hA hB hC hj S hS hp H d := by
  let J := input₀
  have he := congrArg (decode₀ G H)
    (J.source_old (anchor₀) d)
  refine he.trans ?_
  change decode₀ G H
    (RelativeLadderLayer.renderWith I.boundary J.one (field I) (fields X 1)
      (baseAnchor X (anchor₀)) (fields X 2 (anchor₀)) J.ceiling d) = _
  rw [anchor_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized _ hp hG hH (decode_reserved_ceiling hH hb) d

theorem baseRender_lawful (hH : SelfVis 2 H) (hb : BoundedBy S.profile H) :
    RespectsSemanticsBelow (input₀).lowerRows (A, j)
      (fun d => baseRender I X attach hA hB hC hj S hS hp H d.1) :=
  RelativeLadderLayer.renderWith_respects I.boundary I.rows
    (input₀).one (field I) (fields X 1) (proper hB hC)
    _ _ (birth_ranks I X hj S hS hp) hb
    hS.visible
    (hH.mono (by decide)) (boundary_lawful_at I X attach hS)

include hG hH hb in
theorem render_below_old  
     c
    (hc : GradedLe ((input₀).lower.cell c) (A, j)) :
    RespectsSemanticsBelow (rows I X attach hA hB hC)
      ((carrier₀).cell (old₀ c))
      (fun d => render₀ d.1) := by
  let J := input₀
  apply (WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
    (SeparatedSourceLayerCarrier.old_not_full _ _ J.separation)).mpr
  apply (SeparatedSourceLayerCarrier.base_respects_iff J.separation J.lowerRows c _).mpr
  have hl := (baseRender_lawful I X attach hA hB hC hj S hS hp hH hb).mono hc
  simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
    render_old I X attach hA hB hC hj S hS hp hG hH hb, CellScheme.below.mono] using hl

include hG hH hb in
theorem render_lawful_two  
     :
    RespectsSemanticsBelow (rows I X attach hA hB hC) (A, 2)
      (fun d => render I X attach hA hB hC hj S hS hp G H d.1) := by
  let J := input I X attach hA hB hC
  let a := anchor I X hj S hS hp
  have hr := source_lawful I X attach hA hB hC a
  have hν := PairedSlotDecoder.decode_witness (S := PairedSlotEncoding.values S.profile) hG hH
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have hd : (carrier I X attach hA hB hC).grade d.1 ≤ 2 := d.2.2
    have he := hν.clause5 (source I X attach hA hB hC a d.1)
      ((carrier I X attach hA hB hC).grade d.1)
      (le_top.trans_eq (gTop_of_le hd).symm)
      ((carrier I X attach hA hB hC).grade d.1) le_rfl
    exact (congrArg (decode₀ G H) (hr.orderly d)).trans he
  · intro c
    rcases GrowthPaddedSuccessor.cell_cases c.1 with
      ⟨x, hx⟩ | ⟨b, hc⟩
    · have hxc : GradedLe (J.lower.cell x) (A, j) := by
        have hg  := by
          simpa only [hx, CellScheme.grade, SourceLayerCarrier.cell_toCell,
            SourceLayerCarrier.index] using c.2.2
        exact ⟨J.lower.scope_subset x, hg.trans hj⟩
      have hl := render_below_old I X attach hA hB hC hj S hS hp hG hH hb x hxc
      rcases c with ⟨c, h⟩
      dsimp only at hx
      subst c
      exact hl.locality ⟨old I X attach hA hB hC x, GradedLe.refl _⟩
    · rcases c with ⟨c, h⟩
      dsimp only at hc
      subst c
      exact map_capped_locality
        (grade := fun d : (carrier I X attach hA hB hC).below
          ((carrier I X attach hA hB hC).cell (leaf I X attach hA hB hC b)) =>
          (carrier I X attach hA hB hC).grade d.1)
        (E := (rows I X attach hA hB hC).E (leaf I X attach hA hB hC b))
        (c := (⟨leaf I X attach hA hB hC b, GradedLe.refl _⟩ :
          (carrier I X attach hA hB hC).below
            ((carrier I X attach hA hB hC).cell (leaf I X attach hA hB hC b))))
        (p := fun d => source I X attach hA hB hC a d.1)
        (fun d => d.2.2)
        (by simp only [CellScheme.grade, leaf_index, le_refl])
        (fun d => by
          simpa only [CellScheme.grade, leaf_index] using
            (congrArg (Short 2) (leaf_row I X attach hA hB hC b d)).mpr
              (source_short I X attach hA hB hC b d.1))
        (hr.orderly ⟨leaf I X attach hA hB hC b, h⟩).symm
        (hr.locality ⟨leaf I X attach hA hB hC b, h⟩) hν
  · intro c t hs hg
    obtain ⟨w, hw, hle⟩ := hr.availability c t hs hg
    exact ⟨w, hw, hν.mono hle⟩

include hG hH hb in
/-- The original owners above grade two are read literally and use their own
lawful domains. No upper-grade commutation of the grade-two decoder is needed. -/
theorem render_lawful  
     :
    RespectsSemanticsBelow (rows I X attach hA hB hC) (A, j)
      (fun d => render₀ d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  rcases GrowthPaddedSuccessor.cell_cases c.1 with
    ⟨x, hx⟩ | ⟨a, ha⟩
  · have hxc : GradedLe ((input₀).lower.cell x) (A, j) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    rcases c with ⟨c, hc⟩
    dsimp  at hx
    subst c
    exact render_below_old I X attach hA hB hC hj S hS hp hG hH hb x hxc
  · have he : (carrier₀).cell c.1 = (A, 2) :=
      (congrArg (carrier₀).cell ha).trans (leaf_index a)
    exact GradeCutLayerRows.cast_respects he.symm
      (render_lawful_two I X attach hA hB hC hj S hS hp hG hH hb)

theorem render_bound (hH : SelfVis 2 H) (hb : BoundedBy S.profile H)
    d :
    render₀ d ≤ H := by
  apply PairedSlotDecoder.decode_le hH
  intro v hv
  obtain ⟨x, hx⟩ := PairedSlotEncoding.mem_values.mp hv
  simpa only [hx] using hb x

local notation "render₀₀" => render I X attach hA hB hC hj

theorem render_supported {l} (hl : 2 ≤ l) (hH : H ∈ G)
    d :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile
      (render₀₀ S hS hp G H d) :=
  PairedSlotDecoder.decode_supported hl hH _

/-- Whole-coordinate agreement at fixed outer parameters, not equality of
independently rendered sections at different construction grades. -/
theorem render_prefix {T} (hT : Admitted X j T)
    (ht : AvoidsValue T.profile ⊤) {h}
    (hG : VisibleOn 2 G) (hH : SelfVis 2 H)
    (hh : h ∈ G) (hhH : h ≤ H) (hag : Agree S.profile T.profile h) :
    Agree (render₀)
      (render₀₀ T hT ht G H) h := by
  obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ :=
    exists_common_cut hG hH hH hh hhH hhH hp ht hag
  have he' : Agree (fields X 2 (anchor₀))
      (fields X 2 (anchor I X hj T hT ht)) e := by
    rw [anchor_fields, anchor_fields]
    exact he
  have hs := source_prefix I X attach hA hB hC
    (anchor₀) (anchor I X hj T hT ht) heG he'
  exact Agree.decode hs (PairedSlotDecoder.decode_witness hG hH).mono
    (PairedSlotDecoder.decode_witness hG hH).mono hpe hqe (fun _ _ => hcompare _)

theorem render_ceiling (hH : SelfVis 2 H) (hb : BoundedBy S.profile H) :
    render₀
      (leaf I X attach hA hB hC (anchor₀)) = H := by
  unfold render
  rw [source_ceiling]
  exact decode_reserved_ceiling hH hb

include hG hH hb in
/-- The retained padded base has its own actual full-scope ceiling occurrence. -/
theorem render_base_ceiling  
     :
    ∃ c ,
      (carrier I X attach hA hB hC).cell c = (A, 1) ∧
      render₀₀ S hS hp G H c = H := by
  let J := input I X attach hA hB hC
  let a := baseAnchor X (anchor I X hj S hS hp)
  let v := SupportLadderRows.leaf
    (H := RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme))
    (X := Field I.right.scheme I.left.scheme) (by unfold RelativeLadderLayer.rungs; omega) a
  let c := RelativeLadderLayer.added I.boundary J.one v
  refine ⟨old₀ c, ?_, ?_⟩
  · exact (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans
      (RelativeLadderLayer.added_index I.boundary J.one v)
  · rw [render_old I X attach hA hB hC hj S hS hp hG hH hb]
    change LadderScalarRendering.level (LadderScalarRendering.values S.profile) H
      (RelativeLadderLayer.rankIndex I.boundary J.one (field I) (fields X 1) a c) = H
    rw [RelativeLadderLayer.rankIndex_added, SupportLadderRows.index_leaf,
      FiniteProfileControllers.cut_refl]
    exact ite_eq_left (by
      have := LadderScalarRendering.values_card_le S.profile
      unfold RelativeLadderLayer.rungs
      omega)

