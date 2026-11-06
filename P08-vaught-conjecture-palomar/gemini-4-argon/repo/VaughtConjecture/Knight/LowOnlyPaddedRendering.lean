/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSuccessor
public import VaughtConjecture.Knight.RelativeLadderTableDecode
public import VaughtConjecture.Knight.OwnerwiseDecoding

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedRendering
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedSuccessor SourcePrefixRows SharpWitnessComposition
open PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Car" => carrier I F hroot hA hB hC
local notation "Ccell" => CellScheme.cell (carrier I F hroot hA hB hC)
local notation "Cgrade" => CellScheme.grade (carrier I F hroot hA hB hC)
local notation "Rws" => rows I F hroot hA hB hC
local notation "src" => source I F hroot hA hB hC
local notation "old'" => old I F hroot hA hB hC
local notation "leaf'" => leaf I F hroot hA hB hC

theorem source_short (a : F.Anchor 2) (d : Cell Car) : Short 2 (src a d) := by
  let J := input I F hroot hA hB hC
  rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC d with ⟨x, rfl⟩ | ⟨b, rfl⟩
  · change Short 2 (J.source a (J.old x))
    rw [J.source_old]
    rcases RelativeLadderLayer.renderWith_supported I.boundary J.one (field I)
        (F.fields 1) (baseAnchor F a) (F.fields 2 a) J.ceiling x with hz | ⟨f, hf⟩ | hh
    · exact Or.inl hz
    · exact (congrArg (Short 2) hf).mpr (LowOnlyRecursiveCharts.anchor_short F a f)
    · exact (congrArg (Short 2) hh).mpr
        (CanonicalFieldLayer.grid_short 2 (Field I.left I.right) (sourceGrid_endpoint le_rfl))
  · rw [source_leaf]
    exact CanonicalFieldLayer.grid_short 2 (Field I.left I.right) (cut_mem (sourceGrid_bot _ _) _ _)

variable {j : ℕ} (hj : 2 ≤ j) (S : State I.left I.right)
  (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤)

def anchor : F.Anchor 2 := LowOnlyRecursiveCoverage.normalizedAnchor F (by decide) hj hS hp

local notation "anch" => anchor I F hj S hS hp

theorem birth_ranks (d : Field I.left I.right) :
    RelativeLadderLayer.ranks (F.fields 1) (baseAnchor F anch) d =
      LadderScalarRendering.fieldRank S.profile d := by
  rw [baseAnchor_ranks, anchor, LowOnlyRecursiveCoverage.normalizedAnchor_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize 2 S.profile hp d

def render (G : Finset ExtOrd) (H : ExtOrd) (d : Cell Car) : ExtOrd :=
  PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile) G H (src anch d)

local notation "rnd" => render I F hroot hA hB hC hj S hS hp

variable {G : Finset ExtOrd} {H : ExtOrd}

theorem render_old (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) (d : Cell (input I F hroot hA hB hC).lower) :
    rnd G H (old' d) =
      RelativeLadderLayer.renderWith I.boundary (input I F hroot hA hB hC).one (field I)
        (F.fields 1) (baseAnchor F anch) S.profile H d := by
  let J := input I F hroot hA hB hC
  refine (congrArg (PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile) G H)
    (J.source_old anch d)).trans ?_
  change PairedSlotDecoder.decode 2 (PairedSlotEncoding.values S.profile) G H
    (RelativeLadderLayer.renderWith I.boundary J.one (field I) (F.fields 1)
      (baseAnchor F anch) (F.fields 2 anch) J.ceiling d) = _
  rw [anchor, LowOnlyRecursiveCoverage.normalizedAnchor_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized I.boundary J.one
    (field I) (F.fields 1) 2 _ S.profile hp hG hH (decode_reserved_ceiling hH hb) d

theorem render_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow Rws (A, j) (fun d => rnd G H d.1) := by
  let J := input I F hroot hA hB hC
  have hold (x : Cell J.lower) (hxc : GradedLe (J.lower.cell x) (A, j)) :
      RespectsSemanticsBelow Rws (Ccell (old' x)) (fun d => rnd G H d.1) := by
    apply (WeightedSourcePrefixLayer.old_respects_iff J.data J.weight J.weight_visible
      (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation x)).mpr
    apply (SeparatedSourceLayerCarrier.base_respects_iff J.lower
      (LadderWeightedSuccessor.Input.Node (U := F.Anchor 2) (V := Empty))
      2 (by decide) hA J.separation J.lowerRows x _).mpr
    have hl : RespectsSemanticsBelow J.lowerRows (A, j) _ :=
      RelativeLadderLayer.renderWith_respects I.boundary I.rows J.one (field I) (F.fields 1)
        (proper I hB hC) _ _ (birth_ranks I F hj S hS hp) hb
        (LowOnlyRecursiveCharts.profile_visible_one F (by omega) hS) (hH.mono (by decide))
        (LowOnlyOrderedSources.boundary_lawful_at I F hroot j S hS)
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      render_old I F hroot hA hB hC hj S hS hp hG hH hb, CellScheme.below.mono] using hl.mono hxc
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c.1 with ⟨x, hx⟩ | ⟨a, ha⟩
  · have hxc : GradedLe (J.lower.cell x) (A, j) := by
      simpa only [hx, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using c.2
    rcases c with ⟨c, hc⟩; dsimp only at hx; subst c
    exact hold x hxc
  · have he : Ccell c.1 = (A, 2) :=
      (congrArg Ccell ha).trans (leaf_index I F hroot hA hB hC a)
    refine GradeCutLayerRows.cast_respects _ _ he.symm
      (map_respects_of_short_or_local (source_lawful I F hroot hA hB hC anch)
        (fun d => d.2.2) (PairedSlotDecoder.decode_witness hG hH) fun d => ?_)
    rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC d.1 with ⟨x, hx⟩ | ⟨b, hb'⟩
    · have hg : J.lower.grade x ≤ 2 := by
        simpa only [hx, CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using d.2.2
      have hxc : GradedLe (J.lower.cell x) (A, j) :=
        ⟨J.lower.isPlan.subset_of_mem (J.lower.scope_mem_plan x), hg.trans hj⟩
      rcases d with ⟨d, hd⟩; dsimp only at hx; subst d
      exact Or.inr ((hold x hxc).locality ⟨old' x, GradedLe.refl _⟩)
    · rcases d with ⟨d, hd⟩; dsimp only at hb'; subst d
      exact Or.inl fun e => by
        simpa only [CellScheme.grade, leaf_index] using
          (congrArg (Short 2) (leaf_row I F hroot hA hB hC b e)).mpr
            (source_short I F hroot hA hB hC b e.1)

theorem render_bound (hH : SelfVis 2 H) (hb : ∀ d, S.profile d ≤ H) (d : Cell Car) :
    rnd G H d ≤ H := by
  apply PairedSlotDecoder.decode_le hH
  intro v hv
  obtain ⟨x, hx⟩ := PairedSlotEncoding.mem_values.mp hv
  simpa only [hx] using hb x

theorem render_supported {l : ℕ} (hl : 2 ≤ l) (hH : H ∈ G) (d : Cell Car) :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile (rnd G H d) :=
  PairedSlotDecoder.decode_supported hl hH _

theorem render_prefix {T : State I.left I.right} (hT : F.Admissible j T)
    (ht : ∀ d, T.profile d ≠ ⊤) {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hh : h ∈ G) (hhH : h ≤ H) (hag : Agree S.profile T.profile h) :
    Agree (rnd G H) (render I F hroot hA hB hC hj T hT ht G H) h := by
  obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ :=
    exists_common_cut hG hH hH hh hhH hhH hp ht hag
  have he' : Agree (F.fields 2 anch) (F.fields 2 (anchor I F hj T hT ht)) e := by
    rw [anchor, anchor, LowOnlyRecursiveCoverage.normalizedAnchor_fields,
      LowOnlyRecursiveCoverage.normalizedAnchor_fields]
    exact he
  exact Agree.decode (source_prefix I F hroot hA hB hC anch _ heG he')
    (PairedSlotDecoder.decode_witness hG hH).mono (PairedSlotDecoder.decode_witness hG hH).mono
    hpe hqe fun _ _ => hcompare _

theorem render_ceiling (hH : SelfVis 2 H) (hb : ∀ d, S.profile d ≤ H) :
    rnd G H (leaf' anch) = H := by
  unfold render; rw [source_ceiling]; exact decode_reserved_ceiling hH hb

theorem render_base_ceiling (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, S.profile d ≤ H) :
    ∃ c : Cell Car, Ccell c = (A, 1) ∧ rnd G H c = H := by
  let J := input I F hroot hA hB hC
  let a := baseAnchor F anch
  let v := SupportLadderRows.leaf
    (H := RelativeLadderLayer.rungs (X := Field I.left I.right))
    (X := Field I.left I.right) (by unfold RelativeLadderLayer.rungs; omega) a
  let c := RelativeLadderLayer.added I.boundary J.one v
  refine ⟨old' c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans
    (RelativeLadderLayer.added_index I.boundary J.one v), ?_⟩
  rw [render_old I F hroot hA hB hC hj S hS hp hG hH hb]
  change LadderScalarRendering.level (LadderScalarRendering.values S.profile) H
    (RelativeLadderLayer.rankIndex I.boundary J.one (field I) (F.fields 1) a c) = H
  rw [RelativeLadderLayer.rankIndex_added, SupportLadderRows.index_leaf,
    FiniteProfileControllers.cut_refl]
  exact ite_eq_left (by
    have := LadderScalarRendering.values_card_le S.profile
    unfold RelativeLadderLayer.rungs; omega)

