/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeCutSections
public import VaughtConjecture.Knight.PairedCoupledSections

public import VaughtConjecture.Knight.SourceAttachment

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalMixedGradeLayers

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition

open PairedSlotEncoding PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- A lower full-scope layer followed by a strictly higher one over the
same proper boundary. Both layers use the same original field coordinates. -/
structure Frame (D : CellScheme A) where
  sem : Semantics D
  lower : ℕ
  upper : ℕ
  pos : 0 < lower
  strict : lower < upper
  height : upper ≤ A.card
  proper : ∀ d : Cell D, D.scope d ≠ A
  grade : ∀ d : Cell D, D.grade d ≤ upper

namespace Frame

variable (M : Frame D)

theorem lower_card : M.lower ≤ A.card := M.strict.le.trans M.height

theorem upper_pos : 0 < M.upper := M.pos.trans M.strict

def two (sem : Semantics D) (hA : 2 ≤ A.card)
    (hp : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2) : Frame D :=
  ⟨sem, 1, 2, by decide, by decide, hA, hp, hg⟩

end Frame

abbrev enlarged (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
    (k : ℕ) (hk : 0 < k) (hkA : k ≤ A.card) :=
  SourceLayerCarrier.scheme (CanonicalGradeCutSections.scheme sem j hj hjA)
    (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA

variable (M : Frame D)

local notation "Sem₀" => M.sem
local notation "j" => M.lower
local notation "k" => M.upper
local notation "hj" => M.pos
local notation "hjA" => M.lower_card
local notation "hk" => M.upper_pos
local notation "hkA" => M.height
local notation "hjk" => M.strict
local notation "hg" => M.grade
local notation "hproper" => M.proper

abbrev lowerScheme := CanonicalGradeCutSections.scheme Sem₀ j hj hjA

abbrev lowerSem := CanonicalGradeCutSections.rows Sem₀ j hj hjA hproper

abbrev lowerOld := CanonicalGradeCutSections.old Sem₀ j hj hjA

theorem lower_grade (d : Cell (lowerScheme M)) :
    (lowerScheme M).grade d ≤ k := by
  rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA d with
  | inl c => exact hg c
  | inr q => exact (hjk).le

theorem lower_separated (d : Cell (lowerScheme M)) :
    ¬ GradedLe (A, k) ((lowerScheme M).cell d) := by
  rw [SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA d with
  | inl c =>
    intro hc
    exact hproper c (Finset.Subset.antisymm
      (D.scope_subset c) hc.1)
  | inr q => exact fun hc => (not_le_of_gt hjk) hc.2

abbrev upperGrid := sourceGrid k (Fintype.card (Cell D))

abbrev upperCeiling := CanonicalFieldLayer.ceiling k (Cell D)

abbrev lowerSection (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) :
    Cell (lowerScheme M) → ExtOrd :=
  CanonicalGradeCutSections.sectionOf Sem₀ j hj hjA hproper q.property.1
    q.property.2.2
    (upperGrid M) (upperCeiling M)

theorem grid_lower_visible {h : ExtOrd} (hh : h ∈ upperGrid M) :
    SelfVis j h := selfVis_mono (sourceGrid_visible hh) (hjk).le

theorem lowerSection_lawful (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) :
    RespectsSemantics (lowerSem M)
      (lowerSection M q) :=
  CanonicalGradeCutSections.section_lawful Sem₀ j hj hjA hproper q.property.1 _
    (fun _ hh => grid_lower_visible M hh)
    (grid_lower_visible M (sourceGrid_endpoint le_rfl))

theorem lowerSection_old (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) (d : Cell D) :
    lowerSection M q (lowerOld M d) = q.val d :=
  CanonicalGradeCutSections.section_old Sem₀ j hj hjA hproper q.property.1 _ d

theorem lowerSection_bound (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    (d : Cell (lowerScheme M)) :
    lowerSection M q d ≤ upperCeiling M :=
  CanonicalGradeCutSections.section_bound Sem₀ j hj hjA hproper q.property.1 _
    (grid_lower_visible M (sourceGrid_endpoint le_rfl))
    (CanonicalFieldLayer.profile_bound Sem₀ k (Cell D) id q) d

theorem lowerSection_supported (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    (d : Cell (lowerScheme M)) :
    OrbitPrefixSupport.Supported k (upperGrid M : Set ExtOrd) q.val
      (lowerSection M q d) :=
  CanonicalGradeCutSections.section_supported Sem₀ j hj hjA hproper q.property.1 _ (hjk).le
    (sourceGrid_endpoint le_rfl) d

theorem lowerSection_agreement (p q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    {h : ExtOrd} (hh : h ∈ upperGrid M) (hag : Agree p.val q.val h) :
    Agree (lowerSection M p)
      (lowerSection M q) h :=
  CanonicalGradeCutSections.section_agreement Sem₀ j hj hjA hproper p.property.1 _ q.property.1 _
    (fun _ hz => grid_lower_visible M hz)
    (grid_lower_visible M (sourceGrid_endpoint le_rfl)) hh
    (CanonicalFieldLayer.grid_bound k (Cell D) hh) hag

abbrev scheme := enlarged Sem₀ j hj hjA k hk hkA

abbrev oldCell (d : Cell (lowerScheme M)) : Cell (scheme M) :=
  SourceLayerCarrier.toCell (lowerScheme M)
    (CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) k hk hkA (.inl d)

abbrev controller (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) :=
  SourceLayerCarrier.controller (lowerScheme M)
    (CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) k hk hkA q

abbrev ownerEquiv (c : Cell (lowerScheme M)) :=
  SeparatedSourceLayerCarrier.ownerEquiv (lowerScheme M)
    (CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) k hk hkA
    (lower_separated M) c

theorem max_grade (d : Cell (scheme M)) :
    (scheme M).grade d ≤ k := by
  rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc (lowerScheme M)
      (CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) k hk hkA d with
  | inl x => exact lower_grade M x
  | inr q => rfl

def attachment : SourceAttachment (lowerScheme M) k (Cell D)
    (CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) where
  sem := lowerSem M
  pos := hk
  height := hkA
  separated := lower_separated M
  toAttachmentGrid := AttachmentGrid.canonical k (Fintype.card (Cell D))
  fields := Subtype.val
  lower := lowerSection M
  lower_bound q d _ := lowerSection_bound M q d
  lower_lawful q := (lowerSection_lawful M q).toBelow _
  lower_prefix p q _ hh hag d _ := lowerSection_agreement M p q hh hag d

abbrev data := (attachment M).data

abbrev rows := (data M).rows

abbrev source (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) :=
  (data M).profile (controller M q)

theorem source_lower (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    (d : Cell (lowerScheme M)) :
    source M q (oldCell M d) =
      lowerSection M q d :=
  (attachment M).source_old q d

theorem source_boundary (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id) (d : Cell D) :
    source M q
      (oldCell M (lowerOld M d)) = q.val d := by grind [source_lower, lowerSection_old]

theorem inherited_row (c : Cell (lowerScheme M))
    (d : (lowerScheme M).below ((lowerScheme M).cell c)) :
    (rows M).E (oldCell M c)
      (ownerEquiv M c d) =
      (lowerSem M).E c d :=
  (attachment M).inherited_row c d

theorem original_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows M).E
      (oldCell M (lowerOld M c))
      (ownerEquiv M (lowerOld M c)
        (GradeCutLayerCarrier.ownerEquiv D (CanonicalGradeCutSections.Profiles Sem₀ j)
          j hj hjA hproper c d)) = (Sem₀).E c d := by
  rw [inherited_row]
  apply CanonicalGradeCutSections.old_row

theorem consistent (hs : (Sem₀).IsConsistent) :
    (rows M).IsConsistent :=
  (attachment M).consistent
    (CanonicalGradeCutSections.consistent Sem₀ j hj hjA hproper hs)

theorem source_agreement (p q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    {h : ExtOrd} (hh : h ∈ upperGrid M) (hag : Agree p.val q.val h) :
    Agree (source M p)
      (source M q) h :=
  (attachment M).source_prefix hh hag
    (lowerSection_agreement M p q hh hag)

theorem source_supported (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    (d : Cell (scheme M)) :
    OrbitPrefixSupport.Supported k (upperGrid M : Set ExtOrd) q.val
      (source M q d) :=
  (attachment M).source_supported
    (lowerSection_supported M) q d

theorem source_short (q : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id)
    (d : Cell (scheme M)) :
    Short k (source M q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short k (Cell D) hh)
    (CanonicalFieldLayer.profile_short Sem₀ k (Cell D) id q)
    (source_supported M q d)

theorem lower_full_short (c : Cell (lowerScheme M))
    (hc : (lowerScheme M).scope c = A)
    (d : (lowerScheme M).below ((lowerScheme M).cell c)) :
    Short ((lowerScheme M).grade c)
      ((lowerSem M).E c d) := by
  have hjc : (lowerScheme M).grade c ≤ j := by
    have hs := hc
    rw [CellScheme.scope, SourceLayerCarrier.cell_eq] at hs
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases he : SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA c with
    | inl a =>
      rw [he] at hs
      exact (hproper a hs).elim
    | inr q => exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutLayerCarrier.exhaustive D
    (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA c hjc
  obtain ⟨e, rfl⟩ := (GradeCutLayerCarrier.belowEquiv D
    (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA _ hjc).surjective d
  have he := CanonicalGradeCutSections.lower_row Sem₀ j hj hjA hproper a
    ⟨e.1, by simpa only [GradeCutLayerCarrier.embed_cell] using e.2⟩
  have hv := CanonicalFieldLayer.full_source_short
    (CanonicalGradeCutSections.boundaryRows Sem₀ j) j
    (Cell D) (GradeCutBoundary.toCell D j) hj hjA
    (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j) a
    (by simpa only [CellScheme.scope, GradeCutLayerCarrier.embed_cell] using hc)
    ⟨e.1, by grind⟩
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd
    (GradeCutLayerCarrier.embed_cell D (CanonicalGradeCutSections.Profiles Sem₀ j)
      j hj hjA a))).mpr hv

theorem lower_proper_respects {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p)
    {r : Cell (lowerScheme M) → ExtOrd}
    (hread : ∀ d, r (lowerOld M d) = p d)
    (c : Cell (lowerScheme M)) (hc : (lowerScheme M).scope c ≠ A) :
    RespectsSemanticsBelow (lowerSem M)
      ((lowerScheme M).cell c) (fun d => r d.1) := by
  have hc' : (lowerScheme M).cell c ≠ (A, j) :=
    by simp_all
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D
    (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA c hc'
  apply (GradeCutLayerRows.old_respects_iff D (CanonicalGradeCutSections.Profiles Sem₀ j) j hj hjA
    hproper Sem₀ (CanonicalGradeCutSections.lowerRows Sem₀ j hj hjA hproper) x _).mpr
  change RespectsSemanticsBelow Sem₀ (D.cell x) (fun d => r (lowerOld M d.1))
  simpa [hread] using hp.toBelow (D.cell x)

theorem full_source_short (c : Cell (scheme M))
    (hc : (scheme M).scope c = A)
    (d : (scheme M).below ((scheme M).cell c)) :
    Short ((scheme M).grade c)
      ((rows M).E c d) := by
  exact (attachment M).higher_short 0
    (source_short M)
    (fun x hs _ => lower_full_short M x hs) c hc (Nat.zero_le _) d

abbrev normalized {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p)
    (ht : ∀ d, p d ≠ ⊤) : CanonicalFieldLayer.Profile Sem₀ k (Cell D) id :=
  CanonicalFieldLayer.encode Sem₀ k (Cell D) id hg hp ht

variable {G : Finset ExtOrd} {C : ExtOrd}

/-- The new selected section decodes the complete coupled source, including
all retained lower controllers. Lower sections are not supplied as parameters. -/
def sectionOf {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p)
    (ht : ∀ d, p d ≠ ⊤) (G : Finset ExtOrd) (C : ExtOrd)
    (d : Cell (scheme M)) : ExtOrd :=
  PairedSlotDecoder.decode k (values p) G C
    (source M (normalized M hp ht) d)

theorem section_boundary {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) (d : Cell D) :
    sectionOf M hp ht G C
      (oldCell M (lowerOld M d)) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) :
    RespectsSemantics (rows M)
      (sectionOf M hp ht G C) := by
  apply (attachment M).decoded_whole
    (normalized M hp ht) (PairedSlotDecoder.decode_witness hG hC)
    (max_grade M) _ (full_source_short M)
  refine lower_proper_respects M hp
    (r := fun y => PairedSlotDecoder.decode k (values p) G C
      (lowerSection M (normalized M hp ht) y)) ?_
  intro d
  rw [lowerSection_old M]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_bound {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis k C) (hb : ∀ d, p d ≤ C)
    (d : Cell (scheme M)) :
    sectionOf M hp ht G C d ≤ C := by
  exact PairedSlotDecoder.decode_le_of_bound hC hb _

theorem section_supported {K : ℕ} (hkK : k ≤ K) (hCG : C ∈ G)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics Sem₀ p) (ht : ∀ d, p d ≠ ⊤)
    (d : Cell (scheme M)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf M hp ht G C d) :=
  PairedSlotDecoder.decode_supported hkK hCG _

theorem section_agreement {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics Sem₀ p) (hq : RespectsSemantics Sem₀ q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z)
    (hC : SelfVis k C) (hh : h ∈ G)
    (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf M hp htp G C)
      (sectionOf M hq htq G C) h := by
  exact decode_agreement hG hC hh hhC htp htq hag
    (fun _ he ha => source_agreement M _ _ he ha)

end

end VaughtConjecture.Knight.CanonicalMixedGradeLayers
