/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeCutSections
public import VaughtConjecture.Knight.PairedCoupledSections

/-! # Canonical coupled controller rows over the full field inventory

Retained proper owners may have the upper grade. Separation uses their scope,
not an artificial strict grade bound. The lower full-scope controllers and all
proper owners are retained literally; their source readings are constructed by
the grade-cut section operator on the entire enlarged lower carrier.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalMixedGradeLayers

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotEncoding PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)

abbrev lowerScheme := CanonicalGradeCutSections.scheme sem j hj hjA
abbrev lowerSem := CanonicalGradeCutSections.rows sem j hj hjA hproper
abbrev lowerOld := CanonicalGradeCutSections.old sem j hj hjA

local notation "LScheme" => lowerScheme sem j hj hjA
local notation "LSem" => lowerSem sem j hj hjA hproper
local notation "LOld" => lowerOld sem j hj hjA
local notation "P_j" => CanonicalGradeCutSections.Profiles sem j

variable (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
  (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

include hproper hjk in
theorem lower_separated (d : Cell LScheme) : ¬ GradedLe (A, k) (CellScheme.cell LScheme d) := by
  rw [SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc D P_j j hj hjA d with
  | inl c => exact fun hc => hproper c (Finset.Subset.antisymm
      (D.isPlan.subset_of_mem (D.scope_mem_plan c)) hc.1)
  | inr _ => exact fun hc => (not_le_of_gt hjk) hc.2

local notation "LSep" => lower_separated sem j hj hjA hproper k hjk

abbrev upperGrid := sourceGrid k (Fintype.card (Cell D))
abbrev upperCeiling := PairedBoundarySections.ceiling (D := D) k

local notation "UGrid" => upperGrid (D := D) k
local notation "UCeil" => upperCeiling (D := D) k
local notation "Prof" => CanonicalFieldLayer.Profile sem k (Cell D) id

abbrev lowerSection (q : Prof) : Cell LScheme → ExtOrd :=
  CanonicalGradeCutSections.sectionOf sem j hj hjA hproper q.property.1 q.property.2.2 UGrid UCeil

local notation "LSec" => lowerSection sem j hj hjA hproper k

include hjk in
theorem grid_lower_visible {h : ExtOrd} (hh : h ∈ UGrid) : SelfVis j h :=
  selfVis_mono (sourceGrid_visible hh) hjk.le

local notation "gvis" => grid_lower_visible j k hjk

theorem lowerSection_old (q : Prof) (d : Cell D) : LSec q (LOld d) = q.val d :=
  CanonicalGradeCutSections.section_old sem j hj hjA hproper q.property.1 _ d

include hjk in
theorem lowerSection_supported (q : Prof) (d : Cell LScheme) :
    OrbitPrefixSupport.Supported k (UGrid : Set ExtOrd) q.val (LSec q d) :=
  CanonicalGradeCutSections.section_supported sem j hj hjA hproper q.property.1 _ hjk.le
    (sourceGrid_endpoint le_rfl) d

abbrev scheme := SourceLayerCarrier.scheme LScheme Prof k hk hkA

local notation "Sch" => scheme sem j hj hjA k hk hkA

abbrev oldCell (d : Cell LScheme) : Cell Sch :=
  SourceLayerCarrier.toCell LScheme Prof k hk hkA (.inl d)

local notation "OCell" => oldCell sem j hj hjA k hk hkA

abbrev controller (q : Prof) := SourceLayerCarrier.controller LScheme Prof k hk hkA q

local notation "Ctrl" => controller sem j hj hjA k hk hkA

def member (c : SourcePrefixLayer.Controller Sch k) : Prof :=
  (SeparatedSourceLayerCarrier.controllerEquiv LScheme Prof k hk hkA LSep).symm c

local notation "Mem" => member sem j hj hjA hproper k hk hkA hjk

theorem member_controller (q : Prof) : Mem (Ctrl q) = q :=
  (SeparatedSourceLayerCarrier.controllerEquiv LScheme Prof k hk hkA LSep).symm_apply_apply q

abbrev ownerEquiv (c : Cell LScheme) :=
  SeparatedSourceLayerCarrier.ownerEquiv LScheme Prof k hk hkA LSep c

local notation "OEquiv" => ownerEquiv sem j hj hjA hproper k hk hkA hjk

def lower (q : Prof) (d : Cell Sch) : ExtOrd :=
  match SourceLayerCarrier.toOcc LScheme Prof k hk hkA d with
  | .inl x => LSec q x
  | .inr _ => ⊥

local notation "Low" => lower sem j hj hjA hproper k hk hkA

theorem lower_old (q : Prof) (d : Cell LScheme) : Low q (OCell d) = LSec q d := by
  simp only [lower, oldCell, SourceLayerCarrier.toOcc_toCell]

def data : SourcePrefixLayer.Data Sch k (Cell D) where
  base := SeparatedSourceLayerCarrier.base LScheme Prof k hk hkA LSep LSem
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc LScheme Prof k hk hkA d with
    | inl x =>
      rw [SourceLayerCarrier.index, SourceLayerCarrier.cell_eq]
      cases SourceLayerCarrier.toOcc D P_j j hj hjA x with
      | inl c => exact hg c
      | inr _ => exact hjk.le
    | inr _ => exact le_rfl
  grid := UGrid
  bot_mem := sourceGrid_bot _ _
  ceiling := UCeil
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := PairedBoundarySections.grid_bound k hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (Mem c).val
  lower c := Low (Mem c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA d hd
    rw [lower_old]
    exact CanonicalGradeCutSections.section_bound sem j hj hjA hproper (Mem c).property.1 _
      (gvis (sourceGrid_endpoint le_rfl))
      (CanonicalFieldLayer.profile_bound sem k (Cell D) id (Mem c)) x
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff LScheme Prof k hk hkA LSep LSem x _).mpr
    change RespectsSemanticsBelow LSem _ (fun d => Low (Mem c) (OCell d.1))
    simpa only [lower_old] using
      (CanonicalGradeCutSections.section_lawful sem j hj hjA hproper (Mem c).property.1 _
        (fun _ hh => gvis hh) (gvis (sourceGrid_endpoint le_rfl)) :
        RespectsSemantics LSem (LSec (Mem c))).toBelow _
  grid_agreement p q h hh hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA d hd
    simpa only [lower_old] using
      (CanonicalGradeCutSections.section_agreement sem j hj hjA hproper
        (Mem p).property.1 _ (Mem q).property.1 _
        (fun _ hz => gvis hz) (gvis (sourceGrid_endpoint le_rfl)) hh
        (PairedBoundarySections.grid_bound k hh) hag : Agree (LSec (Mem p)) (LSec (Mem q)) h) x

local notation "Dat" => data sem j hj hjA hproper k hg hk hkA hjk

abbrev rows := (Dat).rows
abbrev source (q : Prof) := (Dat).profile (Ctrl q)

local notation "Rws" => rows sem j hj hjA hproper k hg hk hkA hjk
local notation "Src" => source sem j hj hjA hproper k hg hk hkA hjk

theorem source_lower (q : Prof) (d : Cell LScheme) : Src q (OCell d) = LSec q d := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full LScheme Prof k hk hkA LSep d)]
  change Low (Mem (Ctrl q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Prof) (d : Cell D) : Src q (OCell (LOld d)) = q.val d := by
  rw [source_lower, lowerSection_old sem j hj hjA hproper k]

theorem inherited_row (c : Cell LScheme)
    (d : CellScheme.below LScheme (CellScheme.cell LScheme c)) :
    Semantics.E Rws (OCell c) (OEquiv c d) = Semantics.E LSem c d := by
  rw [SourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full LScheme Prof k hk hkA LSep c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem inherited_order : StrictMono OCell := SourceLayerCarrier.old_order _ _ _ _ _

theorem original_row (c : Cell D) (d : D.below (D.cell c)) :
    Semantics.E Rws (OCell (LOld c))
      (OEquiv (LOld c) (GradeCutLayerCarrier.ownerEquiv D P_j j hj hjA hproper c d)) =
      sem.E c d := by
  rw [inherited_row]; exact CanonicalGradeCutSections.old_row sem j hj hjA hproper c d

theorem consistent (hs : sem.IsConsistent) : Semantics.IsConsistent Rws := by
  apply SourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff LScheme Prof k hk hkA LSep LSem x _).mpr
  have he : (Dat).base.E (OCell x) ∘ OEquiv x = Semantics.E LSem x :=
    funext fun d => SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact CanonicalGradeCutSections.consistent sem j hj hjA hproper hs x

theorem source_agreement (p q : Prof) {h : ExtOrd} (hh : h ∈ UGrid) (hag : Agree p.val q.val h) :
    Agree (Src p) (Src q) h := by
  apply (Dat).profile_prefix hh
  change Agree (Mem (Ctrl p)).val (Mem (Ctrl q)).val h
  simpa only [member_controller] using hag

theorem source_supported (q : Prof) (d : Cell Sch) :
    OrbitPrefixSupport.Supported k (UGrid : Set ExtOrd) q.val (Src q d) := by
  by_cases hd : CellScheme.cell Sch d = (A, k)
  · refine Or.inr (Or.inl ?_)
    change (Dat).profile (Ctrl q) d ∈ UGrid
    rw [(Dat).profile_new (Ctrl q) ⟨d, hd⟩]
    exact cut_mem (sourceGrid_bot _ _) _ _
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA d hd
    rw [source_lower]
    exact lowerSection_supported sem j hj hjA hproper k hjk q x

theorem source_short (q : Prof) (d : Cell Sch) : Short k (Src q d) :=
  PairedCoupledSections.supported_short (fun _ hh => PairedBoundarySections.grid_short k hh)
    (CanonicalFieldLayer.profile_short sem k (Cell D) id q)
    (source_supported sem j hj hjA hproper k hg hk hkA hjk q d)

theorem full_source_short (c : Cell Sch) (hc : CellScheme.scope Sch c = A)
    (d : CellScheme.below Sch (CellScheme.cell Sch c)) :
    Short (CellScheme.grade Sch c) (Semantics.E Rws c d) := by
  apply (Dat).full_source_short (fun _ hh => PairedBoundarySections.grid_short k hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA x hx
    change Short k (Low _ (OCell y))
    rw [lower_old]
    exact PairedCoupledSections.supported_short (fun _ hh => PairedBoundarySections.grid_short k hh)
      (CanonicalFieldLayer.profile_short sem k (Cell D) id _)
      (lowerSection_supported sem j hj hjA hproper k hjk _ y)
  · intro x hs hx e
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA x hx
    obtain ⟨z, rfl⟩ := (OEquiv y).surjective e
    have he : (Dat).base.E _ _ = _ :=
      SeparatedSourceLayerCarrier.base_old LScheme Prof k hk hkA LSep LSem y z
    rw [he]
    have hi := SourceLayerCarrier.cell_toCell LScheme Prof k hk hkA (.inl y)
    have hsy : CellScheme.scope LScheme y = A := (congrArg Prod.fst hi).symm.trans hs
    have hjc : CellScheme.grade LScheme y ≤ j := by
      have hs' := hsy
      rw [CellScheme.scope, SourceLayerCarrier.cell_eq] at hs'
      rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
      cases he' : SourceLayerCarrier.toOcc D P_j j hj hjA y with
      | inl a => rw [he'] at hs'; exact (hproper a hs').elim
      | inr _ => exact le_rfl
    obtain ⟨a, rfl⟩ := GradeCutLayerCarrier.exhaustive D P_j j hj hjA y hjc
    obtain ⟨w, rfl⟩ := (GradeCutLayerCarrier.belowEquiv D P_j j hj hjA _ hjc).surjective z
    have hrow := CanonicalGradeCutSections.lower_row sem j hj hjA hproper a
      ⟨w.1, by simpa only [GradeCutLayerCarrier.embed_cell] using w.2⟩
    have hv := CanonicalFieldLayer.full_source_short
      (CanonicalGradeCutSections.boundaryRows sem j) j (Cell D) (GradeCutBoundary.toCell D j) hj hjA
      (GradeCutBoundary.proper D j hproper) (GradeCutBoundary.grade_bound D j) a
      (by simpa only [CellScheme.scope, GradeCutLayerCarrier.embed_cell] using hsy)
      ⟨w.1, by simpa only [GradeCutLayerCarrier.embed_cell] using w.2⟩
    rw [← hrow] at hv
    exact (congrArg (fun i => Short i _) ((congrArg Prod.snd hi).trans
      (congrArg Prod.snd (GradeCutLayerCarrier.embed_cell D P_j j hj hjA a)))).mpr hv

abbrev normalized {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤) : Prof :=
  CanonicalFieldLayer.encode sem k (Cell D) id hg hp ht

local notation "Norm" => normalized sem k hg

variable {G : Finset ExtOrd} {C : ExtOrd}

def sectionOf {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (G : Finset ExtOrd) (C : ExtOrd) (d : Cell Sch) : ExtOrd :=
  PairedSlotDecoder.decode k (values p) G C (Src (Norm hp ht) d)

local notation "SecOf" => sectionOf sem j hj hjA hproper k hg hk hkA hjk

theorem section_boundary {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) (d : Cell D) :
    SecOf hp ht G C (OCell (LOld d)) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) :
    RespectsSemantics Rws (SecOf hp ht G C) := by
  apply (Dat).decoded_respects (Ctrl (Norm hp ht)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _
    (full_source_short sem j hj hjA hproper k hg hk hkA hjk)
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence LScheme Prof k hk hkA c
    (fun he => hc (congrArg Prod.fst he))
  apply (SeparatedSourceLayerCarrier.base_respects_iff LScheme Prof k hk hkA LSep LSem x _).mpr
  change RespectsSemanticsBelow LSem _ (fun d =>
    PairedSlotDecoder.decode k (values p) G C (Low (Mem (Ctrl (Norm hp ht))) (OCell d.1)))
  simp only [member_controller, lower_old]
  have hx : CellScheme.scope LScheme x ≠ A := by
    simpa only [CellScheme.scope, oldCell, SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index] using hc
  obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D P_j j hj hjA x
    (fun he => hx (congrArg Prod.fst he))
  apply (GradeCutLayerRows.old_respects_iff D P_j j hj hjA hproper sem
    (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) y _).mpr
  change RespectsSemanticsBelow sem (D.cell y) (fun d =>
    PairedSlotDecoder.decode k (values p) G C (LSec (Norm hp ht) (LOld d.1)))
  have hread (d) : PairedSlotDecoder.decode k (values p) G C (LSec (Norm hp ht) (LOld d)) = p d := by
    rw [lowerSection_old sem j hj hjA hproper k]
    exact PairedSlotDecoder.decode_normalize hG hC ht d
  simpa only [hread] using hp.toBelow (D.cell y)

theorem section_bound {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p)
    (ht : ∀ d, p d ≠ ⊤) (hC : SelfVis k C) (hb : ∀ d, p d ≤ C) (d : Cell Sch) :
    SecOf hp ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

theorem section_supported {K : ℕ} (hkK : k ≤ K) (hCG : C ∈ G)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤) (d : Cell Sch) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (SecOf hp ht G C d) :=
  PairedSlotDecoder.decode_supported hkK hCG _

theorem section_agreement {p q : Cell D → ExtOrd}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : ∀ d, p d ≠ ⊤) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis k z) (hC : SelfVis k C) (hh : h ∈ G)
    (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (SecOf hp htp G C) (SecOf hq htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC htp htq hag
  exact (source_agreement sem j hj hjA hproper k hg hk hkA hjk
    (Norm hp htp) (Norm hq htq) heG heAgree).decode
    (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

