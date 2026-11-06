
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalGradeCutSections
import VaughtConjecture.Knight.PairedCoupledSections

/-! # Canonical coupled controller rows over the full field inventory

Retained proper owners may have the upper grade. Separation uses their scope,
not an artificial strict grade bound. The lower full-scope controllers and all
proper owners are retained literally; their source readings are constructed by
the grade-cut section operator on the entire enlarged lower carrier.
-/

namespace VaughtConjecture.Knight.CanonicalMixedGradeLayers

open    SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A)

abbrev lowerScheme := CanonicalGradeCutSections.scheme sem j hj hjA
abbrev lowerSem := CanonicalGradeCutSections.rows sem j hj hjA hproper
abbrev lowerOld := CanonicalGradeCutSections.old sem j hj hjA

variable (k : ℕ) (hg : BoundedBy D.grade k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

local notation "lowerScheme₀" => lowerScheme sem j hj hjA

local notation "toOcc₀" => SourceLayerCarrier.toOcc D (CanonicalGradeCutSections.Profiles sem j) j hj hjA

include hg hjk in
theorem lower_grade d :
    (lowerScheme₀).grade d ≤ k := by
  rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
  cases toOcc₀ d with
  | inl c => exact hg c
  | inr q => exact hjk.le

include hproper hjk in
theorem lower_separated d :
    ¬ GradedLe (A, k) ((lowerScheme₀).cell d) := by
  rw [SourceLayerCarrier.cell_eq]
  cases toOcc₀ d with
  | inl c =>
    intro hc
    exact hproper c (Finset.Subset.antisymm
      (D.scope_subset c) hc.1)
  | inr q => exact fun hc => (not_le_of_gt hjk) hc.2

abbrev upperGrid := sourceGrid k (Fintype.card (Cell D))
abbrev upperCeiling := PairedBoundarySections.ceiling (D := D) k

local notation "upperCeiling₀" => upperCeiling (D := D) k

local notation "upperGrid₀" => upperGrid (D := D) k

local notation "Profile₀₀" => CanonicalFieldLayer.Profile sem k (Cell D) id

abbrev lowerSection (q : Profile₀₀) :
    CellLabels (lowerScheme₀) :=
  CanonicalGradeCutSections.sectionOf sem j hj hjA hproper q.property.1
    q.property.2.2
    (upperGrid₀) (upperCeiling₀)

include hjk in
def grid_lower_visible {h} (hh : h ∈ upperGrid₀) := selfVis_mono (sourceGrid_visible hh) hjk.le

local notation "Profile₀" => CanonicalFieldLayer.Profile sem k (Cell D) id

local notation "grid_lower_visible₀" => grid_lower_visible j k hjk (sourceGrid_endpoint le_rfl)

local notation "lowerSection₀" => lowerSection sem j hj hjA hproper k

local notation "lowerSem₀" => lowerSem sem j hj hjA hproper

include hjk in
theorem lowerSection_lawful q :
    RespectsSemantics (lowerSem₀)
      (lowerSection₀ q) :=
  CanonicalGradeCutSections.section_lawful sem j hj hjA hproper q.property.1 _
    (fun _ hh => grid_lower_visible j k hjk hh)
    (grid_lower_visible₀)

local notation "lowerOld₀" => lowerOld sem j hj hjA

theorem lowerSection_old q d :
    lowerSection₀ q (lowerOld₀ d) = q.val d :=
  CanonicalGradeCutSections.section_old sem j hj hjA hproper q.property.1 _ d

include hjk in
theorem lowerSection_bound q
    d :
    lowerSection₀ q d ≤ upperCeiling₀ :=
  CanonicalGradeCutSections.section_bound sem j hj hjA hproper q.property.1 _
    (grid_lower_visible₀)
    (CanonicalFieldLayer.profile_bound q) d

include hjk in
theorem lowerSection_supported (q : Profile₀₀)
    d :
    OrbitPrefixSupport.Supported k (upperGrid₀ : Set ExtOrd) q.val
      (lowerSection₀ q d) :=
  CanonicalGradeCutSections.section_supported sem j hj hjA hproper q.property.1 _ hjk.le
    (sourceGrid_endpoint le_rfl) d

include hjk in
def lowerSection_short q
    d :=
  PairedCoupledSections.supported_short (fun _ hh => PairedBoundarySections.grid_short k hh)
    (CanonicalFieldLayer.profile_short q)
    (lowerSection_supported sem j hj hjA hproper k hjk q d)

include hjk in
theorem lowerSection_agreement (p q : Profile₀₀)
    {h} (hh : h ∈ upperGrid₀) (hag : Agree p.val q.val h) :
    Agree (lowerSection₀ p)
      (lowerSection₀ q) h :=
  CanonicalGradeCutSections.section_agreement sem j hj hjA hproper p.property.1 _ q.property.1 _
    (fun _ hz => grid_lower_visible j k hjk hz)
    (grid_lower_visible₀) hh
    (PairedBoundarySections.grid_bound k hh) hag

abbrev scheme := SourceLayerCarrier.scheme (lowerScheme₀)
  (Profile₀) k hk hkA

local notation "scheme₀" => scheme sem j hj hjA k hk hkA

abbrev oldCell (d : Cell (lowerScheme₀)) : Cell (scheme₀) :=
  SourceLayerCarrier.toCell (lowerScheme₀)
    (Profile₀) k hk hkA (.inl d)

abbrev controller q :=
  SourceLayerCarrier.controller (lowerScheme₀)
    (Profile₀) k hk hkA q

local notation "lower_separated₀" => lower_separated sem j hj hjA hproper k hjk

def member c :=
  (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme₀)
    (Profile₀) k hk hkA
    (lower_separated₀)).symm c

local notation "controller₀" => controller sem j hj hjA k hk hkA

local notation "member₀" => member sem j hj hjA hproper k hk hkA hjk

theorem member_controller q :
    member₀ (controller₀ q) = q :=
  (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme₀)
    (Profile₀) k hk hkA
    (lower_separated₀)).symm_apply_apply q

abbrev ownerEquiv c :=
  SeparatedSourceLayerCarrier.ownerEquiv (lowerScheme₀)
    (Profile₀) k hk hkA
    (lower_separated₀) c

def lower q
    d :=
  match SourceLayerCarrier.toOcc (lowerScheme₀)
      (Profile₀) k hk hkA d with
  | .inl x => lowerSection₀ q x
  | .inr _ => ⊥

local notation "lower₀" => lower sem j hj hjA hproper k hk hkA

local notation "oldCell₀" => oldCell sem j hj hjA k hk hkA

theorem lower_old q
    d :
    lower₀ q (oldCell₀ d) =
      lowerSection₀ q d := by
  simp  [lower,  ]

def data : SourcePrefixLayer.Data (scheme₀) k (Cell D) where
  base := SeparatedSourceLayerCarrier.base lowerScheme₀
    (Profile₀₀) k hk hkA
    lower_separated₀ lowerSem₀
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc lowerScheme₀
        (Profile₀₀) k hk hkA d with
    | inl x => exact lower_grade sem j hj hjA k hg hjk x
    | inr q => exact le_rfl
  grid := upperGrid₀
  bot_mem := sourceGrid_bot
  ceiling := upperCeiling₀
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := PairedBoundarySections.grid_bound k hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member₀ c).val
  lower c := lower₀
    (member₀ c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence lowerScheme₀
      (Profile₀₀) k hk hkA d hd
    rw [lower_old]
    exact lowerSection_bound sem j hj hjA hproper k hjk _ x
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence lowerScheme₀
      (Profile₀₀) k hk hkA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff
      lower_separated₀ lowerSem₀ x _).mpr
    change RespectsSemanticsBelow lowerSem₀ _ (fun d =>
      lower₀ _ (oldCell₀ d.1))
    simpa only [lower_old] using
      (lowerSection_lawful sem j hj hjA hproper k hjk _).toBelow _
  grid_agreement p q h hh hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence lowerScheme₀
      (Profile₀₀) k hk hkA d hd
    simpa only [lower_old] using
      lowerSection_agreement sem j hj hjA hproper k hjk _ _ hh hag x

local notation "data₀" => data sem j hj hjA hproper k hg hk hkA hjk

abbrev rows := (data₀).rows
abbrev source q :=
  (data₀).profile (controller₀ q)

local notation "source₀" => source sem j hj hjA hproper k hg hk hkA hjk

theorem source_lower q
    d :
    source₀ q (oldCell₀ d) =
      lowerSection₀ q d := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _ (SeparatedSourceLayerCarrier.old_not_full hk hkA
    (lower_separated₀))]
  change lower₀
    (member₀ (controller₀ q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary q d :
    source₀ q
      (oldCell₀ (lowerOld₀ d)) = q.val d := by
  rw [source_lower, lowerSection_old sem j hj hjA hproper k]

local notation "ownerEquiv₀" => ownerEquiv sem j hj hjA hproper k hk hkA hjk

local notation "rows₀" => rows sem j hj hjA hproper k hg hk hkA hjk

theorem inherited_row c
    d :
    (rows₀).E (oldCell₀ c)
      (ownerEquiv₀ c d) =
      (lowerSem₀).E c d := by
  rw [SourcePrefixLayer.Data.row_old _ (SeparatedSourceLayerCarrier.old_not_full hk hkA
    (lower_separated₀))]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d

theorem inherited_order : StrictMono (oldCell₀) :=
  SourceLayerCarrier.old_order

theorem original_row c d :
    (rows₀).E
      (oldCell₀ (lowerOld₀ c))
      (ownerEquiv₀ (lowerOld₀ c)
        (GradeCutLayerCarrier.ownerEquiv hj hjA hproper c d)) = sem.E c d := by
  rw [inherited_row]
  exact CanonicalGradeCutSections.old_row sem j hj hjA hproper c d

theorem consistent (hs : sem.IsConsistent) :
    (rows₀).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme₀)
    (Profile₀) k hk hkA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff
    (lower_separated₀) (lowerSem₀) x _).mpr
  have he : (data₀).base.E
      (oldCell₀ x) ∘ ownerEquiv₀ x =
      (lowerSem₀).E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d
  rw [he]
  exact CanonicalGradeCutSections.consistent sem j hj hjA hproper hs x

theorem source_agreement (p q : Profile₀₀)
    {h} (hh : h ∈ upperGrid₀) (hag : Agree p.val q.val h) :
    Agree (source₀ p)
      (source₀ q) h := by
  apply (data₀).profile_prefix hh
  change Agree (member₀
      (controller₀ p)).val
    (member₀ (controller₀ q)).val h
  simpa only [member_controller] using hag

variable {sem j hj hjA hproper k hg hk hkA hjk} in
theorem source_supported (q : Profile₀₀)
    d :
    OrbitPrefixSupport.Supported k (upperGrid₀ : Set ExtOrd) q.val
      (source₀ q d) := by
  by_cases hd : (scheme₀).cell d = (A, k)
  · have he := (data₀).profile_new
      (controller₀ q) ⟨d, hd⟩
    apply Or.inr
    apply Or.inl
    change (data₀).profile
      (controller₀ q) d ∈ upperGrid₀
    rw [he]
    exact cut_mem (sourceGrid_bot) _ _
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme₀)
      (Profile₀₀) k hk hkA d hd
    rw [source_lower]
    exact lowerSection_supported sem j hj hjA hproper k hjk q x

theorem source_short q
    d :
    Short k (source₀ q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => PairedBoundarySections.grid_short k hh)
    (CanonicalFieldLayer.profile_short q)
    (source_supported q d)

theorem lower_full_short c
    (hc : (lowerScheme₀).scope c = A)
    d :
    Short ((lowerScheme₀).grade c)
      ((lowerSem₀).E c d) := by
  have hjc : (lowerScheme₀).grade c ≤ j := by
    have hs := hc
    rw [CellScheme.scope, SourceLayerCarrier.cell_eq] at hs
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases he : toOcc₀ c with
    | inl a =>
      rw [he] at hs
      exact (hproper a hs).elim
    | inr q => exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutLayerCarrier.exhaustive D
    (CanonicalGradeCutSections.Profiles sem j) j hj hjA c hjc
  obtain ⟨e, rfl⟩ := (GradeCutLayerCarrier.belowEquiv _ hjc).surjective d
  have he := CanonicalGradeCutSections.lower_row sem j hj hjA hproper a
    ⟨e.1, by simpa only [GradeCutLayerCarrier.embed_cell] using e.2⟩
  have hv := CanonicalFieldLayer.full_source_short
    (GradeCutBoundary.proper hproper) GradeCutBoundary.grade_bound a
    (by simpa only [CellScheme.scope, GradeCutLayerCarrier.embed_cell] using hc)
    ⟨e.1, by grind⟩
  rw [← he] at hv
  exact (congrArg (fun i => Short i _) (congrArg Prod.snd
    (GradeCutLayerCarrier.embed_cell D (CanonicalGradeCutSections.Profiles sem j)
      j hj hjA a))).mpr hv

theorem lower_proper_respects {p : CellLabels D} (hp : RespectsSemantics sem p)
    {r : CellLabels (lowerScheme₀)}
    (hread : ∀ d, r (lowerOld₀ d) = p d)
    (c : Cell (lowerScheme₀)) (hc : (lowerScheme₀).scope c ≠ A) :
    RespectsSemanticsBelow (lowerSem₀)
      ((lowerScheme₀).cell c) (fun d => r d.1) := by
  have hc' : (lowerScheme₀).cell c ≠ (A, j) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D
    (CanonicalGradeCutSections.Profiles sem j) j hj hjA c hc'
  apply (GradeCutLayerRows.old_respects_iff x _).mpr
  change Semantics.RowLawful sem x (fun d => r (lowerOld₀ d.1))
  simpa only [hread] using hp.toBelow (D.cell x)

theorem full_source_short c
    (hc : (scheme₀).scope c = A)
    d :
    Short ((scheme₀).grade c)
      ((rows₀).E c d) := by
  apply (data₀).full_source_short
    (fun _ hh => PairedBoundarySections.grid_short k hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme₀)
      (Profile₀) k hk hkA x hx
    change Short k (lower₀ _
      (oldCell₀ y))
    rw [lower_old]
    exact lowerSection_short sem j hj hjA hproper k hjk _ y
  · intro x hs hx e
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme₀)
      (Profile₀) k hk hkA x hx
    obtain ⟨z, rfl⟩ := (ownerEquiv₀ y).surjective e
    have he := SeparatedSourceLayerCarrier.base_old (lowerScheme₀)
      (Profile₀) k hk hkA
      (lower_separated₀) (lowerSem₀) z
    change (data₀).base.E _ _ = _ at he
    rw [he]
    have hi := SourceLayerCarrier.cell_toCell (lowerScheme₀)
      (Profile₀) k hk hkA (.inl y)
    
    rw [show (scheme₀).grade (oldCell₀ y) =
      (lowerScheme₀).grade y from congrArg Prod.snd hi]
    exact lower_full_short sem j hj hjA hproper y
      ((congrArg Prod.fst hi).symm.trans hs) z

abbrev normalized {p} (hp : RespectsSemantics sem p)
    (ht : AvoidsValue p ⊤) : Profile₀ :=
  CanonicalFieldLayer.encode hg hp ht

variable {G : Finset ExtOrd} {C : ExtOrd}

local notation "normalized₀" => normalized sem k hg

/-- The new selected section decodes the complete coupled source, including
all retained lower controllers. Lower sections are not supplied as parameters. -/
def sectionOf {p} (hp : RespectsSemantics sem p)
    (ht : AvoidsValue p ⊤) G C
    d :=
  PairedSlotDecoder.decode k (values p) G C
    (source₀ (normalized₀ hp ht) d)

local notation "sectionOf₀" => sectionOf sem j hj hjA hproper k hg hk hkA hjk

theorem section_boundary {p} (hp : RespectsSemantics sem p)
    (ht : AvoidsValue p ⊤) (hG : VisibleOn k G) (hC : SelfVis k C) d :
    sectionOf₀ hp ht G C
      (oldCell₀ (lowerOld₀ d)) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht

theorem section_lawful {p : CellLabels D} (hp : RespectsSemantics sem p)
    (ht : AvoidsValue p ⊤) (hG : VisibleOn k G) (hC : SelfVis k C) :
    RespectsSemantics (rows₀)
      (sectionOf₀ hp ht G C) := by
  apply (data₀).decoded_respects
    (controller₀ (normalized₀ hp ht)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _
    (full_source_short sem j hj hjA hproper k hg hk hkA hjk)
  intro c hc
  have hc' : (scheme₀).cell c ≠ (A, k) :=
    fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (lowerScheme₀)
    (Profile₀) k hk hkA c hc'
  apply (SeparatedSourceLayerCarrier.base_respects_iff
    (lower_separated₀) (lowerSem₀) x _).mpr
  change RespectsSemanticsBelow (lowerSem₀) _ (fun d =>
    PairedSlotDecoder.decode k (values p) G C
      (lower₀
        (member₀
          (controller₀ (normalized₀ hp ht)))
        (oldCell₀ d.1)))
  simp  [member_controller, lower_old]
  apply lower_proper_respects sem j hj hjA hproper hp
    (r := fun y => PairedSlotDecoder.decode k (values p) G C
      (lowerSection₀ (normalized₀ hp ht) y)) _ x
    (by simpa only [CellScheme.scope,  SourceLayerCarrier.cell_toCell,
      SourceLayerCarrier.index] using hc)
  intro d
  rw [lowerSection_old sem j hj hjA hproper k]
  exact PairedSlotDecoder.decode_normalize hG hC ht

theorem section_bound {p} (hp : RespectsSemantics sem p)
    (ht : AvoidsValue p ⊤) (hC : SelfVis k C) (hb : BoundedBy p C)
    d :
    sectionOf₀ hp ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

theorem section_supported {K} (hkK : k ≤ K) (hCG : C ∈ G)
    {p} (hp : RespectsSemantics sem p) (ht : AvoidsValue p ⊤)
    d :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf₀ hp ht G C d) :=
  PairedSlotDecoder.decode_supported hkK hCG _

theorem section_agreement {p q}
    (hp : RespectsSemantics sem p) (hq : RespectsSemantics sem q)
    (htp : AvoidsValue p ⊤) (htq : AvoidsValue q ⊤)
    {h} (hG : VisibleOn k G)
    (hC : SelfVis k C) (hh : h ∈ G)
    (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf₀ hp htp G C)
      (sectionOf₀ hq htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC htp htq hag
  have hs := source_agreement sem j hj hjA hproper k hg hk hkA hjk
    (normalized₀ hp htp) (normalized₀ hq htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

