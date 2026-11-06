/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSeedRows
public import VaughtConjecture.Knight.CanonicalProperOwnerSections

/-! # Decoded selected sections on the actual recursive seed

Retained proper owners may exceed grade three. Input lawfulness is required
only through the current outer grade; all original fields remain literal.
The decoded operator includes every seed controller at fixed outer parameters.
This is selected-section supply, not arbitrary-ambient lifting.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveSeedSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison CanonicalRecursiveSeedRows SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)

local notation "pred" => predecessor sem hA
local notation "pRows" => predecessorRows sem hA hp
local notation "Prof" => Profile sem
local notation "K" => carrier sem hA
local notation "Rws" => rows sem hA hp
local notation "dat" => data sem hA hp
local notation "src" => source sem hA hp
local notation "bdry" => boundary sem hA
local notation "oldC" => old sem hA
local notation "ctrl" => controller sem hA
local notation "cEq" => controllerEquiv sem hA hp
local notation "oEq" => ownerEquiv sem hA hp
local notation "pos3" => Nat.succ_pos 2

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, 3) J) :=
  HighLayerBountiful.equiv pred Prof 3 pos3 hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, 3) J)
    (p : CellScheme.below pred J → ExtOrd) :
    RespectsSemanticsBelow pRows J p ↔
      RespectsSemanticsBelow Rws J (p ∘ (equiv sem hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell pred Prof 3 pos3 hA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem hA hp b.1 d).symm) p
  simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]

def properEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) : D.below J ≃ CellScheme.below K J :=
  (GradeCutPairCarrier.properEquiv D
    (CanonicalPairBoundary.firstProfiles sem 1 2) (CanonicalPairBoundary.secondProfiles sem 2)
    1 2 (by decide) (CanonicalPairLocalSections.one_le (two_le hA)) (by decide)
    (two_le hA) J hJ).trans (equiv sem hA J (fun h => hJ h.1))

theorem proper_respects_iff (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow Rws J (p ∘ (properEquiv sem hA J hJ).symm) :=
  (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le (two_le hA)) (by decide) (two_le hA) hp (by decide)
    sem (CanonicalPairLocalSections.smallRows sem (two_le hA) hp) J hJ p).trans
    (respects_iff sem hA hp J (fun h => hJ h.1) _)

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell K → ExtOrd} (hread : ∀ d, r (bdry d) = p d) :
    RespectsSemanticsBelow Rws J (fun d => r d.1) := by
  let e := properEquiv sem hA J hJ
  have he : (fun d : CellScheme.below K J => r d.1) = (fun d : D.below J => p d.1) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hread a.1
  rw [he]
  exact (proper_respects_iff sem hA hp J hJ _).mp hpr

theorem full_source_short (c : Cell K) (hc : CellScheme.scope K c = A)
    (d : CellScheme.below K (CellScheme.cell K c)) :
    Short (CellScheme.grade K c) (Semantics.E Rws c d) := by
  by_cases he : CellScheme.cell K c = (A, 3)
  · obtain ⟨q, hq⟩ := (Equiv.surjective cEq) ⟨c, he⟩
    have hv : (ctrl q).1 = c := congrArg Subtype.val hq
    have hr := ScopedSourcePrefixLayer.Data.row_new dat (ctrl q)
    subst c
    rw [hr, show CellScheme.grade K (ctrl q).1 = 3 from congrArg Prod.snd (ctrl q).2]
    exact source_short sem hA hp q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA c he
    obtain ⟨e, rfl⟩ := (Equiv.surjective (oEq x)) d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell pred Prof 3 pos3 hA (.inl x)
    change Short (CellScheme.grade K (oldC x)) _
    rw [show CellScheme.grade K (oldC x) = CellScheme.grade pred x from congrArg Prod.snd hi]
    exact CanonicalProperOwnerSections.lower_full_short sem 3 (by decide) hA hp x
      ((congrArg Prod.fst hi).symm.trans hc) e

variable {M : ℕ} (hK : 3 ≤ M) {p : Cell D → ExtOrd}
  (hpr : RespectsSemanticsBelow sem (A, M) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Prof := CanonicalRecursiveInventory.encode sem 0
  (hpr.mono (show GradedLe (A, 3) (A, M) from ⟨le_rfl, hK⟩)) ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell K) : ExtOrd :=
  PairedSlotDecoder.decode 3 (values p) G C (src (normalized sem hK hpr ht) d)

local notation "secOf" => sectionOf sem hA hp

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C) (d : Cell D) :
    secOf hK hpr ht G C (bdry d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C) :
    RespectsSemanticsBelow Rws (A, M) (fun d => secOf hK hpr ht G C d.1) := by
  have hproper (c : Cell K) (hc : CellScheme.scope K c ≠ A) (hg : CellScheme.grade K c ≤ M) :
      RespectsSemanticsBelow Rws (CellScheme.cell K c) (fun d => secOf hK hpr ht G C d.1) :=
    proper_lawful sem hA hp
      (fun ha => hc (Finset.Subset.antisymm ((CellScheme.isPlan K).subset_of_mem (CellScheme.scope_mem_plan K c)) ha))
      (hpr.mono ⟨(CellScheme.isPlan K).subset_of_mem (CellScheme.scope_mem_plan K c), hg⟩)
      (section_boundary sem hA hp hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow Rws (A, 3) (fun d => secOf hK hpr ht G C d.1) := by
    apply ScopedSourcePrefixLayer.Data.decoded_respects dat (ctrl (normalized sem hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem hA hp c.1 hc)
    intro c hc
    have he : CellScheme.cell K c.1 ≠ (A, 3) := fun he => hc (congrArg Prod.fst he)
    have hr := (ScopedSourcePrefixLayer.Data.old_respects_iff dat he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (ScopedSourcePrefixLayer.Data.base dat) _
      (fun d => PairedSlotDecoder.decode 3 (values p) G C
        (ScopedSourcePrefixLayer.Data.profile dat _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      (ScopedSourcePrefixLayer.Data.below_old dat he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : CellScheme.scope K c.1 = A
  · exact hl.mono ⟨(CellScheme.isPlan K).subset_of_mem (CellScheme.scope_mem_plan K c.1),
      RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem) hp 3 hA c.1 hc⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis 3 C) (hb : ∀ d, p d ≤ C) (d : Cell K) :
    secOf hK hpr ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC; intro _ ha
  obtain ⟨d, hd⟩ := mem_values.mp ha; simpa only [hd] using hb d

theorem section_supported {L : ℕ} (hL : 3 ≤ L) (hCG : C ∈ G) (d : Cell K) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (secOf hK hpr ht G C d) :=
  PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, M) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (secOf hK hpr ht G C) (secOf hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  exact (source_agreement_all sem hA hp (normalized sem hK hpr ht)
    (normalized sem hK hqr htq) heG heAgree).decode
    (PairedSlotDecoder.decode_witness hG hC).mono (PairedSlotDecoder.decode_witness hG hC).mono
    hpReach hqReach fun _ _ => hcompare _
