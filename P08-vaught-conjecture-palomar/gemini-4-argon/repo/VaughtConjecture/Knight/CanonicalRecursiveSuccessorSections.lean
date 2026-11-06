/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows

/-! # Preservation of the recursive selected-section contract

Construct the next decoder on the actual successor, and recover the same
lawfulness, literal readback, boundedness, support and whole-coordinate
agreement properties. This does not assert arbitrary-ambient lifting.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison CanonicalRecursiveSuccessorRows SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

local notation "pred" => predecessor sem n hA
local notation "Prof" => Profile sem n
local notation "K" => carrier sem n hA
local notation "Rws" => rows sem n hA hp P
local notation "dat" => data sem n hA hp P
local notation "src" => source sem n hA hp P
local notation "bdry" => boundary sem n hA
local notation "oldC" => old sem n hA
local notation "ctrl" => controller sem n hA
local notation "cEq" => controllerEquiv sem n hA hp
local notation "oEq" => ownerEquiv sem n hA hp
local notation "pos4" => Nat.succ_pos (n + 3)

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, n + 4) J) :=
  HighLayerBountiful.equiv pred Prof (n + 4) pos4 hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, n + 4) J)
    (p : CellScheme.below pred J → ExtOrd) :
    RespectsSemanticsBelow P.rows J p ↔
      RespectsSemanticsBelow Rws J (p ∘ (equiv sem n hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem n hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell pred Prof (n + 4) pos4 hA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem n hA hp P b.1 d).symm) p
  simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell K → ExtOrd} (hread : ∀ d, r (bdry d) = p d) :
    RespectsSemanticsBelow Rws J (fun d => r d.1) := by
  have hl := P.proper_lawful hJ hpr (r := fun d => r (oldC d)) hread
  let e := equiv sem n hA J (fun h => hJ h.1)
  have he : (fun d : CellScheme.below K J => r d.1) =
      (fun d : CellScheme.below pred J => r (oldC d.1)) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]; rfl
  rw [he]
  exact (respects_iff sem n hA hp P J (fun h => hJ h.1) _).mp hl

theorem full_source_short (c : Cell K) (hc : CellScheme.scope K c = A)
    (d : CellScheme.below K (CellScheme.cell K c)) :
    Short (CellScheme.grade K c) (Semantics.E Rws c d) := by
  by_cases he : CellScheme.cell K c = (A, n + 4)
  · obtain ⟨q, hq⟩ := (Equiv.surjective cEq) ⟨c, he⟩
    have hv : (ctrl q).1 = c := congrArg Subtype.val hq
    have hr := ScopedSourcePrefixLayer.Data.row_new dat (ctrl q)
    subst c
    rw [hr, show CellScheme.grade K (ctrl q).1 = n + 4 from congrArg Prod.snd (ctrl q).2]
    exact source_short sem n hA hp P q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA c he
    obtain ⟨e, rfl⟩ := (Equiv.surjective (oEq x)) d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell pred Prof (n + 4) pos4 hA (.inl x)
    change Short (CellScheme.grade K (oldC x)) _
    rw [show CellScheme.grade K (oldC x) = CellScheme.grade pred x from congrArg Prod.snd hi]
    exact P.full_short x ((congrArg Prod.fst hi).symm.trans hc) e

variable {M : ℕ} (hK : n + 4 ≤ M) {p : Cell D → ExtOrd}
  (hpr : RespectsSemanticsBelow sem (A, M) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Prof := CanonicalRecursiveInventory.encode sem (n + 1)
  (hpr.mono (show GradedLe (A, n + 4) (A, M) from ⟨le_rfl, hK⟩)) ht

abbrev sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell K) : ExtOrd :=
  PairedSlotDecoder.decode (n + 4) (values p) G C (src (normalized sem n hK hpr ht) d)

local notation "secOf" => sectionOf sem n hA hp P

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hC : SelfVis (n + 4) C) (d : Cell D) :
    secOf hK hpr ht G C (bdry d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis (n + 4) z) (hC : SelfVis (n + 4) C) :
    RespectsSemanticsBelow Rws (A, M) (fun d => secOf hK hpr ht G C d.1) := by
  have hproper (c : Cell K) (hc : CellScheme.scope K c ≠ A) (hg : CellScheme.grade K c ≤ M) :
      RespectsSemanticsBelow Rws (CellScheme.cell K c) (fun d => secOf hK hpr ht G C d.1) :=
    proper_lawful sem n hA hp P
      (fun ha => hc (Finset.Subset.antisymm ((CellScheme.isPlan K).subset_of_mem (CellScheme.scope_mem_plan K c)) ha))
      (hpr.mono ⟨(CellScheme.isPlan K).subset_of_mem (CellScheme.scope_mem_plan K c), hg⟩)
      (section_boundary sem n hA hp P hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow Rws (A, n + 4) (fun d => secOf hK hpr ht G C d.1) := by
    apply ScopedSourcePrefixLayer.Data.decoded_respects dat (ctrl (normalized sem n hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem n hA hp P c.1 hc)
    intro c hc
    have he : CellScheme.cell K c.1 ≠ (A, n + 4) := fun he => hc (congrArg Prod.fst he)
    have hr := (ScopedSourcePrefixLayer.Data.old_respects_iff dat he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (ScopedSourcePrefixLayer.Data.base dat) _
      (fun d => PairedSlotDecoder.decode (n + 4) (values p) G C
        (ScopedSourcePrefixLayer.Data.profile dat _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      (ScopedSourcePrefixLayer.Data.below_old dat he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : CellScheme.scope K c.1 = A
  · exact hl.mono ⟨(CellScheme.isPlan K).subset_of_mem (CellScheme.scope_mem_plan K c.1),
      RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem) hp (n + 4) hA c.1 hc⟩
  · exact hproper c.1 hc c.2.2

def successor : CanonicalRecursiveContract.State sem (n + 1) hA where
  rows := Rws
  consistent := consistent sem n hA hp P
  proper_lawful := proper_lawful sem n hA hp P
  full_short := full_source_short sem n hA hp P
  sectionOf := secOf
  section_boundary := section_boundary sem n hA hp P
  section_lawful := section_lawful sem n hA hp P
  section_bound := by
    intro _ _ _ _ _ _ _ hC hb _
    apply PairedSlotDecoder.decode_le hC; intro _ ha
    obtain ⟨d, hd⟩ := mem_values.mp ha; simpa only [hd] using hb d
  section_supported := by
    intro _ _ _ _ _ _ _ _ hL hCG _
    exact PairedSlotDecoder.decode_supported hL hCG _
  section_agreement := by
    intro _ hK _ _ hpr htp hqr htq _ _ _ hG hC hh hhC hag
    obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
      largestCommonCut_spec hG hC hC hh hhC hhC htp htq hag
    exact (source_agreement_all sem n hA hp P (normalized sem n hK hpr htp)
      (normalized sem n hK hqr htq) heG heAgree).decode
      (PairedSlotDecoder.decode_witness hG hC).mono (PairedSlotDecoder.decode_witness hG hC).mono
      hpReach hqReach fun _ _ => hcompare _
