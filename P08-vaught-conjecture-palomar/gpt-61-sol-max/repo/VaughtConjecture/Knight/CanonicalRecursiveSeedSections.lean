
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveSeedRows
import VaughtConjecture.Knight.CanonicalProperOwnerSections

/-! # Decoded selected sections on the actual recursive seed

Retained proper owners may exceed grade three. Input lawfulness is required
only through the current outer grade; all original fields remain literal.
The decoded operator includes every seed controller at fixed outer parameters.
This is selected-section supply, not arbitrary-ambient lifting.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveSeedSections
open    SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalRecursiveSeedRows SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card) (hp : AvoidsValue D.scope A)

abbrev equiv J (hJ : ¬ GradedLe (A, 3) J) :=
  HighLayerBountiful.equiv (predecessor sem hA) (Profile sem) 3 (by decide) hA J hJ

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows sem hA hp)

theorem respects_iff J (hJ : ¬ GradedLe (A, 3) J)
    p :
    RespectsSemanticsBelow (predecessorRows sem hA hp) J p ↔
      RespectsSemanticsBelow₀ J (p ∘ (equiv sem hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (predecessor sem hA) (Profile sem) 3 (by decide) hA)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem hA hp b.1 d).symm) p
  simp only [CellScheme.scope,  HighLayerBountiful.equiv_cell]

local notation "carrier₀" => carrier sem hA

def properEquiv (J : GradedIndex ι) (hJ : ¬ A ⊆ J.1) :
    D.below J ≃ (carrier₀).below J :=
  (GradeCutPairCarrier.properEquiv D
    (CanonicalPairBoundary.firstProfiles sem 1 2) (CanonicalPairBoundary.secondProfiles sem 2)
    1 2 (by decide) (CanonicalPairLocalSections.one_le (two_le hA)) (by decide)
    (two_le hA) J hJ).trans (equiv sem hA J (fun h => hJ h.1))

theorem proper_respects_iff (J : GradedIndex ι) (hJ : ¬ A ⊆ J.1)
    p :
    RespectsSemanticsBelow sem J p ↔ RespectsSemanticsBelow₀ J
      (p ∘ (properEquiv sem hA J hJ).symm) :=
  (GradeCutPairRows.proper_respects_iff hp (by decide)
    sem (CanonicalPairLocalSections.smallRows sem (two_le hA) hp) J hJ p).trans
    (respects_iff sem hA hp J (fun h => hJ h.1) _)

local notation "Cell₀" => Cell (carrier sem hA)

theorem proper_lawful {J : GradedIndex ι} (hJ : ¬ A ⊆ J.1) {p : CellLabels D}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell₀ → ExtOrd} (hread : ∀ d, r (boundary sem hA d) = p d) :
    RespectsSemanticsBelow₀ J (fun d => r d.1) := by
  let e := properEquiv sem hA J hJ
  have he : (fun d => r d.1) =
      (fun d => p d.1) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp  
    exact hread a.1
  rw [he]
  exact (proper_respects_iff sem hA hp J hJ _).mp hpr

local notation "data₀" => data sem hA hp

theorem full_source_short (c : Cell₀) (hc : (carrier₀).scope c = A)
    (d : (carrier₀).belowCell c) :
    Short ((carrier₀).grade c) ((rows sem hA hp).E c d) := by
  by_cases he : (carrier₀).cell c = (A, 3)
  · have q := (controllerEquiv sem hA hp).surjective ⟨c, he⟩
    obtain ⟨q, hq⟩ := q
    have hv : (controller sem hA q).1 = c := congrArg Subtype.val hq
    have hr := (data₀).row_new (controller sem hA q)
    subst c
    rw [hr]
    rw [show (carrier₀).grade (controller sem hA q).1 = 3 from
      congrArg Prod.snd (controller sem hA q).2]
    change Short 3 (source sem hA hp q d.1)
    exact source_short sem hA hp q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem hA hp x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell (predecessor sem hA) (Profile sem)
      3 (by decide) hA (.inl x)
    change Short ((carrier₀).grade (old sem hA x)) _
    rw [show (carrier₀).grade (old sem hA x) = (predecessor sem hA).grade x
      from congrArg Prod.snd hi]
    exact CanonicalProperOwnerSections.lower_full_short sem 3 (by decide) hA hp x
      ((congrArg Prod.fst hi).symm.trans hc) e

variable {K : ℕ} (hK : 3 ≤ K) {p : CellLabels D}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : AvoidsValue p ⊤)

abbrev normalized : Profile sem := CanonicalRecursiveInventory.encode sem
  (hpr.mono (show GradedLe (A, 3) (A, K) from ⟨Finset.Subset.refl _, hK⟩)) ht

def sectionOf G C d :=
  PairedSlotDecoder.decode 3 (values p) G C (source sem hA hp (normalized sem hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

local notation "sectionOf₀" => sectionOf sem hA hp hK hpr ht G C

theorem section_boundary (hG : VisibleOn 3 G) (hC : SelfVis 3 C) d :
    sectionOf₀ (boundary sem hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht

theorem section_lawful (hG : VisibleOn 3 G) (hC : SelfVis 3 C) :
    RespectsSemanticsBelow₀ (A, K)
      (fun d => sectionOf₀ d.1) := by
  have hproper (c : Cell₀) (hc : (carrier₀).scope c ≠ A)
      (hg : (carrier₀).grade c ≤ K) :
      RespectsSemanticsBelow₀ ((carrier₀).cell c)
        (fun d => sectionOf₀ d.1) := proper_lawful sem hA hp
      (fun ha => hc (Finset.Subset.antisymm
        ((carrier₀).scope_subset c) ha))
      (hpr.mono ⟨(carrier₀).scope_subset c, hg⟩)
      (section_boundary sem hA hp hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow₀ (A, 3)
      (fun d => sectionOf₀ d.1) := by
    apply (data₀).decoded_respects (controller sem hA (normalized sem hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem hA hp c.1 hc)
    intro c hc
    have he : (carrier₀).cell c.1 ≠ (A, 3) := fun he => hc (congrArg Prod.fst he)
    have hr := ((data₀).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data₀).base _
      (fun d => PairedSlotDecoder.decode 3 (values p) G C
        ((data₀).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data₀).below_old he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : (carrier₀).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      hp 3 hA c.1 hc
    exact hl.mono ⟨(carrier₀).scope_subset c.1, hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis 3 C) (hb : BoundedBy p C)
    d : sectionOf₀ d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  simpa only [hd] using hb d

theorem section_supported {L} (hL : 3 ≤ L) (hCG : C ∈ G)
    d :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : AvoidsValue q ⊤)
    {h} (hG : VisibleOn 3 G) (hC : SelfVis 3 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf₀) (sectionOf sem hA hp hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_agreement_all sem hA hp
    (normalized sem hK hpr ht) (normalized sem hK hqr htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

