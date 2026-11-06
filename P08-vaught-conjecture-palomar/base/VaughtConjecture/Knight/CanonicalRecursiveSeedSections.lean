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

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.CanonicalRecursiveSeedSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalRecursiveSeedRows SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, 3) J) :=
  HighLayerBountiful.equiv (predecessor sem hA) (Profile sem) 3 (by decide) hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, 3) J)
    (p : (predecessor sem hA).below J → ExtOrd) :
    RespectsSemanticsBelow (predecessorRows sem hA hp) J p ↔
      RespectsSemanticsBelow (rows sem hA hp) J (p ∘ (equiv sem hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (predecessor sem hA) (Profile sem) 3 (by decide) hA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem hA hp b.1 d).symm) p
  simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]

def properEquiv (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :
    D.below J ≃ (carrier sem hA).below J :=
  (GradeCutPairCarrier.properEquiv D
    (CanonicalPairBoundary.firstProfiles sem 1 2) (CanonicalPairBoundary.secondProfiles sem 2)
    1 2 (by decide) (CanonicalPairLocalSections.one_le (two_le hA)) (by decide)
    (two_le hA) J hJ).trans (equiv sem hA J (fun h => hJ h.1))

theorem proper_respects_iff (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔ RespectsSemanticsBelow (rows sem hA hp) J
      (p ∘ (properEquiv sem hA J hJ).symm) :=
  (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le (two_le hA)) (by decide) (two_le hA) hp (by decide)
    sem (CanonicalPairLocalSections.smallRows sem (two_le hA) hp) J hJ p).trans
    (respects_iff sem hA hp J (fun h => hJ h.1) _)

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell (carrier sem hA) → ExtOrd} (hread : ∀ d, r (boundary sem hA d) = p d) :
    RespectsSemanticsBelow (rows sem hA hp) J (fun d => r d.1) := by
  let e := properEquiv sem hA J hJ
  have he : (fun d : (carrier sem hA).below J => r d.1) =
      (fun d : D.below J => p d.1) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hread a.1
  rw [he]
  exact (proper_respects_iff sem hA hp J hJ _).mp hpr

theorem full_source_short (c : Cell (carrier sem hA)) (hc : (carrier sem hA).scope c = A)
    (d : (carrier sem hA).below ((carrier sem hA).cell c)) :
    Short ((carrier sem hA).grade c) ((rows sem hA hp).E c d) := by
  by_cases he : (carrier sem hA).cell c = (A, 3)
  · have q := (controllerEquiv sem hA hp).surjective ⟨c, he⟩
    obtain ⟨q, hq⟩ := q
    have hv : (controller sem hA q).1 = c := congrArg Subtype.val hq
    have hr := (data sem hA hp).row_new (controller sem hA q)
    subst c
    rw [hr]
    rw [show (carrier sem hA).grade (controller sem hA q).1 = 3 from
      congrArg Prod.snd (controller sem hA q).2]
    change Short 3 (source sem hA hp q d.1)
    exact source_short sem hA hp q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem hA)
      (Profile sem) 3 (by decide) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem hA hp x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell (predecessor sem hA) (Profile sem)
      3 (by decide) hA (.inl x)
    change Short ((carrier sem hA).grade (old sem hA x)) _
    rw [show (carrier sem hA).grade (old sem hA x) = (predecessor sem hA).grade x
      from congrArg Prod.snd hi]
    exact CanonicalProperOwnerSections.lower_full_short sem 3 (by decide) hA hp x
      ((congrArg Prod.fst hi).symm.trans hc) e

variable {K : ℕ} (hK : 3 ≤ K) {p : Cell D → ExtOrd}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Profile sem := CanonicalRecursiveInventory.encode sem 0
  (hpr.mono (show GradedLe (A, 3) (A, K) from ⟨Finset.Subset.refl _, hK⟩)) ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (carrier sem hA)) : ExtOrd :=
  PairedSlotDecoder.decode 3 (values p) G C (source sem hA hp (normalized sem hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C) (d : Cell D) :
    sectionOf sem hA hp hK hpr ht G C (boundary sem hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C) :
    RespectsSemanticsBelow (rows sem hA hp) (A, K)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
  have hproper (c : Cell (carrier sem hA)) (hc : (carrier sem hA).scope c ≠ A)
      (hg : (carrier sem hA).grade c ≤ K) :
      RespectsSemanticsBelow (rows sem hA hp) ((carrier sem hA).cell c)
        (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
    exact proper_lawful sem hA hp
      (fun ha => hc (Finset.Subset.antisymm
        ((carrier sem hA).isPlan.subset_of_mem ((carrier sem hA).scope_mem_plan c)) ha))
      (hpr.mono ⟨(carrier sem hA).isPlan.subset_of_mem ((carrier sem hA).scope_mem_plan c), hg⟩)
      (section_boundary sem hA hp hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow (rows sem hA hp) (A, 3)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
    apply (data sem hA hp).decoded_respects (controller sem hA (normalized sem hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem hA hp c.1 hc)
    intro c hc
    have he : (carrier sem hA).cell c.1 ≠ (A, 3) := fun he => hc (congrArg Prod.fst he)
    have hr := ((data sem hA hp).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data sem hA hp).base _
      (fun d => PairedSlotDecoder.decode 3 (values p) G C
        ((data sem hA hp).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data sem hA hp).below_old he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : (carrier sem hA).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      hp 3 hA c.1 hc
    exact hl.mono ⟨(carrier sem hA).isPlan.subset_of_mem
      ((carrier sem hA).scope_mem_plan c.1), hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis 3 C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem hA)) : sectionOf sem hA hp hK hpr ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  simpa only [hd] using hb d

theorem section_supported {L : ℕ} (hL : 3 ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis 3 z) (hC : SelfVis 3 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem hA hp hK hpr ht G C) (sectionOf sem hA hp hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_agreement_all sem hA hp
    (normalized sem hK hpr ht) (normalized sem hK hqr htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

end
end VaughtConjecture.Knight.CanonicalRecursiveSeedSections
