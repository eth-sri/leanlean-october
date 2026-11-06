
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows

/-! # Preservation of the recursive selected-section contract

Construct the next decoder on the actual successor, and recover the same
lawfulness, literal readback, boundedness, support and whole-coordinate
agreement properties. This does not assert arbitrary-ambient lifting.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections
open    SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalRecursiveSuccessorRows SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : ∀ d , D.scope d ≠ A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

local notation "GradedLe₀" => GradedLe (A, (n + 4))

local notation "predecessor₀" => predecessor sem n hA

abbrev equiv J (hJ : ¬ GradedLe₀ J) :=
  HighLayerBountiful.equiv (predecessor₀) (Profile sem n)
    (n + 4) (Nat.succ_pos (n + 3)) hA J hJ

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows sem n hA hp P)

theorem respects_iff J (hJ : ¬ GradedLe₀ J)
    p :
    RespectsSemanticsBelow P.rows J p ↔
      RespectsSemanticsBelow₀ J (p ∘ (equiv sem n hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem n hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      predecessor₀ (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row b.1 d).symm) p
  simp only [CellScheme.scope,  HighLayerBountiful.equiv_cell]

local notation "carrier₀" => carrier sem n hA

theorem proper_lawful {J : GradedIndex ι} (hJ : ¬ A ⊆ J.1) {p : CellLabels D}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : CellLabels (carrier₀)}
    (hread : ∀ d, r (boundary sem n hA d) = p d) :
    RespectsSemanticsBelow₀ J (fun d => r d.1) := by
  have hl := P.proper_lawful hJ hpr (r := fun d => r (old sem n hA d)) hread
  let e := equiv sem n hA J (fun h => hJ h.1)
  have he : (fun d => r d.1) =
      (fun d => r (old sem n hA d.1)) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp  
    rfl
  rw [he]
  exact (respects_iff sem n hA hp P J (fun h => hJ h.1) _).mp hl

local notation "controller₀" => controller sem n hA

local notation "data₀" => data sem n hA hp P

theorem full_source_short c (hc : (carrier₀).scope c = A)
    d :
    Short ((carrier₀).grade c) ((rows sem n hA hp P).E c d) := by
  by_cases he : (carrier₀).cell c = (A, (n + 4))
  · have q := (controllerEquiv sem n hA hp).surjective ⟨c, he⟩
    obtain ⟨q, hq⟩ := q
    have hv : (controller₀ q).1 = c := congrArg Subtype.val hq
    have hr := (data₀).row_new (controller₀ q)
    subst c
    rw [hr]
    rw [show (carrier₀).grade (controller₀ q).1 = (n + 4) from
      congrArg Prod.snd (controller₀ q).2]
    change Short (n + 4) (source sem n hA hp P q d.1)
    exact source_short sem n hA hp P q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence predecessor₀
      (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem n hA hp x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell predecessor₀ (Profile sem n)
      (n + 4) (Nat.succ_pos (n + 3)) hA (.inl x)
    change Short ((carrier₀).grade (old sem n hA x)) _
    rw [show (carrier₀).grade (old sem n hA x) = (predecessor₀).grade x
      from congrArg Prod.snd hi]
    exact P.full_short x ((congrArg Prod.fst hi).symm.trans hc) e

variable {K : ℕ} (hK : (n + 4) ≤ K) {p : CellLabels D}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Profile sem n := CanonicalRecursiveInventory.encode sem
  (hpr.mono (show GradedLe₀ (A, K) from ⟨Finset.Subset.refl _, hK⟩)) ht

def sectionOf G C d :=
  PairedSlotDecoder.decode (n + 4) (values p) G C
    (source sem n hA hp P (normalized sem n hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

local notation "SelfVis₀" => SelfVis (n + 4)

local notation "sectionOf₀" => sectionOf sem n hA hp P hK hpr ht G C

theorem section_boundary (hG : ∀ z ∈ G, SelfVis₀ z) (hC : SelfVis₀ C) d :
    sectionOf₀ (boundary sem n hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht

theorem section_lawful (hG : ∀ z ∈ G, SelfVis₀ z) (hC : SelfVis₀ C) :
    RespectsSemanticsBelow₀ (A, K)
      (fun d => sectionOf₀ d.1) := by
  have hproper (c : Cell carrier₀) (hc : (carrier₀).scope c ≠ A)
      (hg : (carrier₀).grade c ≤ K) :
      RespectsSemanticsBelow₀ ((carrier₀).cell c)
        (fun d => sectionOf₀ d.1) := proper_lawful sem n hA hp P
      (fun ha => hc (Finset.Subset.antisymm
        ((carrier₀).scope_subset c) ha))
      (hpr.mono ⟨(carrier₀).scope_subset c, hg⟩)
      (section_boundary sem n hA hp P hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow₀ (A, (n + 4))
      (fun d => sectionOf₀ d.1) := by
    apply (data₀).decoded_respects (controller₀ (normalized sem n hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem n hA hp P c.1 hc)
    intro c hc
    have he : (carrier₀).cell c.1 ≠ (A, (n + 4)) := fun he => hc (congrArg Prod.fst he)
    have hr := ((data₀).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data₀).base _
      (fun d => PairedSlotDecoder.decode (n + 4) (values p) G C
        ((data₀).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data₀).below_old he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : (carrier₀).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      hp (n + 4) hA c.1 hc
    exact hl.mono ⟨(carrier₀).scope_subset c.1, hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis₀ C) (hb : BoundedBy p C)
    d : sectionOf₀ d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  simpa only [hd] using hb d

theorem section_supported {L} (hL : (n + 4) ≤ L) (hCG : C ∈ G)
    d :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem n hA hp P hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : AvoidsValue q ⊤)
    {h} (hG : ∀ z ∈ G, SelfVis₀ z) (hC : SelfVis₀ C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf₀) (sectionOf sem n hA hp P hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_agreement_all sem n hA hp P
    (normalized sem n hK hpr ht) (normalized sem n hK hqr htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

/-- The semantic successor returns precisely the selected-section contract it
consumes. In particular no future selected section is a residual assumption. -/
def successor : CanonicalRecursiveContract.State sem (n + 1) hA where
  rows := rows sem n hA hp P
  consistent := consistent sem n hA hp P
  proper_lawful := proper_lawful sem n hA hp P
  full_short := full_source_short sem n hA hp P
  sectionOf := sectionOf sem n hA hp P
  section_boundary := section_boundary sem n hA hp P
  section_lawful := section_lawful sem n hA hp P
  section_bound := section_bound sem n hA hp P
  section_supported := section_supported sem n hA hp P
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    section_agreement sem n hA hp P hK hpr htp hqr htq

