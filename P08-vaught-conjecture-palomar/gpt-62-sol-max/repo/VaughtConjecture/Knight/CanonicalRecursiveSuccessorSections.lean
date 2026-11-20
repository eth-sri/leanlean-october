/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections

open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison

open CanonicalRecursiveSuccessorRows SharpWitnessComposition

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

theorem boundary_row : (CanonicalRecursiveInventory.patch sem S.proper (n + 3) hA).Preserves sem (rows S) := by
  intro c d
  let e := (CanonicalRecursiveInventory.patch sem S.proper (n + 2) (Nat.le_of_succ_le hA)).ownerEquiv c d
  exact (inherited_row S _ e).trans (S.prev.row c d)

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell (carrier sem n hA) → ExtOrd}
    (hread : ∀ d, r (boundary sem n hA d) = p d) :
    RespectsSemanticsBelow (rows S) J (fun d => r d.1) := by
  exact (CanonicalRecursiveInventory.patch sem S.proper (n + 3) hA).respects (boundary_row S) J
    (CanonicalRecursiveInventory.proper_below sem (n + 3) hA J hJ) hpr hread

theorem full_source_short (c : Cell (carrier sem n hA)) (hc : (carrier sem n hA).scope c = A)
    (d : (carrier sem n hA).below ((carrier sem n hA).cell c)) :
    Short ((carrier sem n hA).grade c) ((rows S).E c d) := by
  by_cases he : (carrier sem n hA).cell c = (A, (n + 3))
  · have q := (controllerEquiv sem n hA S.proper).surjective ⟨c, he⟩
    obtain ⟨q, hq⟩ := q
    have hv : (controller sem n hA q).1 = c := congrArg Subtype.val hq
    have hr := (data S).row_new (controller sem n hA q)
    subst c
    rw [hr]
    rw [show (carrier sem n hA).grade (controller sem n hA q).1 = (n + 3) from
      congrArg Prod.snd (by assumption)]
    change Short (n + 3) (source S q d.1)
    apply source_short
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem n hA)
      (Profile sem n) (n + 3) (by norm_num) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem n hA S.proper x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell (predecessor sem n hA) (Profile sem n)
      (n + 3) (by norm_num) hA (.inl x)
    change Short ((carrier sem n hA).grade (old sem n hA x)) _
    rw [show (carrier sem n hA).grade (old sem n hA x) = (predecessor sem n hA).grade x
      from congrArg Prod.snd hi]
    exact S.prev.full_short x (by simp_all!) e

variable {K : ℕ} (hK : (n + 3) ≤ K) {p : Cell D → ExtOrd}

variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Profile sem n := CanonicalRecursiveInventory.encode sem n
  (hpr.mono (by trivial)) ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (carrier sem n hA)) : ExtOrd :=
  PairedSlotDecoder.decode (n + 3) (values p) G C
    (source S (normalized hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hC : SelfVis (n + 3) C) (d : Cell D) :
    sectionOf S hK hpr ht G C (boundary sem n hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hC : SelfVis (n + 3) C) :
    RespectsSemanticsBelow (rows S) (A, K)
      (fun d => sectionOf S hK hpr ht G C d.1) := by
  have hproper (c : Cell (carrier sem n hA)) (hc : (carrier sem n hA).scope c ≠ A)
      (hg : (carrier sem n hA).grade c ≤ K) :
      RespectsSemanticsBelow (rows S) ((carrier sem n hA).cell c)
        (fun d => sectionOf S hK hpr ht G C d.1) := by
    exact proper_lawful S
      (fun ha => hc (Finset.Subset.antisymm
        ((carrier sem n hA).scope_subset c) ha))
      (hpr.mono ⟨(carrier sem n hA).scope_subset c, hg⟩)
      (by solve_by_elim [section_boundary])
  have hl : RespectsSemanticsBelow (rows S) (A, (n + 3))
      (fun d => sectionOf S hK hpr ht G C d.1) := by
    apply (data S).decoded_respects (controller sem n hA (normalized hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (by grind [full_source_short])
    intro c hc
    have he : (carrier sem n hA).cell c.1 ≠ (A, (n + 3)) := (by simp_all)
    have hr := ((data S).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data S).base _
      (fun d => PairedSlotDecoder.decode (n + 3) (values p) G C
        ((data S).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data S).below_old he _)] using hr
  apply RespectsSemanticsBelow.of_local
  intro c
  by_cases hc : (carrier sem n hA).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      S.proper (n + 3) hA c.1 hc
    exact hl.mono ⟨by simp_all, hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis (n + 3) C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem n hA)) : sectionOf S hK hpr ht G C d ≤ C := by
  exact PairedSlotDecoder.decode_le_of_bound hC hb _

theorem section_supported {L : ℕ} (hL : (n + 3) ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem n hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf S hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis (n + 3) z) (hC : SelfVis (n + 3) C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf S hK hpr ht G C) (sectionOf S hK hqr htq G C) h := by
  exact decode_agreement hG hC hh hhC ht htq hag
    (fun _ he ha => source_agreement_all S _ _ he ha)

/-- The semantic successor returns precisely the selected-section contract it
consumes. In particular no future selected section is a residual assumption. -/
def successor : CanonicalRecursiveContract.Stage sem (n + 1) hA where
  rows := rows S
  consistent := consistent S
  row := boundary_row S
  full_short := full_source_short S
  sectionOf := sectionOf S
  section_boundary := section_boundary S
  section_lawful := section_lawful S
  section_bound := section_bound S
  section_supported := section_supported S
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    section_agreement S hK hpr htp hqr htq

end

end VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections
