/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedProfiles
public import VaughtConjecture.Knight.PairedCoupledSections

public import VaughtConjecture.Knight.SourceAttachment

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalFieldLayer

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition

open PairedSlotEncoding PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)

def Profile := {p : X → ExtOrd // RespectsSemantics sem (p ∘ occ) ∧
  p ∈ CanonicalPairedProfiles.inventory X j}

def Profile.bot : Profile sem j X occ :=
  ⟨fun _ => ⊥, RespectsSemantics.bot sem, rfl, fun _ => bot_ne_top⟩

instance : Fintype (Profile sem j X occ) :=
  ((CanonicalPairedProfiles.inventory_finite X j).subset (fun _ h => h.2)).fintype

theorem profile_short (q : Profile sem j X occ) (x : X) : Short j (q.val x) :=
  CanonicalPairedProfiles.inventory_short X j q.property.2 x

abbrev ceiling : ExtOrd := AttachmentGrid.endpoint j (Fintype.card X)

theorem grid_bound {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card X)) : h ≤ ceiling j X :=
  (AttachmentGrid.canonical j (Fintype.card X)).grid_bound h hh

theorem profile_bound (q : Profile sem j X occ) (x : X) : q.val x ≤ ceiling j X := by
  apply (CanonicalPairedProfiles.inventory_bound X j q.property.2 x).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by simp) le_rfl)

theorem grid_short {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card X)) :
    Short j h := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · tauto
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

variable (hj : 0 < j) (hA : j ≤ A.card)

variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

variable (hg : ∀ d : Cell D, D.grade d ≤ j)

def encode {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ))
    (ht : ∀ x, p x ≠ ⊤) : Profile sem j X occ := by
  refine ⟨PairedSlotEncoding.normalize j p, ?_,
    CanonicalPairedProfiles.normalize_mem_inventory X j ht⟩
  have hr := RespectsSemanticsBelow.map_bottom_reflecting (hp.toBelow (A, j))
    (by tauto) (PairedSlotIncoming.encoder_witness j (values p))
    (PairedSlotIncoming.encoder_reflects_bottom j (values p))
  have hw := hr.toRespects
    (fun d => ⟨D.scope_subset d, hg d⟩)
  simpa only [Function.comp_def, PairedSlotIncoming.encoder_profile] using hw

abbrev scheme := SourceLayerCarrier.scheme D (Profile sem j X occ) j hj hA

abbrev old (d : Cell D) : Cell (scheme sem j X occ hj hA) :=
  SourceLayerCarrier.toCell D (Profile sem j X occ) j hj hA (.inl d)

abbrev controller (q : Profile sem j X occ) :=
  SourceLayerCarrier.controller D (Profile sem j X occ) j hj hA q

include hg in
theorem max_grade (d : Cell (scheme sem j X occ hj hA)) :
    (scheme sem j X occ hj hA).grade d ≤ j := by
  rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
  cases SourceLayerCarrier.toOcc D (Profile sem j X occ) j hj hA d with
  | inl x => exact hg x
  | inr q => exact le_rfl

def attachment : SourceAttachment D j X (Profile sem j X occ) where
  sem := sem
  pos := hj
  height := hA
  separated := SeparatedSourceLayerCarrier.separated_of_proper D j hproper
  toAttachmentGrid := AttachmentGrid.canonical j (Fintype.card X)
  fields := Subtype.val
  lower q := q.val ∘ occ
  lower_bound q d _ := profile_bound sem j X occ q (occ d)
  lower_lawful q := q.property.1.toBelow _
  lower_prefix _ _ _ _ hag d _ := hag (occ d)

abbrev data (_hg : ∀ d : Cell D, D.grade d ≤ j) := (attachment sem j X occ hj hA hproper).data

abbrev ownerEquiv := (attachment sem j X occ hj hA hproper).ownerEquiv

abbrev rows := (data sem j X occ hj hA hproper hg).rows

abbrev source (q : Profile sem j X occ) :=
  (data sem j X occ hj hA hproper hg).profile (controller sem j X occ hj hA q)

theorem source_old (q : Profile sem j X occ) (d : Cell D) :
    source sem j X occ hj hA hproper hg q (old sem j X occ hj hA d) = q.val (occ d) :=
  (attachment sem j X occ hj hA hproper).source_old q d

theorem source_supported (a : Profile sem j X occ) (d : Cell (scheme sem j X occ hj hA)) :
    OrbitPrefixSupport.Supported j (sourceGrid j (Fintype.card X) : Set ExtOrd) a.val
      (source sem j X occ hj hA hproper hg a d) := by
  exact (attachment sem j X occ hj hA hproper).source_supported
    (fun q e => OrbitPrefixSupport.supported_field _ _ q.val (occ e)) a d

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows sem j X occ hj hA hproper hg).E (old sem j X occ hj hA c)
      (ownerEquiv sem j X occ hj hA hproper c d) = sem.E c d :=
  (attachment sem j X occ hj hA hproper).inherited_row c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j X occ hj hA hproper hg).IsConsistent :=
  (attachment sem j X occ hj hA hproper).consistent hs

theorem source_prefix (p q : Profile sem j X occ) {h : ExtOrd}
    (hh : h ∈ sourceGrid j (Fintype.card X)) (hag : Agree p.val q.val h) :
    Agree (source sem j X occ hj hA hproper hg p)
      (source sem j X occ hj hA hproper hg q) h :=
  (attachment sem j X occ hj hA hproper).source_prefix hh hag (fun d => hag (occ d))

theorem full_source_short (c : Cell (scheme sem j X occ hj hA))
    (hc : (scheme sem j X occ hj hA).scope c = A)
    (d : (scheme sem j X occ hj hA).below ((scheme sem j X occ hj hA).cell c)) :
    Short ((scheme sem j X occ hj hA).grade c) ((rows sem j X occ hj hA hproper hg).E c d) := by
  exact (attachment sem j X occ hj hA hproper).higher_short 0
    (fun a e => PairedCoupledSections.supported_short (fun _ hh => grid_short j X hh)
      (profile_short sem j X occ a) (source_supported sem j X occ hj hA hproper hg a e))
    (fun x hs _ _ => (hproper x hs).elim) c hc (Nat.zero_le _) d

variable {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ)) (ht : ∀ x, p x ≠ ⊤)

variable {G : Finset ExtOrd} {C : ExtOrd}

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (scheme sem j X occ hj hA)) : ExtOrd :=
  PairedSlotDecoder.decode j (values p) G C
    (source sem j X occ hj hA hproper hg (encode sem j X occ hg hp ht) d)

theorem section_old (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) (d : Cell D) :
    sectionOf sem j X occ hj hA hproper hg hp ht G C (old sem j X occ hj hA d) = p (occ d) := by
  rw [sectionOf, source_old]
  exact PairedSlotDecoder.decode_normalize hG hC ht (occ d)

theorem section_lawful (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C) :
    RespectsSemantics (rows sem j X occ hj hA hproper hg)
      (sectionOf sem j X occ hj hA hproper hg hp ht G C) := by
  apply (attachment sem j X occ hj hA hproper).decoded_whole
    (encode sem j X occ hg hp ht) (PairedSlotDecoder.decode_witness hG hC)
    (max_grade sem j X occ hj hA hg) _ (full_source_short sem j X occ hj hA hproper hg)
  intro c _
  change RespectsSemanticsBelow sem (D.cell c) (fun d =>
    PairedSlotDecoder.decode j (values p) G C (PairedSlotEncoding.normalize j p (occ d.1)))
  simpa only [Function.comp_apply, PairedSlotDecoder.decode_normalize hG hC ht] using hp.toBelow (D.cell c)

theorem section_bound (hC : SelfVis j C) (hb : ∀ x, p x ≤ C)
    (d : Cell (scheme sem j X occ hj hA)) :
    sectionOf sem j X occ hj hA hproper hg hp ht G C d ≤ C := by
  exact PairedSlotDecoder.decode_le_of_bound hC hb _

theorem section_supported {K : ℕ} (hjK : j ≤ K) (hCG : C ∈ G)
    (d : Cell (scheme sem j X occ hj hA)) :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf sem j X occ hj hA hproper hg hp ht G C d) :=
  PairedSlotDecoder.decode_supported hjK hCG _

/-- Both outer decoder parameters are held fixed. Agreement includes all
actual new controller coordinates, not just the projected old fields. -/
theorem section_agreement {q : X → ExtOrd} (hq : RespectsSemantics sem (q ∘ occ))
    (htq : ∀ x, q x ≠ ⊤) {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hC : SelfVis j C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem j X occ hj hA hproper hg hp ht G C)
      (sectionOf sem j X occ hj hA hproper hg hq htq G C) h := by
  exact decode_agreement hG hC hh hhC ht htq hag
    (fun _ he ha => source_prefix sem j X occ hj hA hproper hg _ _ he ha)

end

end VaughtConjecture.Knight.CanonicalFieldLayer
