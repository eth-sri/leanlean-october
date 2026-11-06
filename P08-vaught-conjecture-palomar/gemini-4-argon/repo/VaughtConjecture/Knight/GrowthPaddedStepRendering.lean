/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepRows
public import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Returning the padded growth rendering invariant after a higher step

The long padded base uses exact table decoding. Higher full-scope owners use
their proved native short rows. The successor recovers the same incoming
renderer contract on its actual installed output, without lifting premises.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedStepRendering
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthHigherSources GrowthPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison GrowthPaddedStepRows

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X attach hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "Base" => base I X attach hA hB hC
local notation "Bcell" => CellScheme.cell (base I X attach hA hB hC)
local notation "Bgrade" => CellScheme.grade (base I X attach hA hB hC)
local notation "BRows" => baseRows I X attach hA hB hC
local notation "Car" => carrier P hnext
local notation "Ccell" => CellScheme.cell (carrier P hnext)
local notation "Cgrade" => CellScheme.grade (carrier P hnext)
local notation "Cscope" => CellScheme.scope (carrier P hnext)
local notation "Cbelow" => CellScheme.below (carrier P hnext)
local notation "Rws" => rows P hk hnext
local notation "Cat" => Catalogue X (k + 1)

abbrev baseMap (d : Cell Base) := old P hnext (P.baseMap d)

local notation "bMap" => baseMap P hnext

theorem base_index (d : Cell Base) : Ccell (bMap d) = Bcell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (P.base_index d)

theorem base_row (c : Cell Base) (d : CellScheme.below Base (Bcell c)) :
    Semantics.E Rws (bMap c) ⟨bMap d.1, by simpa only [base_index] using d.2⟩ =
      Semantics.E BRows c d :=
  (inherited_row P hk hnext (P.baseMap c)
    ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩).trans (P.base_row c d)

theorem base_respects (c : Cell Base) (p : Cell Car → ExtOrd) :
    RespectsSemanticsBelow Rws (Ccell (bMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow BRows (Bcell c) (fun d => p (bMap d.1)) :=
  (old_respects P hk hnext (P.baseMap c) p).trans (P.base_respects c fun d => p (old P hnext d))

include hk in
theorem cell_cases (d : Cell Car) :
    (∃ c, d = bMap c) ∨ Cscope d = A ∧ 2 ≤ Cgrade d ∧ Cgrade d ≤ k + 1 := by
  obtain ⟨x | a, rfl⟩ := (SourceLayerCarrier.enumeration P.carrier Cat
    (k + 1) (Nat.succ_pos k) hnext).surjective d
  · rcases P.cases x with ⟨c, rfl⟩ | ⟨hs, hl, hu⟩
    · exact Or.inl ⟨c, rfl⟩
    · have he := SourceLayerCarrier.cell_toCell P.carrier Cat (k + 1) (Nat.succ_pos k) hnext (.inl x)
      exact Or.inr ⟨(congrArg Prod.fst he).trans hs, hl.trans_eq (congrArg Prod.snd he).symm,
        (congrArg Prod.snd he).le.trans (hu.trans (Nat.le_succ k))⟩
  · have he := SourceLayerCarrier.cell_toCell P.carrier Cat (k + 1) (Nat.succ_pos k) hnext (.inr a)
    exact Or.inr ⟨congrArg Prod.fst he,
      (show 2 ≤ k + 1 by omega).trans_eq (congrArg Prod.snd he).symm, (congrArg Prod.snd he).le⟩

theorem higher_short (c : Cell Car) (hc : Cscope c = A) (hg : 2 ≤ Cgrade c)
    (d : Cbelow (Ccell c)) : Short (Cgrade c) (Semantics.E Rws c d) := by
  by_cases he : Ccell c = (A, k + 1)
  · let a := member P hk hnext ⟨c, he⟩
    have ha : controller P hnext a = ⟨c, he⟩ :=
      (SeparatedSourceLayerCarrier.controllerEquiv P.carrier Cat (k + 1) (Nat.succ_pos k) hnext
        (P.separated I X attach hA hB hC (by omega))).apply_symm_apply _
    rw [(data P hk hnext).row_new ⟨c, he⟩ d, show Cgrade c = k + 1 from congrArg Prod.snd he]
    simpa only [source, ha] using source_short P hk hnext a d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier Cat
      (k + 1) (Nat.succ_pos k) hnext c he
    obtain ⟨e, rfl⟩ := (ownerEquiv P hk hnext x).surjective d
    rw [GrowthPaddedStepRows.inherited_row]
    have hi := SourceLayerCarrier.cell_toCell P.carrier Cat (k + 1) (Nat.succ_pos k) hnext (.inl x)
    change Short (Cgrade (old P hnext x)) _
    rw [show Cgrade (old P hnext x) = P.carrier.grade x from congrArg Prod.snd hi]
    exact P.higher_short x ((congrArg Prod.fst hi).symm.trans hc)
      (hg.trans_eq (congrArg Prod.snd hi)) e

variable {j : ℕ} (hj : k + 1 ≤ j) (S : State I.right.scheme I.left.scheme)
  (hS : Admitted X j S) (hp : ∀ d, S.profile d ≠ ⊤)

local notation "norm" => GrowthHigherSources.normalized X (Nat.succ_pos k) hj S hS hp

def birth : Catalogue X 1 := P.birth (Nat.le_succ k) (state X norm)
  (state_admitted X _) (state_proper X _)

theorem birth_ranks (d : Field I.right.scheme I.left.scheme) :
    RelativeLadderLayer.ranks (fields X 1) (birth P hj S hS hp) d =
      LadderScalarRendering.fieldRank S.profile d := by
  rw [birth, P.birth_ranks, state_profile, GrowthHigherSources.normalized_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize (k + 1) S.profile hp d

def render (G : Finset ExtOrd) (H : ExtOrd) (d : Cell Car) : ExtOrd :=
  PairedSlotDecoder.decode (k + 1) (PairedSlotEncoding.values S.profile) G H
    (source P hk hnext norm d)

local notation "rnd" => render P hk hnext hj S hS hp

variable {G : Finset ExtOrd} {H : ExtOrd}

theorem render_base (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hb : ∀ d, S.profile d ≤ H) (d : Cell Base) :
    rnd G H (bMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth P hj S hS hp) S.profile H d := by
  unfold render baseMap
  rw [source_old]
  unfold selected
  have he := P.render_base (Nat.le_succ k) (state X norm)
    (state_admitted X _) (state_proper X _) (G := grid P) (H := ceiling P)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact GrowthHigherSources.anchor_bound X _ f) d
  refine (congrArg (PairedSlotDecoder.decode (k + 1)
    (PairedSlotEncoding.values S.profile) G H) he).trans ?_
  change PairedSlotDecoder.decode (k + 1) (PairedSlotEncoding.values S.profile) G H
    (RelativeLadderLayer.renderWith I.boundary (by omega) (field I) (fields X 1)
      (birth P hj S hS hp) (state X norm).profile (ceiling P) d) = _
  rw [state_profile, GrowthHigherSources.normalized_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized I.boundary (by omega)
    (field I) (fields X 1) (k + 1) _ S.profile hp hG hH (decode_reserved_ceiling hH hb) d

theorem render_lawful (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hb : ∀ d, S.profile d ≤ H) :
    RespectsSemanticsBelow Rws (A, j) (fun d => rnd G H d.1) := by
  have hbase (b : Cell Base) (hb' : Bgrade b ≤ j) :
      RespectsSemanticsBelow Rws (Ccell (bMap b)) (fun d => rnd G H d.1) := by
    apply (base_respects P hk hnext b _).mpr
    simp only [render_base P hk hnext hj S hS hp hG hH hb]
    exact (RelativeLadderLayer.renderWith_respects I.boundary I.rows (by omega : 0 < A.card)
      (field I) (fields X 1) (proper I hB hC) (birth P hj S hS hp) S.profile
      (birth_ranks P hj S hS hp) hb hS.visible
      (hH.mono (Nat.succ_pos k)) (boundary_lawful_at I X attach hS)).mono
      ⟨(CellScheme.isPlan Base).subset_of_mem (CellScheme.scope_mem_plan Base b), hb'⟩
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  rcases cell_cases P hk hnext c.1 with ⟨b, he⟩ | ⟨_, _, hu⟩
  · have hb' : Bgrade b ≤ j := by simpa only [he, CellScheme.grade, base_index] using c.2.2
    rcases c with ⟨c, hc⟩; dsimp only at he; subst c
    exact hbase b hb'
  · refine (map_respects_of_short_or_local (source_lawful P hk hnext norm) (fun d => d.2.2)
      (PairedSlotDecoder.decode_witness hG hH) fun d => ?_).mono
      ⟨(CellScheme.isPlan Car).subset_of_mem (CellScheme.scope_mem_plan Car c.1), hu⟩
    rcases cell_cases P hk hnext d.1 with ⟨b, he⟩ | ⟨hs, hl, _⟩
    · have hb' : Bgrade b ≤ j := by
        simpa only [he, CellScheme.grade, base_index] using d.2.2.trans hj
      rcases d with ⟨d, hd⟩; dsimp only at he; subst d
      exact Or.inr ((hbase b hb').locality ⟨bMap b, GradedLe.refl _⟩)
    · exact Or.inl (higher_short P hk hnext d.1 hs hl)

theorem render_bound (hH : SelfVis (k + 1) H) (hb : ∀ d, S.profile d ≤ H) (d : Cell Car) :
    rnd G H d ≤ H := by
  apply PairedSlotDecoder.decode_le hH
  intro a ha
  obtain ⟨f, hf⟩ := PairedSlotEncoding.mem_values.mp ha
  simpa only [hf] using hb f

theorem render_supported {l : ℕ} (hl : k + 1 ≤ l) (hH : H ∈ G) (d : Cell Car) :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile (rnd G H d) :=
  PairedSlotDecoder.decode_supported hl hH _

theorem render_agreement {T : State I.right.scheme I.left.scheme} (hT : Admitted X j T)
    (ht : ∀ d, T.profile d ≠ ⊤) {h : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hh : h ∈ G) (hhH : h ≤ H) (hab : Agree S.profile T.profile h) :
    Agree (rnd G H) (render P hk hnext hj T hT ht G H) h := by
  obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ := exists_common_cut hG hH hH hh hhH hhH hp ht hab
  have he' : Agree (fields X (k + 1) norm)
      (fields X (k + 1) (GrowthHigherSources.normalized X (Nat.succ_pos k) hj T hT ht)) e := by
    rw [GrowthHigherSources.normalized_fields, GrowthHigherSources.normalized_fields]; exact he
  exact Agree.decode (source_agreement P hk hnext _ _ heG he')
    (PairedSlotDecoder.decode_witness hG hH).mono (PairedSlotDecoder.decode_witness hG hH).mono
    hpe hqe fun _ _ => hcompare _

theorem render_ceiling_at (_hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hb : ∀ d, S.profile d ≤ H) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k + 1) :
    ∃ c : Cell Car, Ccell c = (A, i) ∧ rnd G H c = H := by
  by_cases he : i = k + 1
  · subst i
    refine ⟨_, (controller P hnext norm).2, ?_⟩
    unfold render source
    rw [ScopedSourcePrefixLayer.Data.profile_diagonal]
    exact decode_reserved_ceiling hH hb
  · obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ k) (state X norm)
      (state_admitted X _) (state_proper X _)
      (fun z (hz : z ∈ grid P) => (sourceGrid_visible hz).mono (Nat.le_succ k))
      ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
      (fun d => by rw [state_profile]; exact GrowthHigherSources.anchor_bound X _ d)
      i hi (by omega)
    refine ⟨old P hnext c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
    unfold render
    rw [source_old]
    exact (congrArg (PairedSlotDecoder.decode (k + 1)
      (PairedSlotEncoding.values S.profile) G H) hv).trans (decode_reserved_ceiling hH hb)

