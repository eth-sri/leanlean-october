
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedStepRows
import VaughtConjecture.Knight.OwnerwiseDecoding

/-! # Returning the padded growth rendering invariant after a higher step

The long padded base uses exact table decoding. Higher full-scope owners use
their proved native short rows. The successor recovers the same incoming
renderer contract on its actual installed output, without lifting premises.
-/

namespace VaughtConjecture.Knight.GrowthPaddedStepRendering
open     Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison GrowthPaddedStepRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {attach : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X attach hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "base₀" => base I X attach hA hB hC

abbrev baseMap d := old P hnext (P.baseMap d)

local notation "baseMap₀" => baseMap P hnext

local notation "carrier₀₀" => carrier P hnext

theorem base_index d :
    (carrier₀₀).cell (baseMap₀ d) = (base₀).cell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (P.base_index d)

theorem base_row c
    (d : (base₀).belowCell c) :
    (rows P hk hnext).E (baseMap₀ c)
      ⟨baseMap₀ d.1, by simpa only [base_index] using d.2⟩ =
        (baseRows attach hA hB hC).E c d :=
  (inherited_row P hk hnext (P.baseMap c)
    ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩).trans (P.base_row c d)

local notation "Cell₀" => Cell (carrier P hnext)

theorem base_respects (c : Cell (base₀))
    (p : Cell₀ → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier₀₀).cell (baseMap₀ c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow (baseRows attach hA hB hC)
        ((base₀).cell c) (fun d => p (baseMap₀ d.1)) :=
  (old_respects P hk hnext (P.baseMap c) p).trans
    (P.base_respects c (fun d => p (old P hnext d)))

local notation "cell_toCell₀" => SourceLayerCarrier.cell_toCell P.carrier (Catalogue X (k + 1)) (k + 1) (Nat.succ_pos k) hnext

include hk in
theorem cell_cases d :
    (∃ c, d = baseMap₀ c) ∨
      (carrier₀₀).scope d = A ∧ 2 ≤ (carrier₀₀).grade d ∧
        (carrier₀₀).grade d ≤ k + 1 := by
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration).surjective d
  rcases x with x | a
  · rcases P.cases x with ⟨c, rfl⟩ | ⟨hs, hl, hu⟩
    · exact Or.inl ⟨c, rfl⟩
    · have he := cell_toCell₀ (.inl x)
      exact Or.inr ⟨(congrArg Prod.fst he).trans hs,
        hl.trans_eq (congrArg Prod.snd he).symm,
        (congrArg Prod.snd he).le.trans (hu.trans (Nat.le_succ k))⟩
  · have he := cell_toCell₀ (.inr a)
    exact Or.inr ⟨congrArg Prod.fst he,
      (show 2 ≤ k + 1 by omega).trans_eq (congrArg Prod.snd he).symm,
      (congrArg Prod.snd he).le⟩

local notation "Catalogue₀" => Catalogue X (k + 1)

theorem higher_short (c : Cell₀) (hc : (carrier₀₀).scope c = A)
    (hg : 2 ≤ (carrier₀₀).grade c)
    (d : (carrier₀₀).belowCell c) :
    Short ((carrier₀₀).grade c) ((rows P hk hnext).E c d) := by
  by_cases he : (carrier₀₀).cell c = (A, k + 1)
  · let a := member P hk hnext ⟨c, he⟩
    have ha : controller P hnext a = ⟨c, he⟩ :=
      (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Catalogue₀)
        (k + 1) (Nat.succ_pos k) hnext
        (P.separated I X attach hA hB hC (by omega))).apply_symm_apply _
    have hr := (data P hk hnext).row_new ⟨c, he⟩ d
    rw [hr, show (carrier₀₀).grade c = k + 1 from congrArg Prod.snd he]
    simpa only [source, ha] using source_short P hk hnext a d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Catalogue₀)
      (k + 1) (Nat.succ_pos k) hnext c he
    obtain ⟨e, rfl⟩ := (ownerEquiv P hk hnext x).surjective d
    rw [GrowthPaddedStepRows.inherited_row]
    have hi := cell_toCell₀ (.inl x)
    change Short ((carrier₀₀).grade (old P hnext x)) _
    rw [show (carrier₀₀).grade (old P hnext x) = P.carrier.grade x from
      congrArg Prod.snd hi]
    exact P.higher_short x ((congrArg Prod.fst hi).symm.trans hc)
      (hg.trans_eq (congrArg Prod.snd hi)) e

variable {j : ℕ} (hj : k + 1 ≤ j) (S : State I.right.scheme I.left.scheme)
  (hS : Admitted X j S) (hp : ∀ d, S.profile d ≠ ⊤)

def normalized : Catalogue₀ :=
  GrowthHigherSources.normalized X (Nat.succ_pos k) hj S hS hp

local notation "fields₀" => fields X (k + 1)

local notation "normalized₀" => normalized hj S hS hp

theorem normalized_fields : fields₀ (normalized₀) =
    PairedSlotEncoding.normalize (k + 1) S.profile :=
  GrowthHigherSources.normalized_fields X

def birth : Catalogue X 1 := P.birth (Nat.le_succ k) (state X (normalized₀))
  (state_admitted X) (state_proper X _)

local notation "birth₀" => birth P hj S hS hp

theorem birth_ranks d :
    RelativeLadderLayer.ranks (fields X 1) (birth₀) d =
      LadderScalarRendering.fieldRank S.profile d := by
  rw [birth, P.birth_ranks, state_profile, normalized_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize hp

local notation "decode₀" => PairedSlotDecoder.decode (k + 1) (PairedSlotEncoding.values S.profile)

def render (G : Finset ExtOrd) (H : ExtOrd) (d : Cell₀) : ExtOrd :=
  decode₀ G H
    (source P hk hnext (normalized₀) d)

variable {G : Finset ExtOrd} {H : ExtOrd}

local notation "SelfVis₀" => SelfVis (k + 1)

local notation "render₀" => render P hk hnext hj S hS hp

local notation "BoundedBy₀" => BoundedBy S.profile H

theorem render_base (hG : ∀ z ∈ G, SelfVis₀ z) (hH : SelfVis₀ H)
    (hb : BoundedBy₀) d :
    render₀ G H (baseMap₀ d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (birth₀) S.profile H d := by
  unfold render baseMap
  rw [source_old]
  
  have he := P.render_base (Nat.le_succ k) (state X (normalized₀))
    (state_admitted X) (state_proper X _) (G := grid P) 
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact GrowthHigherSources.anchor_bound X _ f) d
  refine (congrArg (decode₀ G H) he).trans ?_
  
  rw [state_profile, normalized_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized _ hp hG hH (decode_reserved_ceiling hH hb) d

theorem render_base_lawful (hG : ∀ z ∈ G, SelfVis₀ z) (hH : SelfVis₀ H)
    (hb : BoundedBy₀) c
    (hc : (base₀).grade c ≤ j) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier₀₀).cell (baseMap₀ c))
      (fun d => render₀ G H d.1) := by
  apply (base_respects P hk hnext c _).mpr
  simp only [render_base P hk hnext hj S hS hp hG hH hb]
  have ht := RelativeLadderLayer.renderWith_respects I.boundary I.rows (by omega : 0 < A.card)
    (field I) (fields X 1) (proper hB hC) (birth₀) S.profile
    (birth_ranks P hj S hS hp) hb (hS.visible)
    (hH.mono (Nat.succ_pos k)) (boundary_lawful_at I X attach hS)
  exact ht.mono ⟨(base₀).scope_subset c, hc⟩

theorem render_native_lawful (hG : ∀ z ∈ G, SelfVis₀ z) (hH : SelfVis₀ H)
    (hb : BoundedBy₀) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => render P hk hnext hj S hS hp G H d.1) := by
  have hr := source_lawful P hk hnext (normalized hj S hS hp)
  have hν := PairedSlotDecoder.decode_witness (S := PairedSlotEncoding.values S.profile) hG hH
  apply map_respects_of_short_or_local hr (fun d => d.2.2) hν
  intro c
  rcases cell_cases P hk hnext c.1 with ⟨b, he⟩ | ⟨hs, hl, _⟩
  · right
    have hb' : (base₀).grade b ≤ j := by
      have hc  := c.2.2.trans hj
      simpa only [he, CellScheme.grade, base_index] using hc
    have hrb := render_base_lawful P hk hnext hj S hS hp hG hH hb b hb'
    rcases c with ⟨c, hc⟩
    dsimp only at he
    subst c
    exact hrb.locality ⟨baseMap P hnext b, GradedLe.refl _⟩
  · grind [higher_short]

theorem render_lawful (hG : ∀ z ∈ G, SelfVis₀ z) (hH : SelfVis₀ H)
    (hb : BoundedBy₀) :
    RespectsSemanticsBelow (rows P hk hnext) (A, j)
      (fun d => render P hk hnext hj S hS hp G H d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  rcases cell_cases P hk hnext c.1 with ⟨b, he⟩ | ⟨_, _, hu⟩
  · have hb' : (base₀).grade b ≤ j := by
      simpa only [he, CellScheme.grade, base_index] using c.2.2
    rcases c with ⟨c, hc⟩
    dsimp  at he
    subst c
    exact render_base_lawful P hk hnext hj S hS hp hG hH hb b hb'
  · exact (render_native_lawful P hk hnext hj S hS hp hG hH hb).mono
      ⟨(carrier P hnext).scope_subset c.1, hu⟩

theorem render_bound (hH : SelfVis₀ H) (hb : BoundedBy₀)
    d : render₀ G H d ≤ H := by
  apply PairedSlotDecoder.decode_le hH
  intro a ha
  obtain ⟨f, hf⟩ := PairedSlotEncoding.mem_values.mp ha
  simpa only [hf] using hb f

theorem render_supported {l} (hl : k + 1 ≤ l) (hH : H ∈ G)
    d :
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) S.profile
      (render₀ G H d) := PairedSlotDecoder.decode_supported hl hH _

theorem render_agreement {T} (hT : Admitted X j T)
    (ht : AvoidsValue T.profile ⊤) {h}
    (hG : ∀ z ∈ G, SelfVis₀ z) (hH : SelfVis₀ H)
    (hh : h ∈ G) (hhH : h ≤ H) (hab : Agree S.profile T.profile h) :
    Agree (render₀ G H) (render P hk hnext hj T hT ht G H) h := by
  obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ := exists_common_cut hG hH hH hh hhH hhH hp ht hab
  have he' : Agree (fields₀ (normalized₀))
      (fields₀ (normalized hj T hT ht)) e := by
    rw [normalized_fields, normalized_fields]
    exact he
  exact Agree.decode (source_agreement P hk hnext _ _ heG he')
    (PairedSlotDecoder.decode_witness hG hH).mono (PairedSlotDecoder.decode_witness hG hH).mono
    hpe hqe (fun _ _ => hcompare _)

theorem render_ceiling (hH : SelfVis₀ H) (hb : BoundedBy₀) :
    render₀ G H (controller P hnext (normalized₀)).1 = H := by
  unfold render source
  rw [ScopedSourcePrefixLayer.Data.profile_diagonal]
  exact decode_reserved_ceiling hH hb

theorem render_ceiling_at (_hG : ∀ z ∈ G, SelfVis₀ z) (hH : SelfVis₀ H)
    (hb : BoundedBy₀) i (hi : 1 ≤ i) (hik : i ≤ k + 1) :
    ∃ c , (carrier₀₀).cell c = (A, i) ∧
      render₀ G H c = H := by
  by_cases he : i = k + 1
  · subst i
    exact ⟨_, (controller P hnext (normalized₀)).2,
      render_ceiling P hk hnext hj S hS hp hH hb⟩
  · have hil : i ≤ k := by omega
    obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ k) (state X (normalized₀))
      (state_admitted X) (state_proper X _)
      (fun z (hz) => (sourceGrid_visible hz).mono (Nat.le_succ k))
      ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
      (fun d => by rw [state_profile]; exact GrowthHigherSources.anchor_bound X _ d) i hi hil
    refine ⟨old P hnext c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
    unfold render
    rw [source_old]
    
    exact (congrArg (decode₀ G H) hv).trans (decode_reserved_ceiling hH hb)

