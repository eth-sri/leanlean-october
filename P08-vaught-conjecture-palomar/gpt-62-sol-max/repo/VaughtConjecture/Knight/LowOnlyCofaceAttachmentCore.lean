/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedReceivingCore
public import VaughtConjecture.Knight.FirstLossLowFamilyCore
public import VaughtConjecture.Knight.CoatomBoundaryPresentation
public import VaughtConjecture.Knight.CommonFaceAlignment

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyCofaceAttachment

open TypeTower StageType KnightRealization Value ExtOrd CappedDonor LowOnly

open CellScheme.restrictFace FirstLossLowFamily AmalgamationPlan SemSchemeBoundaryInput

noncomputable section

universe w

variable {α : LimitStage} {k K : ℕ} {p : StageType α.1 k}
  {P C : StageType α.1 (k + 1)} (hP : IsCoface p P) (hC : IsCoface p C)

def pair (k : ℕ) : CoatomPair k := CoatomPair.step Fin.castSuccEmb

def data : CoatomBoundaryPresentation.Data (pair k) where
  left := P.scheme
  right := C.scheme
  common := p.scheme
  visibleLeft := hP.extendsDomain.visible
  visibleRight := hC.extendsDomain.visible
  faceLeft := hP.extendsDomain.restrict
  faceRight := hC.extendsDomain.restrict

local notation "D" => data hP hC

local notation "s" => CoatomBoundaryPresentation.Data.step (data hP hC)

/-- The same ordered input in the general whole-boundary interface. -/
def input : WholeDonorBoundary.Input Finset.univ
    (Finset.univ.erase (s).a) (Finset.univ.erase (s).b) (s).plan k (k + 1) (k + 1) :=
  (D).input

local notation "I" => input hP hC

theorem root_receipt (F : LowOnly.Family P.scheme C.scheme K)
    (hF : F.root = commonRoot_of_cofaces hP hC) :
    (I).RootMatches F.root := by
  intro i
  have hrootcard : (rootFace k).card = k := by
    simp only [rootFace, Finset.card_image_of_injective _ Fin.castSuccEmb.injective,
      Finset.card_univ, Fintype.card_fin]
  let b := faceBelow P.scheme p.scheme Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict i
  let a : P.scheme.scheme.below (rootFace k, (rootFace k).card) :=
    ⟨b.1, b.2.1, b.2.2.trans_eq hrootcard.symm⟩
  rw [hF]
  refine ⟨a, faceBelow_val .., ?_⟩
  change (faceOf hP hC a).1 = _
  rw [faceOf, commonFace_val_congr Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card a b rfl]
  exact (congrArg Subtype.val (commonFace_faceBelow Fin.castSuccEmb hP.extendsDomain.visible
    hP.extendsDomain.restrict Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict i)).trans
    (faceBelow_val ..)

theorem left_proper : Finset.univ.erase (s).a ⊂ (Finset.univ : Finset (Fin (k + 2))) :=
  Finset.erase_ssubset (s).ha

theorem right_proper : Finset.univ.erase (s).b ⊂ (Finset.univ : Finset (Fin (k + 2))) :=
  Finset.erase_ssubset (s).hb

theorem coverage : ∀ T ∈ (s).plan, T ≠ Finset.univ →
    T ⊆ Finset.univ.erase (s).a ∨ T ⊆ Finset.univ.erase (s).b :=
  fun _ => AmalgamatedBoundaryPlan.proper_scope_cover s

/-- A supplied LOW family over two cofaces yields an actual copy of the donor
over their common root. The cutoff, physical scheme, and readback are derived. -/
theorem receive_of_receiving {M : Type w} {W : KnightRealization α M} (hcons :
    W.IsExactParentConsistent)
    (hFC : FiniteCutReceiving W)
    (u : Fin (k + 1) ↪ M) (hu : W.eval u = some C)
    (F : LowOnly.Family P.scheme C.scheme K)
    (hF : F.root = commonRoot_of_cofaces hP hC) (hp : F.p = P.label)
    (hc : C.label F.gap.c = ⊤) (hr : C.label F.gap.r.1 = ⊤) :
    ∃ t : Fin (k + 1) ↪ M,
      W.eval t = some P ∧ Fin.castSuccEmb.trans t = Fin.castSuccEmb.trans u := by
  have hs : F.root.Shared F.p C.label := by
    rw [hF, hp]
    exact shared_of_cofaces hP hC
  obtain ⟨v, pD, -, heval, htuple, heq, hlabel⟩ :=
    LowOnlyPaddedModelReceiving.receive_of_shared_of_receiving (I) F (root_receipt hP hC F hF)
      (by simp) (left_proper hP hC) (right_proper hP hC) (coverage hP hC)
      hcons hFC u C hu rfl hs hc hr (fun d hd => by
        rw [hp] at hd ⊢
        exact (P.label_bound d).resolve_right hd)
  have htype : pD = P := by
    apply StageType.eq_of_label heq
    aesop
  exact ⟨(I).placeLeft.trans v, htype ▸ heval, htuple⟩

end

end VaughtConjecture.Knight.LowOnlyCofaceAttachment
