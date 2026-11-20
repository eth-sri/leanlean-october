/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedLegalCertificate
public import VaughtConjecture.Knight.FiniteCoverReceivingCore
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.LowOnlyActualState

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedModelReceiving

open TypeTower StageType KnightRealization Value ExtOrd CappedDonor LowOnly

open CellScheme.restrictFace

noncomputable section

universe w

variable {l m n K : ℕ} {B C : Finset (Fin l)} {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : I.RootMatches F.root)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

local notation "E" => LowOnlyPaddedLegal.semScheme I F hroot hA hB hC hcover

local notation "donor" => LowOnlyPaddedLegal.donor I F hroot hA hB hC hcover

local notation "priv" => LowOnlyPaddedLegal.privateFace I F hroot hA hB hC hcover

include hroot hA hB hC hcover in
/-- Receive from a raw certificate by truncating the finished lawful display.
Only the cutoff is bounded by the stage; the actual private face remains literal.
The separator certificate, not cap cancellation alone, recovers donor tops. -/
theorem receive_raw_of_receiving {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) {S : State I.left I.right}
    (hS : F.Admissible (Finset.univ : Finset (Fin l)).card S)
    (hdonor : S.u = F.p) (hc : S.v F.gap.c = ⊤) (hr : S.v F.gap.r.1 = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b)
    (hb : S.b < ofOrd α.1)
    (u : Fin n ↪ M) (pC : StageType α.1 n) (hu : W.eval u = some pC)
    (hCs : pC.scheme = I.right)
    (hCv : ∀ d, pC.label d = S.v (SemScheme.castCell hCs d)) :
    ∃ (v : Fin l ↪ M) (pD : StageType α.1 n),
      I.placeRight.trans v = u ∧ W.eval (I.placeLeft.trans v) = some pD ∧
      I.commonLeft.trans (I.placeLeft.trans v) = I.commonRight.trans u ∧
      ∃ h : pD.scheme = I.left,
        ∀ d, pD.label d = F.p (SemScheme.castCell h d) := by
  obtain ⟨w, hw, -, hwp, -, hread⟩ :=
    LowOnlyPaddedLegalCertificate.exists_supported_certificate I F hroot hA hB hC hcover
      hS hdonor hc hr hactive
  let Q : StageType α.1 l := ofRespects α.2 E w hw
  have RC := LowOnlyPaddedLegal.private_receipt I F hroot hA hB hC hcover
  have hCv' (d : Cell I.right.scheme) : pC.label (SemScheme.castCell hCs.symm d) = S.v d := by
    simpa only [SemScheme.castCell_castCell_symm] using hCv (SemScheme.castCell hCs.symm d)
  have hp : typeMap I.placeRight Q = some pC := (RC.labels_iff pC hCs.symm).2 fun d => by
    change truncExt α.1 (w ((priv).map d)) = _
    exact (congrArg (truncExt α.1) ((hwp d).trans (hCv' d).symm)).trans
      (truncExt_id_of_bound (pC.label_bound _))
  obtain ⟨v, Q', hv, hev, hq, hcap⟩ :=
    FiniteCoverReceiving.finiteCoverReceiving_of_receiving hcons hFC Q I.placeRight u pC hp hu S.b
      (lt_of_le_of_lt bot_le hactive) hb
  let q : Cell (E).scheme → ExtOrd := fun d => Q'.label (SemScheme.castCell hq.symm d)
  have hqLaw : RespectsSemantics (E).rows q := respects_castCell hq Q'.respects
  let T : StageType α.1 l := ⟨E, q, fun d => Q'.label_bound _, hqLaw⟩
  have hQT : Q' = T := StageType.eq_of_label hq (fun _ => rfl)
  rw [hQT] at hev
  have hprivate : typeMap I.placeRight T = some pC := by
    have h := hcons v T I.placeRight hev
    rw [hv, hu] at h
    exact h.symm
  have hretain (d : Cell I.right.scheme) : q ((priv).map d) = S.v d :=
    ((RC.labels_iff pC hCs.symm).1 hprivate d).trans (hCv' d)
  have hcaps : ∀ d, min (q d) S.b = min (w d) S.b := by
    intro d
    have he := hcap (SemScheme.castCell hq.symm d)
    change min (q d) S.b = min (truncExt α.1 (w d)) S.b at he
    exact he.trans (FiniteCoverReceiving.min_truncExt_of_lt hb (w d))
  have hdon : ∀ d, q ((donor).map d) = F.p d := hread q hqLaw hretain S.b hactive hcaps
  have RD := LowOnlyPaddedLegal.donor_receipt I F hroot hA hB hC hcover
  refine ⟨v, T.restrictFace I.placeLeft RD.visible, hv, ?_, ?_, RD.restrict_eq, fun d => ?_⟩
  · rw [hcons v T I.placeLeft hev]
    exact typeMap_eq_some I.placeLeft T RD.visible
  · rw [← Function.Embedding.trans_assoc, I.commute, Function.Embedding.trans_assoc, hv]
  · change q (toCell (E).scheme I.placeLeft RD.visible d) = _
    exact (congrArg q (RD.toCell_eq d)).trans (hdon _)

include hroot hA hB hC hcover in
/-- Exact receiving from the actual private tuple and a lawful donor sharing
its root. The active state and cutoff are constructed, not supplied. -/
theorem receive_of_shared_of_receiving {M : Type w} {α : LimitStage} {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) (hFC : FiniteCutReceiving W) (u : Fin n ↪ M) (pC :
      StageType α.1 n)
    (hu : W.eval u = some pC) (hCs : pC.scheme = I.right)
    (hshared : F.root.Shared F.p (fun d => pC.label (SemScheme.castCell hCs.symm d)))
    (hc : pC.label (SemScheme.castCell hCs.symm F.gap.c) = ⊤)
    (hr : pC.label (SemScheme.castCell hCs.symm F.gap.r.1) = ⊤)
    (hpbound : ∀ d, F.p d ≠ ⊤ → F.p d < ofOrd α.1) :
    ∃ (v : Fin l ↪ M) (pD : StageType α.1 n),
      I.placeRight.trans v = u ∧ W.eval (I.placeLeft.trans v) = some pD ∧
      I.commonLeft.trans (I.placeLeft.trans v) = I.commonRight.trans u ∧
      ∃ h : pD.scheme = I.left,
        ∀ d, pD.label d = F.p (SemScheme.castCell h d) := by
  let v : Cell I.right.scheme → ExtOrd := fun d => pC.label (SemScheme.castCell hCs.symm d)
  have hv : RespectsSemantics I.right.rows v := respects_castCell hCs pC.respects
  obtain ⟨b, hb, hadm, hactive, _hbound⟩ := LowOnlyActualState.exists_active F v hv hshared
    hpbound (fun d hd => (pC.label_bound _).resolve_right hd)
  exact receive_raw_of_receiving I F hroot hA hB hC hcover hcons hFC
    (S := ⟨F.p, v, b⟩) (hadm _) rfl hc hr hactive hb u pC hu hCs (fun _ => rfl)

end

end VaughtConjecture.Knight.LowOnlyPaddedModelReceiving
