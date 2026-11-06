
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.LowOnlyPaddedFiniteCertificate
import VaughtConjecture.Knight.LowOnlyPaddedLegal

/-! # Stage-bounded exact-readback data on the legal LOW scheme

The constructed legal carrier, literal ordered faces, bounded whole display,
and arbitrary-section certificate are composed here. A subsequent model
application must still produce the received tuple and its finite-cut receipts.
No realization of a selected display is inferred from bottom patterns alone.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedLegalCertificate
open     LowOnly LowOnlyOrderedLadder
open  LowOnlyPaddedInstallation LowOnlyPaddedEndpoints

variable {l m n K : ℕ} {B C : FiniteScope l} {R : VaughtConjecture.AmalgamationPlan.SupportFamily (Fin l)}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ (Finset.univ : FiniteScope l).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

local notation "E" => LowOnlyPaddedLegal.semScheme I F hroot hA hB hC hcover
local notation "donor" => LowOnlyPaddedLegal.donor I F hroot hA hB hC hcover
local notation "priv" => LowOnlyPaddedLegal.privateFace I F hroot hA hB hC hcover

/-- A raw supported display and exact readback certificate, before imposing a stage bound. -/
theorem exists_supported_certificate {S}
    (hS : F.Admissible (Finset.univ : FiniteScope l).card S)
    (hdonor : S.u = F.p) (hc : S.v F.gap.c = ⊤) (hr : S.v F.gap.r.1 = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w ,
      RespectsSemantics (E).rows w ∧
      (∀ d, w ((donor).map d) = F.p d) ∧
      (∀ d, w ((priv).map d) = S.v d) ∧
      (∀ d, OrbitPrefixSupport.Supported (Finset.univ : FiniteScope l).card
        ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∀ q ,
        RespectsSemantics (E).rows q →
        (∀ d, q ((priv).map d) = S.v d) →
        ∀ δ, LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < δ →
          (CappedEq q w δ) →
          ∀ d, q ((donor).map d) = F.p d := by
  obtain ⟨w, hw, ho, hsupp, hread⟩ :=
    LowOnlyPaddedFiniteCertificate.certificate I hA hB hC F hroot hS hdonor hc hactive
  have hdmap (d : Cell I.left.scheme) : (donor).map d =
      original I F hroot hA hB hC ((Finset.univ : FiniteScope l).card - 2) (by omega)
        (I.leftFace.map d) :=
    face_map I F hroot hA hB hC I.leftFace hB.not_ge _ _ d
  have hcmap (d : Cell I.right.scheme) : (priv).map d =
      original I F hroot hA hB hC ((Finset.univ : FiniteScope l).card - 2) (by omega)
        (I.rightFace.map d) :=
    face_map I F hroot hA hB hC I.rightFace hC.not_ge _ _ d
  refine ⟨w, hw, ?_, ?_, hsupp, ?_⟩
  · intro d
    exact (congrArg w (hdmap d)).trans ((ho (I.leftFace.map d)).trans
      ((field_donor I).trans (congrFun hdonor d)))
  · intro d
    exact (congrArg w (hcmap d)).trans ((ho (I.rightFace.map d)).trans
      (field_private hroot
        (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) d))
  · intro q hq hp δ hδ hcap d
    exact (congrArg q (hdmap d)).trans (hread q hq
      (((congrArg q (hcmap F.gap.c)).symm.trans (hp F.gap.c)).trans hc)
      (((congrArg q (hcmap F.gap.r.1)).symm.trans (hp F.gap.r.1)).trans hr) δ hδ hcap d)


