/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedSelectedPair

/-! # Arbitrary-section readback for the constructed whole paired display

All native grades at least two use the same actual occurrence interface.
Serving charts and admission follow from lawfulness; the two private top
receipts and strict leaf comparison remain the only readback inputs.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedPairReadback
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedEndpoints
open LowOnlyPaddedRestriction LowOnlyPaddedRenderChart LowOnlyPaddedSelectedChart
open LowOnlyPaddedSelectedPair
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)
  (hroot : I.RootAgreement F) (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def originalAt t (ht : t + 2 ≤ A.card) (d : I.boundary.below (A, t + 2)) :
    (build frame t ht).carrier.below (A, t + 2) :=
  ⟨original frame t ht d.1, by rw [original_index]; exact d.2⟩

variable (I) in
def privateIncl {j} (d : I.right.ClippedCells j) : I.boundary.below (A, j) :=
  ⟨I.rightFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

variable (I) in
def donorIncl {j} (d : I.left.ClippedCells j) : I.boundary.below (A, j) :=
  ⟨I.leftFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

variable (I F) in
theorem native_top_chart t (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : I.RootAgreement F)
    (ht : t + 2 ≤ A.card)
    {q : (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).carrier.below (A, t + 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).rows (A, t + 2) q)
    (htop : ∃ d, (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).carrier.grade d.1 = t + 2 ∧ q d = ⊤) :
    ∃ a, ∃ σ,
      Witness (gTop (t + 2)) σ ∧
      ∀ d, σ (nativeSource (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a d.1) = q d := by
  exact PaddedTower.Step.exists_top_chart (before (⟨hroot,hA,hB,hC⟩ : I.LowFrame F) t (by omega)) _ ht hq htop

variable (I F) in
theorem native_readback t (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : I.RootAgreement F)
    (ht : t + 2 ≤ A.card) a
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) (state F a).profile <
      (state F a).b)
    {q : (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).carrier.below (A, t + 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).rows (A, t + 2) q)
    (hc : q (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (privateIncl I (F.gap.cC le_rfl))) = ⊤)
    (hr : q (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (privateIncl I (F.gap.rC le_rfl))) = ⊤)
    (hsep : q (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (partner t rfl a hlt)) <
      q (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a))
    d (hd : F.p d.1 = ⊤) :
    q (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (donorIncl I d)) = ⊤ := by
  have hg : (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht).carrier.grade
      (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (privateIncl I (F.gap.cC le_rfl))).1 = t + 2 :=
    (congrArg Prod.snd ((original_index (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht _).trans
      (I.rightFace.index _))).trans F.gap.c_grade
  obtain ⟨b, σ, hσ, hread⟩ := native_top_chart I hA hB hC t F hroot ht hq ⟨_, hg, hc⟩
  have hv (e : I.right.ClippedCells (t + 2)) :
      σ ((state F b).v e.1) = q (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (privateIncl I e)) := by
    have he := hread (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (privateIncl I e))
    have hs := (native_source_original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht b (I.rightFace.map e.1)).trans
      ((congrFun (state_profile F b).symm _).trans
        (field_private I F hroot
          (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega)
            (state_admissible F b)) e.1))
    exact (congrArg σ hs).symm.trans he
  have hs := hread (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a)
  have hp := hread (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (partner t rfl a hlt))
  rw [source_leaf] at hs hp
  have hcmp : σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2))
      (state F b).profile (LowSeparator.partnerState F (state F a)).profile) <
      σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field I.left I.right) (t + 2))
        (state F b).profile (state F a).profile) := by
    simpa only [state_profile, Family.fields, partner] using hp.trans_lt (hsep.trans_eq hs.symm)
  have htop := LowSeparator.donor_top_readback F (state_admissible F b) (LowSeparator.activation_of_serving F (by rw [state_profile]; exact a.property.1) hlt hσ.mono hcmp) hσ ((hv (F.gap.cC le_rfl)).trans hc) ((hv (F.gap.rC le_rfl)).trans hr) d.1 hd
  have he := hread (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (donorIncl I d))
  have hs := (native_source_original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht b (I.leftFace.map d.1)).trans
    ((congrFun (state_profile F b).symm _).trans (field_donor I (state F b) d.1))
  exact he.symm.trans ((congrArg σ hs).trans htop)

variable (I F) in
theorem whole_readback t F
    (hroot : I.RootAgreement F)
    (ht : t + 2 ≤ A.card) r (hheight : t + r + 2 ≤ A.card)
    a
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) (state F a).profile <
      (state F a).b)
    {q : Cell (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hheight).carrier → ExtOrd}
    (hq : RespectsSemantics (build (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hheight).rows q)
    (hc : q (original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hheight (I.rightFace.map F.gap.c)) = ⊤)
    (hr : q (original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hheight (I.rightFace.map F.gap.r.1)) = ⊤)
    (hsep : q (belowEquiv (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hheight
        (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (partner t rfl a hlt))).1 <
      q (belowEquiv (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hheight
        (leafAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht a)).1)
    d (hd : F.p d = ⊤) :
    q (original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hheight (I.leftFace.map d)) = ⊤ := by
  have hm (e : I.boundary.below (A, t + 2)) :
      q (belowEquiv (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hheight
        (originalAt (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht e)).1 =
      q (original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) (t + r) hheight e.1) :=
    congrArg q (belowEquiv_original (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hheight e)
  let d' : I.left.ClippedCells (t + 2) :=
    ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩
  exact (hm (donorIncl I d')).symm.trans
    (native_readback I hA hB hC t F hroot ht a hlt
      (whole_pullback (⟨hroot, hA, hB, hC⟩ : I.LowFrame F) t ht (A, t + 2) le_rfl r hheight hq)
      ((hm (privateIncl I (F.gap.cC le_rfl))).trans hc)
      ((hm (privateIncl I (F.gap.rC le_rfl))).trans hr) hsep d' hd)

end
end VaughtConjecture.Knight.LowOnlyPaddedPairReadback
