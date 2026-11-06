/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedPairReadback
public import VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport

/-! # Finite exact-readback certificates on the unchanged LOW carrier

A constructed whole display supplies the strict separator. Agreement at any
cap above its negative reading retains that separator, and the actual private
top receipts force all donor tops. Non-top donor values are pinned by the same
cap. This finite theorem does not assert a model occurrence of the display.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedFiniteCertificate
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedEndpoints
open LowOnlyPaddedRestriction LowOnlyPaddedSelectedPair
noncomputable section

/-- A proper negative reading and a top positive reading remain strictly
ordered after receiving below a larger cutoff. -/
theorem separator_of_cap {D : Type*} {w q : D → ExtOrd} {lo hi} {a δ}
    (hwlo : w lo = a) (hwhi : w hi = ⊤) (hδ : a < δ)
    (hcap : ∀ d, min (q d) δ = min (w d) δ) : q lo < q hi := by grind

/-- Proper donor values are recovered by ordinary cap cancellation. -/
theorem exact_of_cap_and_top {D X : Type*} {w q : D → ExtOrd} {p : X → ExtOrd}
    (f : X → D) {δ} (hw : ∀ d, w (f d) = p d)
    (hcap : ∀ d, min (q d) δ = min (w d) δ)
    (hproper : ∀ d, p d ≠ ⊤ → p d < δ)
    (htop : ∀ d, p d = ⊤ → q (f d) = ⊤) : ∀ d, q (f d) = p d := by grind

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- The paired mechanism gives a supported whole display and an arbitrary-
section exact readback certificate, at every native grade at least two. -/
theorem paired_certificate (t : ℕ) (F : LowOnly.Family I.left I.right (t + 2))
    (hroot : ∀ i,
      ∃ a,
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (ht : t + 2 ≤ A.card) r hr
    (hfull : t + r + 2 = A.card)
    {S} (hS : F.Admissible (t + r + 2) S)
    (hdonor : S.u = F.p) (htop : S.v F.gap.c = ⊤)
    (hactive : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w,
      RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows w ∧
      (∀ d, w (original I F hroot hA hB hC (t + r) hr d) = S.profile (field I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + r + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∀ q,
        RespectsSemantics (build I F hroot hA hB hC (t + r) hr).rows q →
        q (original I F hroot hA hB hC (t + r) hr (I.rightFace.map F.gap.c)) = ⊤ →
        q (original I F hroot hA hB hC (t + r) hr (I.rightFace.map F.gap.r.1)) = ⊤ →
        ∀ δ, LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q (original I F hroot hA hB hC (t + r) hr (I.leftFace.map d)) = F.p d := by
  obtain ⟨w, hw, ho, hsupp, a, hlt, hpos, hneg⟩ :=
    exists_whole_pair (I := I) (hA := hA) (hB := hB) (hC := hC) t F hroot ht r hr hfull
      hS ⟨Sum.inr (Sum.inl F.gap.c), htop⟩ hactive
  refine ⟨w, hw, ho, hsupp, ?_⟩
  intro q hq hc hr' δ hδ hcap
  have hsep := separator_of_cap hneg hpos hδ hcap
  refine exact_of_cap_and_top (fun d => original I F hroot hA hB hC (t + r) hr
    (I.leftFace.map d)) (p := F.p) (δ := δ) ?_ hcap ?_ ?_
  · intro d
    exact (ho (I.leftFace.map d)).trans ((field_donor I S d).trans (congrFun hdonor d))
  · intro d hd
    have hm := LowSeparator.le_donorMax (LowSeparator.donorField F) S.profile
      (d := Sum.inl d) hd
    change S.u d ≤ _ at hm
    rw [hdonor] at hm
    exact (hm.trans (LowSeparator.donorMax_le_cutoffCut (t + 2)
      (LowSeparator.donorField F) S.profile)).trans_lt hδ
  · exact LowOnlyPaddedPairReadback.whole_readback I hA hB hC t F hroot ht r hr
      a hlt hq hc hr' hsep

/-- Grade one has the same finite certificate, with the distinct rank-tip
separator and the unrounded donor maximum. -/
theorem rank_certificate (F : LowOnly.Family I.left I.right 1)
    (hroot : ∀ i,
      ∃ a,
        a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
    (t : ℕ) (ht : t + 2 ≤ A.card) (hfull : t + 2 = A.card)
    {S} (hS : F.Admissible (t + 2) S)
    (hdonor : S.u = F.p) (htop : S.v F.gap.c = ⊤)
    (hactive : LowSeparator.donorMax (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w,
      RespectsSemantics (build I F hroot hA hB hC t ht).rows w ∧
      (∀ d, w (original I F hroot hA hB hC t ht d) = S.profile (field I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported (t + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∀ q,
        RespectsSemantics (build I F hroot hA hB hC t ht).rows q →
        q (original I F hroot hA hB hC t ht (I.rightFace.map F.gap.c)) = ⊤ →
        q (original I F hroot hA hB hC t ht (I.rightFace.map F.gap.r.1)) = ⊤ →
        ∀ δ, LowSeparator.donorMax (LowSeparator.donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q (original I F hroot hA hB hC t ht (I.leftFace.map d)) = F.p d := by
  obtain ⟨w, hw, ho, hsupp, T, _, hlt, qs, qt, hqs, hqt, hpos, hneg⟩ :=
    exists_whole_rank_pair (I := I) (hA := hA) (hB := hB) (hC := hC) F hroot t ht hfull
      hS ⟨Sum.inr (Sum.inl F.gap.c), htop⟩ hactive
  refine ⟨w, hw, ho, hsupp, ?_⟩
  intro q hq hc hr δ hδ hcap
  have hsep := separator_of_cap hneg hpos hδ hcap
  refine exact_of_cap_and_top (fun d => original I F hroot hA hB hC t ht
    (I.leftFace.map d)) (p := F.p) (δ := δ) ?_ hcap ?_ ?_
  · intro d
    exact (ho (I.leftFace.map d)).trans ((field_donor I S d).trans (congrFun hdonor d))
  · intro d hd
    have hm := LowSeparator.le_donorMax (LowSeparator.donorField F) S.profile
      (d := Sum.inl d) hd
    change S.u d ≤ _ at hm
    grind
  · intro d hd
    let d' : I.left.scheme.below (effC n 1) :=
      ⟨d, Finset.subset_univ _, le_min (F.top_grade d hd) (gradeC_le d)⟩
    exact LowOnlyPaddedReadbackTransport.rank_readback I F hroot hA hB hC
      (build I F hroot hA hB hC t ht) hlt hqs hqt hq hsep hc hr d' hd

include hC in
/-- The private original face supplies the native grade bound; it is not an
additional height assumption about the constructed carrier. -/
theorem family_height {K : ℕ} (F : LowOnly.Family I.left I.right K) : K ≤ A.card := by
  have hcard : C.card = n := by
    rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective,
      Finset.card_univ, Fintype.card_fin]
  exact F.gap.K_le.trans (hcard ▸ Finset.card_le_card hC.subset)

/-- Uniform finite certificate for every positive native grade, including
the separate grade-one base. Both branches use the unchanged full carrier. -/
theorem certificate {K : ℕ} (F : LowOnly.Family I.left I.right K)
    hroot
    {S} (hS : F.Admissible A.card S)
    (hdonor : S.u = F.p) (htop : S.v F.gap.c = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < S.b) :
    ∃ w : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
      RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows w ∧
      (∀ d, w (original I F hroot hA hB hC (A.card - 2) (by omega) d) =
        S.profile (field I d)) ∧
      (∀ d, OrbitPrefixSupport.Supported A.card ({⊤} : Set ExtOrd) S.profile (w d)) ∧
      ∀ q : Cell (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier → ExtOrd,
        RespectsSemantics (build I F hroot hA hB hC (A.card - 2) (by omega)).rows q →
        q (original I F hroot hA hB hC (A.card - 2) (by omega) (I.rightFace.map F.gap.c)) = ⊤ →
        q (original I F hroot hA hB hC (A.card - 2) (by omega) (I.rightFace.map F.gap.r.1)) = ⊤ →
        ∀ δ, LowSeparator.cutoffCut K (LowSeparator.donorField F) S.profile < δ →
          (∀ d, min (q d) δ = min (w d) δ) →
          ∀ d, q (original I F hroot hA hB hC (A.card - 2) (by omega)
            (I.leftFace.map d)) = F.p d := by
  have he : A.card - 2 + 2 = A.card := by omega
  by_cases hK : K = 1
  · subst K
    obtain ⟨w, hw, ho, hsupp, hr⟩ := rank_certificate I hA hB hC F hroot
      (A.card - 2) (by omega) he (he.symm ▸ hS) hdonor htop
      ((LowSeparator.donorMax_le_cutoffCut 1
        (LowSeparator.donorField F) S.profile).trans_lt hactive)
    refine ⟨w, hw, ho, ?_, ?_⟩
    · simpa only [he] using hsupp
    · intro q hq hc hrc δ hδ hcap
      exact hr q hq hc hrc δ
        ((LowSeparator.donorMax_le_cutoffCut 1
          (LowSeparator.donorField F) S.profile).trans_lt hδ) hcap
  · have hpos := F.gap.K_pos
    obtain ⟨t, rfl⟩ : ∃ t, K = t + 2 := ⟨K - 2, by omega⟩
    have hheight := family_height I hC F
    have hr : t + (A.card - (t + 2)) = A.card - 2 := by omega
    have hh : t + (A.card - (t + 2)) + 2 = A.card := by omega
    have hres := paired_certificate I hA hB hC t F hroot hheight
      (A.card - (t + 2)) (by omega) hh (hh.symm ▸ hS) hdonor htop hactive
    generalize_proofs hheight' at hres
    generalize hu : t + (A.card - (t + 2)) = u at hheight' hres
    have hueq : u = A.card - 2 := hu.symm.trans hr
    clear hu
    subst u
    simpa only [he] using hres

end
end VaughtConjecture.Knight.LowOnlyPaddedFiniteCertificate
