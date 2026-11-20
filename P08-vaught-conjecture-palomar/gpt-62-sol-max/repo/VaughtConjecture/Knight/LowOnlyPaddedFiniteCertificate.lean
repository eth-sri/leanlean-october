/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedPairReadback
public import VaughtConjecture.Knight.LowOnlyPaddedReadbackTransport

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedFiniteCertificate

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open LowOnlyPaddedContract LowOnlyPaddedIteration

open LowOnlyPaddedSelectedPair

noncomputable section

/-- A proper negative reading and a top positive reading remain strictly
ordered after receiving below a larger cutoff. -/
theorem separator_of_cap {D : Type*} {w q : D → ExtOrd} {lo hi : D} {a δ : ExtOrd}
    (hwlo : w lo = a) (hwhi : w hi = ⊤) (hδ : a < δ)
    (hcap : ∀ d, min (q d) δ = min (w d) δ) : q lo < q hi := by grind

/-- Proper donor values are recovered by ordinary cap cancellation. -/
theorem exact_of_cap_and_top {D X : Type*} {w q : D → ExtOrd} {p : X → ExtOrd}
    (f : X → D) {δ : ExtOrd} (hw : ∀ d, w (f d) = p d)
    (hcap : ∀ d, min (q d) δ = min (w d) δ)
    (hproper : ∀ d, p d ≠ ⊤ → p d < δ)
    (htop : ∀ d, p d = ⊤ → q (f d) = ⊤) : ∀ d, q (f d) = p d := by grind

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n : ℕ}

section

variable {K : ℕ} (L : BuildContext A B C R m n K)
  (t : ℕ) (ht : t + 2 ≤ A.card)

local notation "P" => L.tower t ht

local notation "orig" => Padded.Layer.original (L.tower t ht)

/-- A supported display whose donor readings survive every larger cut. -/
abbrev Certificate (S : State L.I.left L.I.right) (θ : ExtOrd) : Prop :=
  ∃ w : Cell (P).carrier → ExtOrd, RespectsSemantics (P).rows w ∧
    (∀ d, w (orig d) = S.profile (field L.I d)) ∧
    (∀ d, OrbitPrefixSupport.Supported (t + 2) ({⊤} : Set ExtOrd) S.profile (w d)) ∧
    ∀ q : Cell (P).carrier → ExtOrd, RespectsSemantics (P).rows q →
      q (orig (L.I.rightFace.map L.F.gap.c)) = ⊤ →
      q (orig (L.I.rightFace.map L.F.gap.r.1)) = ⊤ →
      ∀ δ, θ < δ → (∀ d, min (q d) δ = min (w d) δ) →
        ∀ d, q (orig (L.I.leftFace.map d)) = L.F.p d

private theorem finish {S : State L.I.left L.I.right} {θ : ExtOrd}
    (hdonor : S.u = L.F.p) (hθ : LowSeparator.donorMax (LowSeparator.donorField L.F) S.profile ≤ θ)
    {w : Cell (P).carrier → ExtOrd} (hw : RespectsSemantics (P).rows w)
    (ho : ∀ d, w (orig d) = S.profile (field L.I d))
    (hs : ∀ d, OrbitPrefixSupport.Supported (t + 2) ({⊤} : Set ExtOrd) S.profile (w d))
    {lo hi : Cell (P).carrier} (hlo : w lo = θ) (hhi : w hi = ⊤)
    (read_top : ∀ q : Cell (P).carrier → ExtOrd, RespectsSemantics (P).rows q →
      q (orig (L.I.rightFace.map L.F.gap.c)) = ⊤ →
      q (orig (L.I.rightFace.map L.F.gap.r.1)) = ⊤ → q lo < q hi →
      ∀ d, L.F.p d = ⊤ → q (orig (L.I.leftFace.map d)) = ⊤) :
    Certificate L t ht S θ := by
  refine ⟨w, hw, ho, hs, fun q hq hc hr δ hδ hcap => ?_⟩
  apply exact_of_cap_and_top (fun d => orig (L.I.leftFace.map d)) _ hcap _
    (read_top q hq hc hr (separator_of_cap hlo hhi hδ hcap))
  · intro d
    exact (ho _).trans ((field_donor L.I S d).trans (congrFun hdonor d))
  · intro d hd
    have hm := LowSeparator.le_donorMax (LowSeparator.donorField L.F) S.profile
      (d := Sum.inl d) hd
    change S.u d ≤ _ at hm
    rw [hdonor] at hm
    exact (hm.trans hθ).trans_lt hδ

end

/-- Paired slots give the certificate at native grades at least two. -/
private theorem paired_certificate (t : ℕ) (L : BuildContext A B C R m n (t + 2)) (ht : t + 2 ≤ A.card) (r : ℕ) (hr : t + r + 2 ≤ A.card)
    (hfull : t + r + 2 = A.card)
    {S : State L.I.left L.I.right} (hS : L.F.Admissible (t + r + 2) S)
    (hdonor : S.u = L.F.p) (htop : S.v L.F.gap.c = ⊤)
    (hactive : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) S.profile < S.b) :
    Certificate L (t + r) hr S
      (LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) S.profile) := by
  obtain ⟨w, hw, ho, hs, a, hlt, hpos, hneg⟩ :=
    exists_whole_pair t L ht r hr hfull
      hS ⟨Sum.inr (Sum.inl L.F.gap.c), htop⟩ hactive
  exact finish L (t + r) hr hdonor
    (LowSeparator.donorMax_le_cutoffCut _ _ _) hw ho hs hneg hpos
    (fun _ => LowOnlyPaddedPairReadback.whole_readback t L ht r hr a hlt)

/-- Rank tips give the grade-one certificate. -/
private theorem rank_certificate (L : BuildContext A B C R m n 1) (t : ℕ) (ht : t + 2 ≤ A.card) (hfull : t + 2 = A.card)
    {S : State L.I.left L.I.right} (hS : L.F.Admissible (t + 2) S)
    (hdonor : S.u = L.F.p) (htop : S.v L.F.gap.c = ⊤)
    (hactive : LowSeparator.donorMax (LowSeparator.donorField L.F) S.profile < S.b) :
    Certificate L t ht S (LowSeparator.donorMax (LowSeparator.donorField L.F) S.profile) := by
  obtain ⟨w, hw, ho, hs, T, _, hlt, qs, qt, hqs, hqt, hpos, hneg⟩ :=
    exists_whole_rank_pair L t ht hfull
      hS ⟨Sum.inr (Sum.inl L.F.gap.c), htop⟩ hactive
  refine finish L t ht hdonor le_rfl hw ho hs hneg hpos ?_
  intro q hq hc hr hsep d hd
  exact LowOnlyPaddedReadbackTransport.rank_readback L.I L.F L.root L.height L.leftProper L.rightProper
    (L.tower t ht) hlt hqs hqt hq hsep hc hr
    ⟨d, Finset.subset_univ _, le_min (L.F.top_grade d hd) (gradeC_le d)⟩ hd

/-- The private original face supplies the native grade bound; it is not an
additional height assumption about the constructed carrier. -/
theorem family_height {K : ℕ} (L : BuildContext A B C R m n K) : K ≤ A.card := by
  have hcard : C.card = n := by
    rw [← L.I.imageRight, Finset.card_image_of_injective _ L.I.placeRight.injective,
      Finset.card_univ, Fintype.card_fin]
  exact L.F.gap.K_le.trans (hcard ▸ Finset.card_le_card L.rightProper.subset)

/-- Uniform finite certificate for every positive native grade, including
the separate grade-one base. Both branches use the unchanged full carrier. -/
theorem certificate {K : ℕ} (L : BuildContext A B C R m n K)
    {S : State L.I.left L.I.right} (hS : L.F.Admissible A.card S)
    (hdonor : S.u = L.F.p) (htop : S.v L.F.gap.c = ⊤)
    (hactive : LowSeparator.cutoffCut K (LowSeparator.donorField L.F) S.profile < S.b) :
    Certificate L (A.card - 2) (Nat.sub_add_cancel L.height).le S
      (LowSeparator.cutoffCut K (LowSeparator.donorField L.F) S.profile) := by
  have he := Nat.sub_add_cancel L.height
  by_cases hK : K = 1
  · subst K
    obtain ⟨w, hw, ho, hsupp, hr⟩ := rank_certificate L
      (A.card - 2) he.le he (he.symm ▸ hS) hdonor htop
      ((LowSeparator.donorMax_le_cutoffCut 1
        (LowSeparator.donorField L.F) S.profile).trans_lt hactive)
    exact ⟨w, hw, ho, hsupp, fun q hq hc hrc δ hδ => hr q hq hc hrc δ
      ((LowSeparator.donorMax_le_cutoffCut 1 _ _).trans_lt hδ)⟩
  · have hpos := L.F.gap.K_pos
    obtain ⟨t, rfl⟩ : ∃ t, K = t + 2 := ⟨K - 2, by omega⟩
    have hheight := family_height L
    have hr : t + (A.card - (t + 2)) = A.card - 2 := by omega
    have hh : t + (A.card - (t + 2)) + 2 = A.card := by omega
    have hres := paired_certificate t L hheight
      (A.card - (t + 2)) (by omega) hh (hh.symm ▸ hS) hdonor htop hactive
    generalize_proofs hheight' at hres
    generalize hu : t + (A.card - (t + 2)) = u at hheight' hres
    have hueq : u = A.card - 2 := hu.symm.trans hr
    clear hu
    subst u
    exact hres

end

end VaughtConjecture.Knight.LowOnlyPaddedFiniteCertificate
