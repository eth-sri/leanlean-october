/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSelectedPair

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedPairReadback

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open LowOnlyPaddedContract LowOnlyPaddedIteration

open LowOnlyPaddedRenderChart LowOnlyPaddedSelectedChart

open LowOnlyPaddedSelectedPair

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n : ℕ}
variable (I : WholeDonorBoundary.Input A B C R m n n)

def privateIncl {j : ℕ} (d : I.right.scheme.below (effC n j)) : I.boundary.below (A, j) :=
  ⟨I.rightFace.map d.1, I.boundary.scope_subset _,
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

def donorIncl {j : ℕ} (d : I.left.scheme.below (effC n j)) : I.boundary.below (A, j) :=
  ⟨I.leftFace.map d.1, I.boundary.scope_subset _,
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

theorem native_readback (t : ℕ) (L : BuildContext A B C R m n (t + 2))
    (ht : t + 2 ≤ A.card) (a : L.F.Anchor (t + 2))
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) (state L.F a).profile <
      (state L.F a).b)
    {q : (L.tower t ht).carrier.below (A, t + 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (L.tower t ht).rows (A, t + 2) q)
    (hc : q ((L.tower t ht).originalAt (privateIncl L.I (L.F.gap.cC le_rfl))) = ⊤)
    (hr : q ((L.tower t ht).originalAt (privateIncl L.I (L.F.gap.rC le_rfl))) = ⊤)
    (hsep : q (leafAt L t ht (partner a hlt)) <
      q (leafAt L t ht a))
    (d : L.I.left.scheme.below (effC n (t + 2))) (hd : L.F.p d.1 = ⊤) :
    q ((L.tower t ht).originalAt (donorIncl L.I d)) = ⊤ := by
  have hg : (L.tower t ht).carrier.grade
      ((L.tower t ht).originalAt (privateIncl L.I (L.F.gap.cC le_rfl))).1 = t + 2 :=
    (congrArg Prod.snd (((L.tower t ht).original_index _).trans
      (L.I.rightFace.index _))).trans L.F.gap.c_grade
  obtain ⟨b, σ, hσ, hread⟩ := (L.tower t ht).top_chart hq ⟨_, hg, hc⟩
  change ∀ d, σ ((L.tower t ht).source b d.1) = q d at hread
  have hv (e : L.I.right.scheme.below (effC n (t + 2))) :
      σ ((state L.F b).v e.1) = q ((L.tower t ht).originalAt (privateIncl L.I e)) := by
    have he := hread ((L.tower t ht).originalAt (privateIncl L.I e))
    have hs := ((L.tower t ht).source_original b (L.I.rightFace.map e.1)).trans
      ((congrFun (state_profile L.F b).symm _).trans
        (field_private L.I L.F L.root (state_admissible L.F b) e.1))
    exact (congrArg σ hs).symm.trans he
  have hs := hread (leafAt L t ht a)
  have hp := hread (leafAt L t ht (partner a hlt))
  rw [source_leaf] at hs hp
  have hcmp : σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field L.I.left L.I.right) (t + 2))
      (state L.F b).profile (LowSeparator.partnerState L.F (state L.F a)).profile) <
      σ (SourcePrefixRows.cut (LowSeparator.grid (X := Field L.I.left L.I.right) (t + 2))
        (state L.F b).profile (state L.F a).profile) := by
    simpa [state_profile, Family.fields, partner] using hp.trans_lt (hsep.trans_eq hs.symm)
  have htop := LowSeparator.serving_readback L.F (state_admissible L.F b)
    (by rw [state_profile]; exact a.property.1) hlt hσ hcmp
    ((hv (L.F.gap.cC le_rfl)).trans hc) ((hv (L.F.gap.rC le_rfl)).trans hr) d.1 hd
  have he := hread ((L.tower t ht).originalAt (donorIncl L.I d))
  have hs := ((L.tower t ht).source_original b (L.I.leftFace.map d.1)).trans
    ((congrFun (state_profile L.F b).symm _).trans (field_donor L.I (state L.F b) d.1))
  exact he.symm.trans ((congrArg σ hs).trans htop)

theorem whole_readback (t : ℕ) (L : BuildContext A B C R m n (t + 2))
    (ht : t + 2 ≤ A.card) (r : ℕ) (hheight : t + r + 2 ≤ A.card)
    (a : L.F.Anchor (t + 2))
    (hlt : LowSeparator.cutoffCut (t + 2) (LowSeparator.donorField L.F) (state L.F a).profile <
      (state L.F a).b)
    {q : Cell (L.tower (t + r) hheight).carrier → ExtOrd}
    (hq : RespectsSemantics (L.tower (t + r) hheight).rows q)
    (hc : q ((L.tower (t + r) hheight).original (L.I.rightFace.map L.F.gap.c)) = ⊤)
    (hr : q ((L.tower (t + r) hheight).original (L.I.rightFace.map L.F.gap.r.1)) = ⊤)
    (hsep : q (L.advance t ht r hheight
        (leafAt L t ht (partner a hlt))).1 <
      q (L.advance t ht r hheight
        (leafAt L t ht a)).1)
    (d : Cell L.I.left.scheme) (hd : L.F.p d = ⊤) :
    q ((L.tower (t + r) hheight).original (L.I.leftFace.map d)) = ⊤ := by
  have hm (e : L.I.boundary.below (A, t + 2)) :
      q (L.advance t ht r hheight
        ((L.tower t ht).originalAt e)).1 =
      q ((L.tower (t + r) hheight).original e.1) :=
    congrArg q (Padded.buildEquiv_original L.initial t ht (A, t + 2) le_rfl r hheight e)
  let d' : L.I.left.scheme.below (effC n (t + 2)) :=
    ⟨d, Finset.subset_univ _, le_min (L.F.top_grade d hd) (gradeC_le d)⟩
  exact (hm (donorIncl L.I d')).symm.trans
    (native_readback t L ht a hlt
      (Padded.build_pullback L.initial t ht (A, t + 2) le_rfl r hheight hq)
      ((hm (privateIncl L.I (L.F.gap.cC le_rfl))).trans hc)
      ((hm (privateIncl L.I (L.F.gap.rC le_rfl))).trans hr) hsep d' hd)

end

end VaughtConjecture.Knight.LowOnlyPaddedPairReadback
