/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FirstLossAcquisitionCore
public import VaughtConjecture.Knight.LowOnlyFibres

@[expose] public section

namespace VaughtConjecture.Knight.FirstLossLowFamily

open TypeTower StageType KnightRealization Value ExtOrd TopSupport CellScheme.restrictFace
  AmalgamationPlan CappedDonor

universe w

section CommonRoot

variable {α : Ordinal.{0}} {k : ℕ} {pR : S α k} {P C : S α (k + 1)} (hP : IsCoface pR P)
  (hC : IsCoface pR C)

/-- The root face on `k + 1` points. -/
abbrev rootFace (k : ℕ) : Finset (Fin (k + 1)) := Finset.univ.image Fin.castSuccEmb

/-- The identification of the two copies of the root. -/
noncomputable def faceOf :
    P.scheme.scheme.below (rootFace k, (rootFace k).card) ≃
      C.scheme.scheme.below (rootFace k, (rootFace k).card) :=
  commonFace Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card

/-- The root cell of a root-face cell of the donor. -/
noncomputable def rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    Cell pR.scheme.scheme :=
  SemScheme.castCell hP.extendsDomain.restrict
    ((bP Fin.castSuccEmb hP.extendsDomain.visible (rootFace k).card).symm a).1

theorem toCell_rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
      (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)) = a.1 :=
  toCell_belowEquiv_symm_val P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
    (BJ' := (Finset.univ, (rootFace k).card)) (BJ := (rootFace k, (rootFace k).card)) rfl a

theorem faceOf_val (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    (faceOf hP hC a).1 = toCell C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
      (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a)) :=
  commonFace_val Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card a

theorem faceOf_grade (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
    P.scheme.scheme.grade a.1 = C.scheme.scheme.grade (faceOf hP hC a).1 :=
  (commonFace_grade Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card a).symm

set_option maxHeartbeats 1200000 in
theorem faceOf_respects {j : ℕ} (v : C.scheme.scheme.below (LowOnly.faceIndex (rootFace k) j) → ExtOrd) :
    RespectsSemanticsBelow C.scheme.rows (LowOnly.faceIndex (rootFace k) j) v ↔
      RespectsSemanticsBelow P.scheme.rows (LowOnly.faceIndex (rootFace k) j)
        (v ∘ LowOnly.rootCut (faceOf hP hC) (faceOf_grade hP hC) j) := by
  let k' := min (rootFace k).card j
  let e := commonFace Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict k'
  let r := LowOnly.rootCut (faceOf hP hC) (faceOf_grade hP hC) j
  have he (a : P.scheme.scheme.below (rootFace k, k')) : e a = r a := by
    apply Subtype.ext
    let a' : P.scheme.scheme.below (rootFace k, (rootFace k).card) :=
      ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩
    change (e a).1 = (faceOf hP hC a').1
    exact commonFace_val_congr Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
      Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict k' a a' rfl
  change _ ↔ RespectsSemanticsBelow P.scheme.rows (rootFace k, k') (fun a => v (r a))
  simp only [← he]
  exact commonFace_respects Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict k' v

/-- Two cofaces of one type have a literal common root along the initial face. -/
noncomputable def commonRoot_of_cofaces : LowOnly.CommonRoot P.scheme C.scheme where
  A := rootFace k
  B := rootFace k
  A_mem := hP.extendsDomain.visible
  B_mem := hC.extendsDomain.visible
  face := faceOf hP hC
  grade := faceOf_grade hP hC
  respects_iff := faceOf_respects hP hC

/-- The labels of two cofaces agree on the common root. -/
theorem shared_of_cofaces : (commonRoot_of_cofaces hP hC).Shared P.label C.label := by
  intro a
  change P.label a.1 = C.label (faceOf hP hC a).1
  have hPl := (typeMap_eq_some_iff_labels Fin.castSuccEmb P pR hP.extendsDomain.visible
    hP.extendsDomain.restrict).mp hP
    (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a))
  have hCl := (typeMap_eq_some_iff_labels Fin.castSuccEmb C pR hC.extendsDomain.visible
    hC.extendsDomain.restrict).mp hC
    (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a))
  rw [← toCell_rootCell hP a, faceOf_val hP hC a]
  exact hPl.trans hCl.symm

end CommonRoot

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

/-- Enlarge the donor over the literal private root obtained by first loss. -/
theorem exists_lowOnlyFamily_of_tail (hcons : R.IsExactParentConsistent) {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K) (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore R B)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : R.eval t = some p) (q : S α.1 (n + 1))
    (hq : IsCoface p q) (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ (k : ℕ) (u : Fin (k + 1) ↪ M) (CT : S α.1 (k + 1)) (e : Fin n ↪ Fin k)
      (pR : S α.1 k) (Q' : S α.1 (k + 1)),
      R.eval u = some CT ∧ (e.trans Fin.castSuccEmb).trans u = t ∧
      typeMap (FixedHeight.extendFace e) Q' = some q ∧
      ∃ (hCT : IsCoface pR CT) (hQ' : IsCoface pR Q') (F : LowOnly.Family Q'.scheme CT.scheme K),
        F.root = commonRoot_of_cofaces hQ' hCT ∧ F.p = Q'.label ∧
        CT.label F.gap.c = ⊤ ∧ CT.label F.gap.r.1 = ⊤ := by
  obtain ⟨m, Cov, Q, hQ, hQK, k, g, c, hc, e, het, hvg, hvg', H, hH, hfull, x, o, hxs, hxtop, hxH,
    hoH, hocell, hxo, hgap⟩ := FirstLossAcquisition.first_loss_of_tail hcons hcoin hKpos hres t p hp
  set g₁ : Fin (k + 1) ↪ Fin m := snoc g c hc with hg₁def
  have hg : Fin.castSuccEmb.trans g₁ = g := castSuccEmb_trans_snoc g c hc
  -- the two face types of the cover: the smaller face `pR`, the larger face `CT`
  set pR : S α.1 k := Q.restrictFace g hvg with hpRdef
  set CT : S α.1 (k + 1) := Q.restrictFace g₁ hvg' with hCTdef
  have hpR : typeMap g Q = some pR := typeMap_eq_some g Q hvg
  have hCT : typeMap g₁ Q = some CT := typeMap_eq_some g₁ Q hvg'
  have hcofCT : IsCoface pR CT := by
    change typeMap Fin.castSuccEmb CT = some pR
    rwa [typeMap_trans Fin.castSuccEmb g₁ Q CT hCT, hg]
  -- the root type is the restriction of `pR` along `e`
  have hep : typeMap e pR = some p := by
    rw [typeMap_trans e g Q pR hpR]
    have h := hcons Cov Q (e.trans g) hQ
    rw [het, hp] at h
    exact h.symm
  have hRtops : ∀ d, pR.label d = ⊤ → pR.scheme.scheme.grade d ≤ K := fun d hd =>
    (FirstLossAcquisition.face_top_grade_le hpR d hd).trans_eq hQK
  -- the enlarged donor
  obtain ⟨Q', hcofQ', hQ'e, hQ'K⟩ :=
    FirstLossAcquisition.exists_enlarged_donor pR e p hep hRtops q hq hqK
  -- the owner and the low source as cells of the private face
  have hos : Q.scheme.scheme.scope o = Finset.univ.image g₁ := congrArg Prod.fst hocell
  have hog : Q.scheme.scheme.grade o = K := congrArg Prod.snd hocell
  obtain ⟨oC, hoC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg')
    (Finset.subset_of_eq hos)
  obtain ⟨xC, hxC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg') hxs
  have hxoC : GradedLe (CT.scheme.scheme.cell xC) (CT.scheme.scheme.cell oC) :=
    (gradedLe_restrictFace_iff Q.scheme.scheme g₁ hvg').mpr (by rw [hoC, hxC]; exact hxo)
  have hoCg : CT.scheme.scheme.grade oC = K := by
    change Q.scheme.scheme.grade (toCell Q.scheme.scheme g₁ hvg' oC) = K
    rw [hoC]; exact hog
  let lift := toCell Q.scheme.scheme g₁ hvg'
  let liftRow (d : CT.scheme.scheme.below (CT.scheme.scheme.cell oC)) :
      Q.scheme.scheme.below (Q.scheme.scheme.cell o) :=
    ⟨lift d.1, hoC ▸ gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg' d.2⟩
  have row_eq (d : CT.scheme.scheme.below (CT.scheme.scheme.cell oC)) :
      CT.scheme.rows.E oC d = Q.scheme.rows.E o (liftRow d) :=
    Q.scheme.rows.E_congr hoC rfl
  let r : CT.scheme.scheme.below (CT.scheme.scheme.cell oC) := ⟨xC, hxoC⟩
  have hr : CT.scheme.rows.E oC r = Q.scheme.rows.E o ⟨x, hxo⟩ :=
    (row_eq r).trans (Q.scheme.rows.E_congr rfl hxC)
  let gap : LowOnly.SourceGap CT.scheme K :=
    ⟨oC, hoCg, r, by
      erw [hr, row_eq ⟨oC, GradedLe.refl _⟩]
      exact (hgap ⟨o, GradedLe.refl _⟩ hoH).trans_eq (Q.scheme.rows.E_congr rfl hoC.symm)⟩
  -- the common root and the family
  let root := commonRoot_of_cofaces hcofQ' hcofCT
  have hshared : root.Shared Q'.label CT.label := shared_of_cofaces hcofQ' hcofCT
  have hroot_sub : root.B ⊆ CT.scheme.scheme.scope gap.c := by
    intro y _
    change y ∈ Finset.univ.filter (fun j => g₁ j ∈ Q.scheme.scheme.scope
      (toCell Q.scheme.scheme g₁ hvg' oC))
    simp_all
  have hface_scope : ∀ a : Q'.scheme.scheme.below (rootFace k, (rootFace k).card),
      Q.scheme.scheme.scope (toCell Q.scheme.scheme g₁ hvg' (root.face a).1) ⊆
        Finset.univ.image g := by
    intro a
    have him := image_scope_restrictFace Q.scheme.scheme g₁ hvg' (root.face a).1
    rw [← him]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzB : z ∈ rootFace k := (root.face a).2.1 hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzB
    rw [← hg]
    simp
  let F : LowOnly.Family Q'.scheme CT.scheme K :=
    { root := root
      gap := gap
      p := Q'.label
      p_lawful := Q'.respects
      top_grade := hQ'K
      root_sub := hroot_sub
      root_gap := by
        intro a ht
        let d : CT.scheme.scheme.below (CT.scheme.scheme.cell oC) :=
          ⟨(root.face a).1, (root.face a).2.1.trans hroot_sub,
            (root.grade a).symm.trans_le ((hQ'K a.1 ht).trans_eq hoCg.symm)⟩
        change extVisibilityReplace (CT.scheme.rows.E oC r) K K < CT.scheme.rows.E oC d
        erw [hr, row_eq d]
        exact hgap (liftRow d) (hfull _ (hface_scope a) ((hshared a).symm.trans ht)) }
  refine ⟨k, g₁.trans Cov, CT, e, pR, Q', ?_, ?_, hQ'e, hcofCT, hcofQ', F, rfl, rfl,
    ?_, ?_⟩
  · have h := hcons Cov Q g₁ hQ
    rw [h]
    exact hCT
  · rw [Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc Fin.castSuccEmb, hg,
      ← Function.Embedding.trans_assoc]
    exact het
  · change Q.label (toCell Q.scheme.scheme g₁ hvg' oC) = ⊤
    rw [hoC]
    exact mem_topSet.mp (hH.subset hoH)
  · change Q.label (toCell Q.scheme.scheme g₁ hvg' xC) = ⊤
    rw [hxC]
    exact hxtop

end VaughtConjecture.Knight.FirstLossLowFamily
