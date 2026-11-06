/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FirstLossAcquisitionCore
public import VaughtConjecture.Knight.LowOnlyFibres

/-! # From the first-loss acquisition to the gate-free LOW family

The literal adapter from `FirstLossAcquisition` to KVC's `LowOnly.Family`: the two actual legal
cofaces of the finite-characteristic receiver, their literal common root, the actual owner and
low source, every strict-gap hypothesis, and the admissibility of the actual pair.

* **The private face** is the acquired cover's type restricted to the larger first-loss face
  `g ⌢ c`; **the donor** is the enlarged donor over the smaller face `g`
  (`exists_enlarged_donor`), whose tops have grade at most `K`.  Both are cofaces of the type of
  the smaller face along `Fin.castSuccEmb`.
* **The common root** (`commonRoot_of_cofaces`): two cofaces of one type have a literal common
  root along the initial face — the identification is `CappedDonor.commonFace`, and its grade,
  scope and row identities are derived from the two literal restrictions (rows transport along
  the scheme equalities, `rows_castCell`).  The actual labellings agree on the root
  (`shared_of_cofaces`).
* **The source gap**: the surviving full-scope grade-`K` owner and the lost top, read as cells
  of the private face; the strict gap at the owner is the acquired gap, since the restricted
  rows are the cover's rows.
* **The family**: the donor labelling, its top-grade bound, the root inside the owner's scope,
  and the strict gaps at every root top (retained tops of the smaller face lie below the owner,
  and the acquired gap covers them).
* **Admissibility of the actual pair**: for every cutoff `b` visible at `min j K`, the state
  `(donor labels, private labels, b)` is `Admissible j` — both labellings are lawful through
  every grade, agree on the root, are `1`-visible on future fields (orderliness), and LOW's
  conclusion is met since every designated donor top is literally `⊤`.  Higher-grade proper root
  values are retained literally; nothing is truncated to grade `K`.

No physical receiver is used. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.FirstLossLowFamily

open TypeTower StageType KnightRealization Value ExtOrd TopSupport CellScheme.restrictFace
  AmalgamationPlan CappedDonor

universe w

/-! ## Transport lemmas -/

/-- Rows transport along an equality of schemes. -/
theorem rows_castCell {n : ℕ} {X Y : SemScheme n} (h : X = Y) (Sig : Cell X.scheme)
    (d : X.scheme.below (X.scheme.cell Sig))
    (hd : GradedLe (Y.scheme.cell (SemScheme.castCell h d.1))
      (Y.scheme.cell (SemScheme.castCell h Sig))) :
    Y.rows.E (SemScheme.castCell h Sig) ⟨SemScheme.castCell h d.1, hd⟩ = X.rows.E Sig d := by
  subst h; rfl

theorem gradedLe_castCell {n : ℕ} {X Y : SemScheme n} (h : X = Y) {c c' : Cell X.scheme}
    (hc : GradedLe (X.scheme.cell c) (X.scheme.cell c')) :
    GradedLe (Y.scheme.cell (SemScheme.castCell h c))
      (Y.scheme.cell (SemScheme.castCell h c')) := by
  subst h; exact hc

/-- The scope of the image of a transported cell of a literal restriction. -/
theorem scope_toCell_castCell {m n : ℕ} {X : SemScheme n} {f : Fin m ↪ Fin n}
    {hv : Finset.univ.image f ∈ X.scheme.plan} {Z : SemScheme m}
    (h : X.restrictFace f hv = Z) (c : Cell Z.scheme) :
    X.scheme.scope (toCell X.scheme f hv (SemScheme.castCell h.symm c)) =
      (Z.scheme.scope c).image f := by
  subst h; exact (image_scope_restrictFace X.scheme f hv c).symm

/-! ## The literal common root of two cofaces -/

section CommonRoot

variable {α : Ordinal.{0}} {k : ℕ} {pR : S α k} {P C : S α (k + 1)} (hP : IsCoface pR P)
  (hC : IsCoface pR C)

/-- The root face on `k + 1` points. -/
abbrev rootFace (k : ℕ) : Finset (Fin (k + 1)) := Finset.univ.image Fin.castSuccEmb

/-- The identification of the two copies of the root. -/
def faceOf :
    P.scheme.scheme.below (rootFace k, (rootFace k).card) ≃
      C.scheme.scheme.below (rootFace k, (rootFace k).card) :=
  commonFace Fin.castSuccEmb hP.extendsDomain.visible hP.extendsDomain.restrict
    Fin.castSuccEmb hC.extendsDomain.visible hC.extendsDomain.restrict (rootFace k).card

/-- The root cell of a root-face cell of the donor. -/
def rootCell (a : P.scheme.scheme.below (rootFace k, (rootFace k).card)) :
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

/-- Two cofaces of one type have a literal common root along the initial face. -/
def commonRoot_of_cofaces : LowOnly.CommonRoot P.scheme C.scheme where
  A := rootFace k
  B := rootFace k
  A_mem := hP.extendsDomain.visible
  B_mem := hC.extendsDomain.visible
  face := faceOf hP hC
  grade a := (commonFace_grade Fin.castSuccEmb hP.extendsDomain.visible
    hP.extendsDomain.restrict Fin.castSuccEmb hC.extendsDomain.visible
    hC.extendsDomain.restrict (rootFace k).card a).symm
  scope a b := by
    have hsP (x) : P.scheme.scheme.scope x.1 =
        (pR.scheme.scheme.scope (rootCell hP x)).image Fin.castSuccEmb := by
      rw [← toCell_rootCell hP x]
      exact scope_toCell_castCell hP.extendsDomain.restrict (rootCell hP x)
    have hsC (x) : C.scheme.scheme.scope (faceOf hP hC x).1 =
        (pR.scheme.scheme.scope (rootCell hP x)).image Fin.castSuccEmb := by
      rw [faceOf_val hP hC x]
      exact scope_toCell_castCell hC.extendsDomain.restrict (rootCell hP x)
    rw [hsP a, hsP b, hsC a, hsC b]
  row a d hd := by
    obtain ⟨d'', hd''⟩ := exists_toCell_eq (D := P.scheme.scheme) (f := Fin.castSuccEmb)
      (hr := hP.extendsDomain.visible) (d.2.1.trans a.2.1)
    have hle : GradedLe (P.scheme.scheme.cell (toCell P.scheme.scheme Fin.castSuccEmb
        hP.extendsDomain.visible d''))
        (P.scheme.scheme.cell (toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
          (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a)))) := by
      rw [hd'', toCell_rootCell hP a]; exact d.2
    have hle' := (gradedLe_restrictFace_iff P.scheme.scheme Fin.castSuccEmb
      hP.extendsDomain.visible).mpr hle
    let dR : pR.scheme.scheme.below (pR.scheme.scheme.cell (rootCell hP a)) :=
      ⟨SemScheme.castCell hP.extendsDomain.restrict d'',
        gradedLe_castCell hP.extendsDomain.restrict hle'⟩
    have hL : P.scheme.rows.E a.1 d = pR.scheme.rows.E (rootCell hP a) dR :=
      (Semantics.E_congr' P.scheme.rows (toCell_rootCell hP a).symm
        (d' := ⟨toCell P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible d'', hle⟩)
        hd''.symm).trans
        (rows_castCell hP.extendsDomain.restrict _ ⟨d'', hle'⟩
          (gradedLe_castCell hP.extendsDomain.restrict hle')).symm
    have hd3 : ((bP Fin.castSuccEmb hP.extendsDomain.visible (rootFace k).card).symm
        ⟨d.1, d.2.trans a.2⟩).1 = d'' :=
      toCell_injective P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
        ((toCell_belowEquiv_symm_val P.scheme.scheme Fin.castSuccEmb hP.extendsDomain.visible
          (BJ' := (Finset.univ, (rootFace k).card)) (BJ := (rootFace k, (rootFace k).card)) rfl _).trans
          hd''.symm)
    have hleC := gradedLe_castCell hC.extendsDomain.restrict.symm dR.2
    have hR : C.scheme.rows.E (faceOf hP hC a).1 ⟨(faceOf hP hC ⟨d.1, d.2.trans a.2⟩).1, hd⟩ =
        pR.scheme.rows.E (rootCell hP a) dR :=
      (Semantics.E_congr' C.scheme.rows (faceOf_val hP hC a)
        (d' := ⟨toCell C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible
          (SemScheme.castCell hC.extendsDomain.restrict.symm dR.1),
          gradedLe_of_restrictFace C.scheme.scheme Fin.castSuccEmb hC.extendsDomain.visible hleC⟩)
        (by rw [faceOf_val hP hC ⟨d.1, d.2.trans a.2⟩]; unfold rootCell; rw [hd3])).trans
        (rows_castCell hC.extendsDomain.restrict.symm (rootCell hP a) dR hleC)
    exact hL.trans hR.symm

/-- The labels of two cofaces agree on the common root. -/
theorem shared_of_cofaces : (commonRoot_of_cofaces hP hC).Shared P.label C.label := fun a => by
  change P.label a.1 = C.label (faceOf hP hC a).1
  rw [← toCell_rootCell hP a, faceOf_val hP hC a]
  exact ((typeMap_eq_some_iff_labels Fin.castSuccEmb P pR hP.extendsDomain.visible
      hP.extendsDomain.restrict).mp hP
      (SemScheme.castCell hP.extendsDomain.restrict.symm (rootCell hP a))).trans
    ((typeMap_eq_some_iff_labels Fin.castSuccEmb C pR hC.extendsDomain.visible
      hC.extendsDomain.restrict).mp hC
      (SemScheme.castCell hC.extendsDomain.restrict.symm (rootCell hP a))).symm

end CommonRoot

/-! ## The family from the first-loss acquisition -/

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

theorem exists_lowOnlyFamily_of_tail (hcons : R.IsExactParentConsistent) {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (hKpos : 0 < K) (hres : ∀ {k : ℕ} (B : Fin k ↪ M), ¬ TopSupportRigidCore.RigidCore R B)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : R.eval t = some p) (q : S α.1 (n + 1))
    (hq : IsCoface p q) (hqK : ∀ d, q.label d = ⊤ → q.scheme.scheme.grade d ≤ K) :
    ∃ (k : ℕ) (u : Fin (k + 1) ↪ M) (CT : S α.1 (k + 1)) (e : Fin n ↪ Fin k)
      (pR : S α.1 k) (Q' : S α.1 (k + 1)),
      R.eval u = some CT ∧ (e.trans Fin.castSuccEmb).trans u = t ∧
      IsCoface pR CT ∧ IsCoface pR Q' ∧ typeMap (FixedHeight.extendFace e) Q' = some q ∧
      ∃ F : LowOnly.Family Q'.scheme CT.scheme K,
        F.p = Q'.label ∧ F.root.A = rootFace k ∧ F.root.B = rootFace k ∧
        CT.label F.gap.c = ⊤ ∧ CT.label F.gap.r.1 = ⊤ ∧
        ∀ (j : ℕ) (b : ExtOrd), SelfVis (min j K) b →
          F.Admissible j ⟨Q'.label, CT.label, b⟩ := by
  obtain ⟨m, Cov, Q, hQ, hQK, k, g, c, hc, e, het, hvg, hvg', H, hH, hfull, x, o, hxs, hxtop, hxH,
    hoH, hocell, hxo, hgap⟩ := FirstLossAcquisition.first_loss_of_tail hcons hcoin hKpos hres t p hp
  set g₁ : Fin (k + 1) ↪ Fin m := snoc g c hc
  have hg : Fin.castSuccEmb.trans g₁ = g := castSuccEmb_trans_snoc g c hc
  set pR : S α.1 k := Q.restrictFace g hvg
  set CT : S α.1 (k + 1) := Q.restrictFace g₁ hvg'
  have hpR : typeMap g Q = some pR := typeMap_eq_some g Q hvg
  have hCT : typeMap g₁ Q = some CT := typeMap_eq_some g₁ Q hvg'
  have hcofCT : IsCoface pR CT := by
    change typeMap Fin.castSuccEmb CT = some pR
    rw [typeMap_trans Fin.castSuccEmb g₁ Q CT hCT, hg]; exact hpR
  have hep : typeMap e pR = some p := by
    rw [typeMap_trans e g Q pR hpR]
    have h := hcons Cov Q (e.trans g) hQ; rw [het, hp] at h; exact h.symm
  obtain ⟨Q', hcofQ', hQ'e, hQ'K⟩ :=
    FirstLossAcquisition.exists_enlarged_donor pR e p hep
      (fun d hd => (FirstLossAcquisition.face_top_grade_le hpR d hd).trans_eq hQK) q hq hqK
  have hos : Q.scheme.scheme.scope o = Finset.univ.image g₁ := congrArg Prod.fst hocell
  obtain ⟨oC, hoC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg') hos.le
  obtain ⟨xC, hxC⟩ := exists_toCell_eq (D := Q.scheme.scheme) (f := g₁) (hr := hvg') hxs
  have hxoC : GradedLe (CT.scheme.scheme.cell xC) (CT.scheme.scheme.cell oC) :=
    (gradedLe_restrictFace_iff Q.scheme.scheme g₁ hvg').mpr (by rw [hoC, hxC]; exact hxo)
  have hoCg : CT.scheme.scheme.grade oC = K := by
    change Q.scheme.scheme.grade (toCell Q.scheme.scheme g₁ hvg' oC) = K
    rw [hoC]; exact congrArg Prod.snd hocell
  have hgap_at (w : CT.scheme.scheme.below (CT.scheme.scheme.cell oC))
      (hw : toCell Q.scheme.scheme g₁ hvg' w.1 ∈ H) :
      extVisibilityReplace (CT.scheme.rows.E oC ⟨xC, hxoC⟩) K K < CT.scheme.rows.E oC w := by
    have hbw : GradedLe (Q.scheme.scheme.cell (toCell Q.scheme.scheme g₁ hvg' w.1))
        (Q.scheme.scheme.cell o) :=
      hoC ▸ gradedLe_of_restrictFace Q.scheme.scheme g₁ hvg' w.2
    have h := hgap ⟨_, hbw⟩ hw
    have ex : CT.scheme.rows.E oC ⟨xC, hxoC⟩ = Q.scheme.rows.E o ⟨x, hxo⟩ :=
      Semantics.E_congr' Q.scheme.rows hoC hxC
    have ew : CT.scheme.rows.E oC w = Q.scheme.rows.E o ⟨_, hbw⟩ :=
      Semantics.E_congr' Q.scheme.rows hoC rfl
    rwa [ex, ew]
  let root := commonRoot_of_cofaces hcofQ' hcofCT
  have hshared : root.Shared Q'.label CT.label := shared_of_cofaces hcofQ' hcofCT
  have hroot_sub : root.B ⊆ CT.scheme.scheme.scope oC := fun y _ => by
    change y ∈ Finset.univ.filter fun j => g₁ j ∈ Q.scheme.scheme.scope
      (toCell Q.scheme.scheme g₁ hvg' oC)
    rw [Finset.mem_filter, hoC, hos]
    exact ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let F : LowOnly.Family Q'.scheme CT.scheme K :=
    { root := root
      gap := ⟨oC, hoCg, ⟨xC, hxoC⟩, hgap_at ⟨oC, GradedLe.refl _⟩ (hoC.symm ▸ hoH)⟩
      p := Q'.label
      p_lawful := Q'.respects
      top_grade := hQ'K
      root_sub := hroot_sub
      root_gap := fun a ht => by
        have hface_scope : Q.scheme.scheme.scope (toCell Q.scheme.scheme g₁ hvg' (root.face a).1) ⊆
            Finset.univ.image g := by
          rw [← image_scope_restrictFace Q.scheme.scheme g₁ hvg' (root.face a).1]
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ((root.face a).2.1 hz)
          rw [← hg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
        exact hgap_at ⟨(root.face a).1, (root.face a).2.1.trans hroot_sub,
          (root.grade a).symm.trans_le ((hQ'K a.1 ht).trans_eq hoCg.symm)⟩
          (hfull _ hface_scope ((hshared a).symm.trans ht)) }
  refine ⟨k, g₁.trans Cov, CT, e, pR, Q', by rw [hcons Cov Q g₁ hQ]; exact hCT, ?_,
    hcofCT, hcofQ', hQ'e, F, rfl, rfl, rfl, ?_, ?_, fun j b hb => ?_⟩
  · rw [Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc Fin.castSuccEmb, hg,
      ← Function.Embedding.trans_assoc]
    exact het
  · change Q.label (toCell Q.scheme.scheme g₁ hvg' oC) = ⊤
    rw [hoC]; exact mem_topSet.mp (hH.subset hoH)
  · change Q.label (toCell Q.scheme.scheme g₁ hvg' xC) = ⊤
    rw [hxC]; exact hxtop
  · exact
      { lawfulP := Q'.respects.toBelow _
        lawfulC := CT.respects.toBelow _
        shared := hshared
        futureP := fun d _ => SelfVis.mono (show SelfVis (Q'.scheme.scheme.grade d) (Q'.label d)
          from (Q'.respects.orderly d).symm) (Q'.scheme.scheme.grade_pos d)
        futureC := fun d _ => SelfVis.mono (show SelfVis (CT.scheme.scheme.grade d) (CT.label d)
          from (CT.respects.orderly d).symm) (CT.scheme.scheme.grade_pos d)
        cutoff := hb
        low := fun _ _ d hd => le_top.trans_eq (hd : Q'.label d = ⊤).symm }

