/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemanticPatch
public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.CappedLifting
public import VaughtConjecture.Knight.FiniteOffset

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {B A : Finset ι}

variable {D : CellScheme B} {K : CellScheme A}

variable (semD : Semantics D) (semK : Semantics K)

/-- Literal inherited semantics with no foreign cells inside the face. -/
structure ExactSemanticFace where
  map : Cell D ↪ Cell K
  index : ∀ d, K.cell (map d) = D.cell d
  exhaustive : ∀ z, K.scope z ⊆ B → ∃ d, map d = z
  row : ∀ (c : Cell D) (d : D.below (D.cell c)),
    semK.E (map c) ⟨map d.1, by grind⟩ = semD.E c d

namespace ExactSemanticFace

/-- Locate a face occurrence in the ambient full-scope cut. -/
abbrev belowAmbient {ι : Type*} [DecidableEq ι] {A B : Finset ι} {D : CellScheme B} {E : CellScheme A}
    {rd : Semantics D} {re : Semantics E} (G : ExactSemanticFace rd re) {j : ℕ}
    (d : Cell D) (hd : D.grade d ≤ j) : E.below (A, j) :=
  ⟨G.map d, E.scope_subset _, (congrArg Prod.snd (G.index d)).le.trans hd⟩

variable {semD semK} (F : ExactSemanticFace semD semK)

def patch : SemanticPatch D K where
  map := F.map
  index := F.index
  closed c d hd := F.exhaustive d (hd.1.trans (D.scope_subset c))

def belowMap (c : Cell D) (d : D.below (D.cell c)) : K.below (K.cell (F.map c)) :=
  ⟨F.map d.1, by rw [F.index, F.index]; exact d.2⟩

noncomputable def belowEquiv (BJ : Finset ι × ℕ) (hB : BJ.1 ⊆ B) :
    D.below BJ ≃ K.below BJ :=
  F.patch.belowEquiv BJ (fun d hd => F.exhaustive d (hd.1.trans hB))

theorem respects_below_iff (BJ : Finset ι × ℕ) (hB : BJ.1 ⊆ B)
    (q : K.below BJ → ExtOrd) :
    RespectsSemanticsBelow semK BJ q ↔
      RespectsSemanticsBelow semD BJ (q ∘ F.belowEquiv BJ hB) :=
  iff_comp_symm (F.belowEquiv BJ hB).symm
    (F.patch.respects_iff F.row BJ (fun d hd => F.exhaustive d (hd.1.trans hB))) q

/-- Restriction includes arbitrary whole ambient labellings. -/
theorem restrict {q : Cell K → ExtOrd} (hq : RespectsSemantics semK q) :
    RespectsSemantics semD (q ∘ F.map) :=
  ((F.respects_below_iff (B, B.card) (Finset.Subset.refl _) _).mp (hq.toBelow _)).toRespects
    (fun d => ⟨D.scope_subset d, (D.grade_le_card_scope d).trans (Finset.card_le_card (D.scope_subset d))⟩)

/-- Carry a literal face through an occurrence embedding preserving its rows.
Only the image inside the original scope has to be exhaustive. -/
def through {S : Finset ι} {L : CellScheme S} {semL : Semantics L}
    (f : Cell K ↪ Cell L) (index : ∀ d, L.cell (f d) = K.cell d)
    (exhaustive : ∀ z, L.scope z ⊆ B → ∃ z', f z' = z)
    (row : ∀ (c : Cell K) (d : K.below (K.cell c)),
      semL.E (f c) ⟨f d.1, by rw [index, index]; exact d.2⟩ = semK.E c d) :
    ExactSemanticFace semD semL where
  map := F.map.trans f
  index d := (index (F.map d)).trans (F.index d)
  exhaustive z hz := by
    obtain ⟨e, rfl⟩ := exhaustive z hz
    obtain ⟨d, rfl⟩ := F.exhaustive e (by simpa only [CellScheme.scope, index] using hz)
    exact ⟨d, rfl⟩
  row c d := (row (F.map c) (F.belowMap c d)).trans (F.row c d)

include F in
/-- Every proper-target lifting clause transfers at the original cap. -/
theorem lift {CI BJ : Finset ι × ℕ} (hB : BJ.1 ⊆ B)
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan)
    (h : GradedLe CI BJ) (hb : semD.IsBountiful) : CoatomBoundaryExtension.CappedLift semK h :=
  F.patch.lift F.row h (fun d hd => F.exhaustive d (hd.1.trans hB))
    (CoatomBoundaryExtension.lift_of_bountiful hb hCI hBJ h)

end ExactSemanticFace

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace ExactSemanticFace

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {n : ℕ}
  {S : SemScheme n} {e : Fin n ↪ ι} {he : Finset.univ.image e = B}
  {D : CellScheme A} {sem : Semantics D}
  (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) sem)
  {i j : ℕ} (cut : ∀ d : Cell S.scheme, S.scheme.grade d ≤ i ↔ S.scheme.grade d ≤ j)

/-- The grade bound may be nominal or reduced to the arity of the face. -/
def fullEquiv : S.scheme.below (Finset.univ, i) ≃ D.below (B, j) :=
  (show S.scheme.below (Finset.univ, i) ≃
      (AmalgamatedBoundary.pointImage S.scheme e he).below (B, j) from {
    toFun := fun d => ⟨d.1,
      (Finset.image_subset_image (Finset.subset_univ _)).trans he.subset, (cut d.1).mp d.2.2⟩
    invFun := fun d => ⟨d.1, Finset.subset_univ _, (cut d.1).mpr d.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (G.belowEquiv (B, j) (Finset.Subset.refl _))

theorem full_respects_iff (q : D.below (B, j) → ExtOrd) :
    RespectsSemanticsBelow sem (B, j) q ↔
      RespectsSemanticsBelow S.rows (Finset.univ, i) (q ∘ G.fullEquiv cut) := by
  refine iff_comp_symm (G.fullEquiv cut).symm
    (respects_iff_of_equiv (G.fullEquiv cut) (fun d => (congrArg Prod.snd (G.index d.1)).symm)
          (fun d f => ?_)
      (fun c d _ => (G.row c.1 (PointImageSemantics.belowEquiv S.scheme e he c.1 d)).symm)) q
  change (S.scheme.cell d.1).1 ⊆ (S.scheme.cell f.1).1 ↔
    (D.cell (G.map d.1)).1 ⊆ (D.cell (G.map f.1)).1
  rw [G.index d.1, G.index f.1]
  exact (Finset.image_subset_image_iff e.injective).symm

end

end ExactSemanticFace

end VaughtConjecture.Knight
