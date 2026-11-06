module

public import GS.UnitaryTopology.QuaternionRetraction
public import GS.NonmanifoldFinal.EuclideanTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Column reindexing of the actual three-row rank cone

The maps preserve mathlib's matrix rank and the inherited matrix topology.
They allow a four-column-block Clifford construction to be stated at an
ordinary scalar matrix width.
-/
noncomputable section
open Matrix GS GS.NonmanifoldFinal
namespace GS.UnitaryTopology

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

def rankThreeReindex (e : κ ≃ ν) : RankThreeCone κ ≃ₜ RankThreeCone ν where
  toFun W := ⟨W.val.reindex (Equiv.refl _) e, by
    simpa only [Matrix.rank_reindex] using W.property⟩
  invFun W := ⟨W.val.reindex (Equiv.refl _) e.symm, by
    simpa only [Matrix.rank_reindex] using W.property⟩
  left_inv W := by
    apply Subtype.ext
    ext i j
    simp
  right_inv W := by
    apply Subtype.ext
    ext i j
    simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun W : RankThreeCone κ => W.val i (e.symm j))
    exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun W : RankThreeCone ν => W.val i (e j))
    exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

@[simp] theorem rankThreeReindex_zero (e : κ ≃ ν) :
    rankThreeReindex e rankThreeZero = rankThreeZero := by
  apply Subtype.ext
  ext i j
  rfl

def productRankThreeReindex (e : ℕ) (f : κ ≃ ν) :
    ((Fin e → ℝ) × RankThreeCone κ) ≃ₜ ((Fin e → ℝ) × RankThreeCone ν) :=
  (Homeomorph.refl _).prodCongr (rankThreeReindex f)

@[simp] theorem productRankThreeReindex_zero (e : ℕ) (f : κ ≃ ν) :
    productRankThreeReindex e f (0,rankThreeZero) = (0,rankThreeZero) := by
  exact Prod.ext rfl (rankThreeReindex_zero f)

end GS.UnitaryTopology
