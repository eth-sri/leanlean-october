
import GS.Nonmanifold.OriginalCompactModel
import GS.NonmanifoldObstruction.ProductSphere
import GS.Topology.RankReindex



/-!
# Finite coordinates for the actual GS local model

This file only changes coordinates by explicit homeomorphisms. In particular,
Matrix.rank and all induced topologies are retained. No nonmanifold hypothesis
is introduced. The coordinate maps are checked with the pinned Lean toolchain.
-/
noncomputable section
open GS.Nonmanifold GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {ι κ ν : Type*}

variable (q : ℕ)

/-- Pack two independent coordinate arrays, without changing either norm. -/
def sumCoordinates : ((ι → ℝ) × (κ → ℝ)) ≃ₜ ((ι ⊕ κ) → ℝ) :=
  Homeomorph.sumArrowHomeomorphProdArrow.symm

/-- Change column labels in an actual two-row rank cone. -/
def reindexRankCone [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] (e : κ ≃ ν) : RankCone κ ≃ₜ RankCone ν :=
  GS.Topology.reindexRankOne e



/-- The exact combined type of unconstrained coordinates of the GS model. -/
abbrev FreeIndex  := Fin q ⊕ (NonzeroIndex q ⊕ UpperIndex q)

def modelFreeCoordinates  :
    ModelCoordinates q ≃ₜ ConeSpace (FreeIndex q) (UpperIndex q) :=
  ((Homeomorph.refl _).prodCongr (Homeomorph.prodAssoc _ _ _).symm).trans
    ((Homeomorph.prodAssoc _ _ _).symm.trans
      ((((Homeomorph.refl _).prodCongr sumCoordinates).trans sumCoordinates).prodCongr
        (Homeomorph.refl _)))

@[simp] theorem modelFreeCoordinates_zero  :
    modelFreeCoordinates q (modelCoordinatesZero q) = productZero := by aesop

/-- Relate the product of a cone subtype to the ambient subset in the ORIGINAL
ConeProductNonManifoldGoal, not to a replacement definition of the cone. -/
def flattenConeProduct [Fintype ι] [Fintype κ] [DecidableEq κ] :
    ConeSpace ι κ ≃ₜ
      {p : (ι → ℝ) × Matrix (Fin 2) κ ℝ // p.2.rank ≤ 1} where
  toFun p := ⟨(p.1,p.2.val),p.2.property⟩
  invFun p := (p.val.1,⟨p.val.2,p.property⟩)
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop



/-- Reindex the width as d+2, as required by the explicitly constructed section.
The parameter d here counts EXTRA columns, not the article's total width. -/
def widthEquivExtra (κ : Type*) [Fintype κ] (hκ : 2 ≤ Fintype.card κ) := (Fintype.equivFin κ).trans
    (Equiv.cast (congrArg Fin (Nat.sub_add_cancel hκ).symm))

def coneCoordinatesExtra [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hκ : 2 ≤ Fintype.card κ) :
    ConeSpace ι κ ≃ₜ ConeSpace ι (Fin ((Fintype.card κ - 2) + 2)) :=
  (Homeomorph.refl (ι → ℝ)).prodCongr (reindexRankCone (widthEquivExtra κ hκ))



end GS.NonmanifoldFinal
