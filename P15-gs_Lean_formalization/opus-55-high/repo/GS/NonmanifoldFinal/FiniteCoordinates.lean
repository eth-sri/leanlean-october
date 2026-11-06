module

public import GS.Nonmanifold.OriginalCompactModel
public import GS.NonmanifoldObstruction.ProductSphere

@[expose] public section



/-!
# Finite coordinates for the actual GS local model

This file only changes coordinates by explicit homeomorphisms. In particular,
Matrix.rank and all induced topologies are retained. No nonmanifold hypothesis
is introduced. The coordinate maps are checked with the pinned Lean toolchain.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {ι κ ν : Type*}

/-- Reindex real coordinates; this preserves the product topology. -/
def reindexReal (e : ι ≃ κ) : (ι → ℝ) ≃ₜ (κ → ℝ) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Pack two independent coordinate arrays, without changing either norm. -/
def sumCoordinates : ((ι → ℝ) × (κ → ℝ)) ≃ₜ ((ι ⊕ κ) → ℝ) :=
  Homeomorph.sumArrowHomeomorphProdArrow.symm

/-- Change column labels in an actual two-row rank cone. -/
def reindexRankCone [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] (e : κ ≃ ν) : RankCone κ ≃ₜ RankCone ν where
  toFun W := ⟨fun i j => W.val i (e.symm j), rank_le_one_of_two_column_minors _ fun _ _ =>
    (rank_le_one_iff_minors W.val).mp W.property _ _⟩
  invFun W := ⟨fun i j => W.val i (e j), rank_le_one_of_two_column_minors _ fun _ _ =>
    (rank_le_one_iff_minors W.val).mp W.property _ _⟩
  left_inv W := by simp
  right_inv W := by simp


section
variable (q : ℕ)
/-- The exact combined type of unconstrained coordinates of the GS model. -/
abbrev FreeIndex := Fin q ⊕ (NonzeroIndex q ⊕ UpperIndex q)

def modelFreeCoordinates :
    ModelCoordinates q ≃ₜ ConeSpace (FreeIndex q) (UpperIndex q) where
  toFun p := (Sum.elim p.1 (Sum.elim p.2.1 p.2.2.1), p.2.2.2)
  invFun p := (fun i => p.1 (.inl i),
    fun j => p.1 (.inr (.inl j)), fun k => p.1 (.inr (.inr k)), p.2)
  left_inv p := rfl
  right_inv p := by aesop
  continuous_toFun := by
    refine .prodMk (continuous_pi fun i => ?_) (by fun_prop)
    rcases i with i|i|i <;> dsimp <;> fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem modelFreeCoordinates_zero :
    modelFreeCoordinates q (modelCoordinatesZero q) = productZero :=
  Prod.ext (funext fun i => by rcases i with i|i|i <;> rfl) rfl

end

section
variable [Fintype ι] [Fintype κ] [DecidableEq κ]
/-- Convert both finite index sets to Fin; the equality is topological, not an
unproved assertion that the default sup norm equals the Frobenius norm. -/
def coneCoordinatesToFin :
    ConeSpace ι κ ≃ₜ ConeSpace (Fin (Fintype.card ι)) (Fin (Fintype.card κ)) :=
  (reindexReal (Fintype.equivFin ι)).prodCongr
    (reindexRankCone (Fintype.equivFin κ))

@[simp] theorem coneCoordinatesToFin_zero :
    (coneCoordinatesToFin : ConeSpace ι κ ≃ₜ _) productZero = productZero :=
  rfl

end

section
variable (q : ℕ)
def modelToFin : ModelCoordinates q ≃ₜ
    ConeSpace (Fin (Fintype.card (FreeIndex q))) (Fin (Fintype.card (UpperIndex q))) :=
  (modelFreeCoordinates q).trans coneCoordinatesToFin

@[simp] theorem modelToFin_zero :
    modelToFin q (modelCoordinatesZero q) = productZero := by
  simp [modelToFin]

end

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


section
variable [Fintype ι] [Fintype κ] [DecidableEq κ] (hκ : 2 ≤ Fintype.card κ)
def coneCoordinatesExtra :
    ConeSpace ι κ ≃ₜ ConeSpace ι (Fin ((Fintype.card κ - 2) + 2)) :=
  (Homeomorph.refl (ι → ℝ)).prodCongr (reindexRankCone ((Fintype.equivFin κ).trans (Equiv.cast (by grind))))

@[simp] theorem coneCoordinatesExtra_zero :
    (coneCoordinatesExtra hκ : ConeSpace ι κ ≃ₜ _) productZero = productZero :=
  rfl

end

end GS.NonmanifoldFinal
