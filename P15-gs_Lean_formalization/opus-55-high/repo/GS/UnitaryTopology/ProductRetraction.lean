module

public import GS.UnitaryTopology.EuclideanRetract
public import GS.UnitaryTopology.QuaternionRetraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The Clifford retraction with arbitrary Euclidean factors

The singular zero-matrix stratum is retained. The sole deleted point is the
origin of the full product. The Euclidean projection has exactly that zero.
-/
noncomputable section
open GS.NonmanifoldFinal GS.NonmanifoldClosure
namespace GS.UnitaryTopology

section
variable (e r : ℕ)
def pairCoordinatesEuclidean : ((Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) ≃ₜ Eucl (e+r*4) :=
  (sumCoordinates.trans (reindexReal ((Fintype.equivFin _).trans (finCongr (by simp))))).trans
    (EuclideanSpace.equiv _ ℝ).symm.toHomeomorph

@[simp] theorem pairCoordinatesEuclidean_zero :
    pairCoordinatesEuclidean e r (0,0) = 0 := by
  ext i
  simp [pairCoordinatesEuclidean,sumCoordinates,reindexReal]

end

end GS.UnitaryTopology
