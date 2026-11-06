module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import GS.UnitaryTopology.Nonmanifold
public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryManifold.CayleyCharts

@[expose] public section


/-!
# Transport of the cone obstruction through actual local models

An arbitrary locally Euclidean outer factor can be absorbed into the free
coordinates of the rank-three-row model. Finite tuples of the actual unitary
block groups are locally Euclidean by the existing Cayley charts, with their
inherited matrix topology. The final transfer accepts a proved pointed open
or neighbourhood model; it introduces no nonmanifold hypothesis.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.NonmanifoldFinal GS.NonmanifoldClosure GS.NonmanifoldObstruction
open GS.UnitaryManifold GS.UnitaryLocalModel
namespace GS.UnitaryTopology

section
variable (n d : ℕ)
/-- Pack the outer Euclidean coordinates and the unconstrained cone center. -/
def euclideanConeCoordinates :
    (Eucl n × ConeCoordinates d) ≃ₜ
      ((Fin (n+d) → ℝ) × RankThreeCone (Fin d)) :=
  (((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.prodCongr
      (Homeomorph.refl (ConeCoordinates d))).trans
    (Homeomorph.prodAssoc _ _ _).symm).trans
      ((sumCoordinates.trans (reindexReal finSumFinEquiv)).prodCongr
        (Homeomorph.refl _))

@[simp] theorem euclideanConeCoordinates_zero :
    euclideanConeCoordinates n d (0,coneCoordinatesZero d) = (0,rankThreeZero) :=
  Prod.ext (funext fun i => by simp [euclideanConeCoordinates, sumCoordinates, reindexReal, coneCoordinatesZero, Homeomorph.prodAssoc]) rfl

end

end GS.UnitaryTopology
