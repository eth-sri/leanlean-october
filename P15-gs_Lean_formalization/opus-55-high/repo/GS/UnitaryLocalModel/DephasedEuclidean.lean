module

public import GS.UnitaryLocalModel.DephasedNeighborhood
public import GS.UnitaryLocalModel.DephasedDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section


/-!
# Standard real coordinates for the dephased unitary chart

The kernel chart is transported by a genuine continuous linear equivalence
to `Fin ((q - 1)^2) → ℝ`. No norm-preserving identification is asserted.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.UnitaryLocalModel
variable {q : ℕ}

section
variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)
/-- A continuous linear coordinate identification with the computed dimension. -/
def dephasedCoordinateEquiv :
    DephasedModel Q o ≃L[ℝ] (Fin ((q-1)^2) → ℝ) := by
  letI : Module.Free ℝ (DephasedModel Q o) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ (DephasedModel Q o))
  let b :=
    Module.finBasisOfFinrankEq ℝ (DephasedModel Q o) (finrank_dephasedModel Q o hQ)
  let e := b.equivFun
  exact LinearEquiv.toContinuousLinearEquiv
    (𝕜 := ℝ) (E := DephasedModel Q o) (F := Fin ((q-1)^2) → ℝ) e

def euclideanDephasedDomain : Set (Fin ((q-1)^2) → ℝ) :=
  (dephasedCoordinateEquiv Q o hQ).symm ⁻¹' dephasedChartDomain Q o hQ

def euclideanDephasedParametrization (x : Fin ((q-1)^2) → ℝ) : CMat q :=
  dephasedParametrization Q o hQ ((dephasedCoordinateEquiv Q o hQ).symm x)

def euclideanDephasedCoordinates (A : DephasedUnitary Q o) : Fin ((q-1)^2) → ℝ :=
  dephasedCoordinateEquiv Q o hQ (dephasedCoordinates Q o hQ A)

theorem euclideanDephasedDomain_open : IsOpen (euclideanDephasedDomain Q o hQ) :=
  (dephasedChartDomain_open Q o hQ).preimage (by fun_prop)

theorem zero_mem_euclideanDephasedDomain :
    (0 : Fin ((q-1)^2) → ℝ) ∈ euclideanDephasedDomain Q o hQ := by
  change (dephasedCoordinateEquiv Q o hQ).symm 0 ∈ dephasedChartDomain Q o hQ
  simpa using zero_mem_dephasedChartDomain Q o hQ

@[simp] theorem euclideanDephasedParametrization_zero : euclideanDephasedParametrization Q o hQ 0 = Q.val := by
  simp [euclideanDephasedParametrization]

theorem euclideanDephasedParametrization_continuousOn :
    ContinuousOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) :=
  (dephasedParametrization_continuousOn Q o hQ).comp
    (by fun_prop) (by tauto)

theorem euclideanDephasedParametrization_injectiveOn :
    Set.InjOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) := by
  intro x hx y hy he
  apply (dephasedCoordinateEquiv Q o hQ).symm.injective
  exact dephasedParametrization_injectiveOn Q o hQ hx hy he

theorem euclideanDephasedParametrization_coordinates (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    euclideanDephasedParametrization Q o hQ (euclideanDephasedCoordinates Q o hQ A) = A.val.val := by
  simpa [euclideanDephasedParametrization, euclideanDephasedCoordinates] using
    dephasedParametrization_coordinates Q o hQ A hA

end

end GS.UnitaryLocalModel
