
import GS.UnitaryLocalModel.DephasedNeighborhood
import GS.UnitaryLocalModel.DephasedDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace



/-!
# Standard real coordinates for the dephased unitary chart

The kernel chart is transported by a genuine continuous linear equivalence
to `Fin ((q - 1)^2) → ℝ`. No norm-preserving identification is asserted.
-/
noncomputable section
namespace GS.UnitaryLocalModel

variable (Q : FullUnitary q) (o : Fin q) (hQ : AnchorNonzero Q.val Q.val o)

/-- A continuous linear coordinate identification with the computed dimension. -/
def dephasedCoordinateEquiv :
    DephasedModel Q o ≃L[ℝ] (Fin ((q-1)^2) → ℝ) :=
  by
  apply ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := DephasedModel Q o) (F := Fin ((q-1)^2) → ℝ)
  simp only [Module.finrank_pi,Fintype.card_fin]
  have hd := LinearMap.finrank_range_add_finrank_ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)
  rw [anchorDerivative_range Q o hQ,finrank_top,
    ← (GS.UnitaryManifold.fullSkewCoordinateEquiv q).finrank_eq] at hd
  simp [AnchorCoordinates,GS.Mat,Module.finrank_matrix] at hd
  have hq : q - 1 + 1 = q := by have ho := o.isLt; omega
  
  nlinarith

def euclideanDephasedDomain : Set (Fin ((q-1)^2) → ℝ) :=
  (dephasedCoordinateEquiv Q o hQ).symm ⁻¹' dephasedChartDomain Q o hQ

def euclideanDephasedParametrization (x : Fin ((q-1)^2) → ℝ) : CMat q :=
  dephasedParametrization Q o hQ ((dephasedCoordinateEquiv Q o hQ).symm x)

variable (A : DephasedUnitary Q o)

def euclideanDephasedCoordinates  : Fin ((q-1)^2) → ℝ :=
  dephasedCoordinateEquiv Q o hQ (dephasedCoordinates Q o hQ A)

theorem euclideanDephasedDomain_open : IsOpen (euclideanDephasedDomain Q o hQ) :=
  (dephasedChartDomain_open Q o hQ).preimage (dephasedCoordinateEquiv Q o hQ).symm.continuous

theorem zero_mem_euclideanDephasedDomain :
    (0 : Fin ((q-1)^2) → ℝ) ∈ euclideanDephasedDomain Q o hQ := by
  change (dephasedCoordinateEquiv Q o hQ).symm 0 ∈ dephasedChartDomain Q o hQ
  simpa using zero_mem_dephasedChartDomain Q o hQ

@[simp] theorem euclideanDephasedParametrization_zero : euclideanDephasedParametrization Q o hQ 0 = Q.val := by
  simp [euclideanDephasedParametrization]

theorem euclideanDephasedParametrization_continuousOn :
    ContinuousOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) :=
  (dephasedParametrization_continuousOn Q o hQ).comp
    (dephasedCoordinateEquiv Q o hQ).symm.continuous.continuousOn (fun _ h => h)

theorem euclideanDephasedParametrization_injectiveOn :
    Set.InjOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) := by
  intro x hx y hy he
  apply (dephasedCoordinateEquiv Q o hQ).symm.injective
  exact dephasedParametrization_injectiveOn Q o hQ hx hy he

/-- The local homeomorphism in the standard real coordinate space. -/
def euclideanDephasedChartHomeomorph :
    dephasedChartSource Q o hQ ≃ₜ euclideanDephasedDomain Q o hQ :=
  (dephasedChartHomeomorph Q o hQ).trans
    ((dephasedCoordinateEquiv Q o hQ).toHomeomorph.subtype
      (fun x => by simp [euclideanDephasedDomain]))

theorem euclideanDephasedParametrization_coordinates 
    (hA : A ∈ dephasedChartSource Q o hQ) :
    euclideanDephasedParametrization Q o hQ (euclideanDephasedCoordinates Q o hQ A) = A.val.val := by
  simpa [euclideanDephasedParametrization, euclideanDephasedCoordinates] using
    dephasedParametrization_coordinates Q o hQ A hA

end GS.UnitaryLocalModel
