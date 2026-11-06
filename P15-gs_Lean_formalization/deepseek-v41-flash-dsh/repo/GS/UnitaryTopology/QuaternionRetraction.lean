module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.ComplexAlgebra
public import GS.Continuation.ExponentialBasics
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.OriginalGImage
public import GS.Nonmanifold.CircleRetract
public import GS.Nonmanifold.RadialCone
public import GS.Nonmanifold.RankOneGeometry
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.NonmanifoldObstruction.HomogeneousRetraction
public import GS.NonmanifoldObstruction.ProductSphere
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryLocalModel.OuterFibres
public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.UnitaryLocalModel.RankCone
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A Clifford contraction of the real three-row rank-one cone

For a width divisible by four, two orthogonal anticommuting complex structures
give a linear contraction onto the column space. Its squared Euclidean norm
equals the Frobenius square on rank-one matrices. The first-row section is an
exact right inverse. In particular the contraction has no additional zeros.
-/
noncomputable section
open Matrix GS GS.UnitaryLocalModel GS.NonmanifoldObstruction
open scoped BigOperators
namespace GS.UnitaryTopology

abbrev RankThreeCone (κ : Type*) [Fintype κ] :=
  {W : Matrix (Fin 3) κ ℝ // W.rank ≤ 1}

def rankThreeZero {κ : Type*} [Fintype κ] : RankThreeCone κ := ⟨0,by simp⟩

def quaternionContraction {r : ℕ} (W : Matrix (Fin 3) (Fin r × Fin 4) ℝ) :
    Fin r × Fin 4 → ℝ := fun j =>
  ![W 0 (j.1,0)-W 1 (j.1,1)-W 2 (j.1,2),
    W 0 (j.1,1)+W 1 (j.1,0)+W 2 (j.1,3),
    W 0 (j.1,2)-W 1 (j.1,3)+W 2 (j.1,0),
    W 0 (j.1,3)+W 1 (j.1,2)-W 2 (j.1,1)] j.2

theorem continuous_quaternionContraction (r : ℕ) :
    Continuous (@quaternionContraction r) := by
  apply continuous_pi
  intro j
  rcases j with ⟨j,a⟩
  fin_cases a <;> simp [quaternionContraction] <;> fun_prop

theorem quaternionContraction_outer_square {r : ℕ}
    (u : AxisVector) (z : Fin r × Fin 4 → ℝ) (j : Fin r) :
    (∑ a : Fin 4, quaternionContraction (sphereOuter u z) (j,a)^2) =
      (u 0^2+u 1^2+u 2^2) * (∑ a : Fin 4, z (j,a)^2) := by
  norm_num [quaternionContraction,sphereOuter,Fin.sum_univ_succ,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  ring

theorem quaternionContraction_preserves_square {r : ℕ}
    (W : RankThreeCone (Fin r × Fin 4)) :
    vectorSq (quaternionContraction W.val) = frobSq W.val := by
  obtain ⟨u,hu,z,hz⟩ := exists_sphereOuter_of_rank_le_one W.val W.property
  rw [← hz,frobSq_sphereOuter hu]
  simp only [vectorSq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quaternionContraction_outer_square,hu,one_mul]

def firstRowSection {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → ℝ) :
    RankThreeCone κ :=
  ⟨sphereOuter (fun i => if i=0 then 1 else 0) z,rank_sphereOuter_le_one _ _⟩

theorem continuous_firstRowSection {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Continuous (@firstRowSection κ _ _) := by
  apply Continuous.subtype_mk
  unfold sphereOuter
  fun_prop

@[simp] theorem firstRowSection_zero {κ : Type*} [Fintype κ] [DecidableEq κ] :
    firstRowSection (0 : κ → ℝ) = rankThreeZero := by
  apply Subtype.ext
  ext i j
  simp [firstRowSection,sphereOuter,rankThreeZero]

@[simp] theorem quaternionContraction_section {r : ℕ} (z : Fin r × Fin 4 → ℝ) :
    quaternionContraction (firstRowSection z).val = z := by
  funext j
  rcases j with ⟨j,a⟩
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  fin_cases a <;> norm_num [quaternionContraction,firstRowSection,sphereOuter,h20] <;> rfl

theorem quaternionContraction_zero_iff {r : ℕ} (W : RankThreeCone (Fin r × Fin 4)) :
    quaternionContraction W.val = 0 ↔ W = rankThreeZero := by
  constructor
  · intro he
    have hs := quaternionContraction_preserves_square W
    rw [he] at hs
    have hW : frobSq W.val = 0 := by simpa [vectorSq] using hs.symm
    exact Subtype.ext ((frobSq_eq_zero_iff W.val).mp hW)
  · rintro rfl
    funext j
    rcases j with ⟨j,a⟩
    fin_cases a <;> norm_num [quaternionContraction,rankThreeZero]

end GS.UnitaryTopology
