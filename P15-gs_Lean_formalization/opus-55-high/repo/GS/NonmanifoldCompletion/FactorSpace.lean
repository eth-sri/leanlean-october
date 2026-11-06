module

public import GS.NonmanifoldCompletion.BlockRealization
public import GS.Extensions.FiniteTopology
public import GS.Extensions.TransportedProjection
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Core

@[expose] public section


noncomputable section
namespace GS.NonmanifoldCompletion

/-- Extracting the actual scalar block equations at the marked image point. -/
theorem smallFactorMap_eq_base_blocks {q : ℕ} (Q₀ : Mat q)
    (p : SmallBlockParameters ℝ q) (he : smallFactorMap p=basePoint Q₀) (i j : Fin q) :
    p.1 i * diagTwo (p.2.1 i j) (p.2.2.1 i j) * p.2.2.2 j = Q₀ i j • (1 : Mat 2) := by
  ext a b
  have hh := congrFun (congrFun he (finProdFinEquiv (i,a))) (finProdFinEquiv (j,b))
  rw [smallFactorMap_block] at hh
  have hi : finProdFinEquiv.symm (finProdFinEquiv (i,a)) = (i,a) :=
    Equiv.symm_apply_apply _ _
  have hj : finProdFinEquiv.symm (finProdFinEquiv (j,b)) = (j,b) :=
    Equiv.symm_apply_apply _ _
  dsimp only [basePoint] at hh
  rw [hi,hj] at hh
  omega

end GS.NonmanifoldCompletion
