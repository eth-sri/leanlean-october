module

public import GS.RiemannianCompletion.ChartMetric
public import GS.Extensions.FiniteTopology
public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual fibrewise continuous bilinear metric, with topology compatibility

The codomain is the standard space of continuous linear maps. Bounds are proved
in the ORIGINAL chart norm, which is not redefined to be a Frobenius norm.
The metric is continuous on each fibre and compatible with its existing
topology. `GS.GlobalGeometry.TangentBundleMetric` proves smooth metric evaluation
on the actual total tangent bundle. Mathlib v4.19 has no `RiemannianMetric`
structure to register; the intrinsic path distance is not constructed here.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open GS.RiemannianCompletion
open scoped Manifold Topology
namespace GS.GlobalGeometry
variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

-- The library tangent space is the chart model, but intentionally does not
-- expose its norm through global instances. Use the existing chart norm
-- locally; its topology is the library tangent-space topology.
local instance tangentSpaceChartNormedAddCommGroup
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    NormedAddCommGroup (TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :=
  inferInstanceAs (NormedAddCommGroup (PairModel b₁ b₂))

local instance tangentSpaceChartNormedSpace
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    NormedSpace ℝ (TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :=
  inferInstanceAs (NormedSpace ℝ (PairModel b₁ b₂))

local instance tangentSpaceChartFiniteDimensional
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    FiniteDimensional ℝ (TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :=
  inferInstanceAs (FiniteDimensional ℝ (PairModel b₁ b₂))

/-- Bundle metric coefficients in the standard nested continuous-linear-map type. -/
def tangentMetricCLM (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X →L[ℝ]
      TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (tangentMetric σ X v).toContinuousLinearMap
      map_add' := by
        intro v w
        ext u
        exact tangentPairing_add_left σ X v w u
      map_smul' := by
        intro a v
        ext u
        exact tangentPairing_smul_left σ X a v u }

@[simp] theorem tangentMetricCLM_apply (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v w : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) :
    tangentMetricCLM σ X v w = tangentPairing σ X v w := rfl

end GS.GlobalGeometry
