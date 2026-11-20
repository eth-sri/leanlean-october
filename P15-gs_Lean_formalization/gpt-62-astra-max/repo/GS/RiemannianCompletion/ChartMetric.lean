module

public import GS.RiemannianCompletion.Gradient
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth compatible Frobenius coefficients in every orbit chart

These are the actual derivatives of the previously constructed inverse charts.
No regularity of the arbitrarily chosen preferredFactor is assumed. The metric
in an arbitrary chart is obtained by differentiating that chart's smooth matrix
reconstruction; compatibility is proved by differentiating the true transition
identity. Positivity at every point of every chart follows by comparison with
a preferred chart centred at the same matrix.

This file supplies coordinate-level metric regularity. Global smoothness on
the actual tangent bundle is proved in `GS.GlobalGeometry.TangentBundleMetric`.
No identification of chordal and intrinsic distances is asserted.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion Filter Set
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

end GS.RiemannianCompletion
