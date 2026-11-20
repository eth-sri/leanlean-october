module

public import GS.RiemannianCompletion.TangentMetric
public import GS.ManifoldCompletion.OrbitSmooth

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The gradient of an actual restricted loss on the no-overlap orbit

The differential in the Riesz identity is mathlib's mfderiv of f restricted to
MatrixOrbit. The ambient gradient is obtained from the actual fderiv; it is not
an input assumed to represent the derivative. The unique tangent lift of the
old matrix projector defines the vector, and the Riesz identity is PROVED.

No norm instance is installed: the chart norm and the Frobenius metric are
kept distinct. Smooth metric evaluation on the total tangent bundle is proved
in `GS.GlobalGeometry.TangentBundleMetric`.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- This vector inhabits mathlib's TangentSpace for the constructed atlas. -/
def intrinsicGradient (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X :=
  tangentProjection σ X (ambientGradient f X.val)

@[simp] theorem intrinsicGradient_ambient (f : Mat n → ℝ)
    (X : MatrixOrbit block₁ block₂ (permMatrix σ)) :
    inclusionDifferential σ X (intrinsicGradient σ f X) =
      pointProjection block₁ block₂ X.val (ambientGradient f X.val) :=
  inclusion_tangentProjection σ X _

end GS.RiemannianCompletion
