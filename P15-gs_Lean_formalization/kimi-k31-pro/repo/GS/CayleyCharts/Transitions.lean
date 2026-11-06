module

public import GS.CayleyCharts.BlockCharts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth transitions and coordinate expressions of group operations

All domains are explicit determinant-nonvanishing conditions. The transition
formulas are linked to the actual chart inverse identities. Smoothness of a
formal ambient expression is not substituted for the inverse identity.
No `LieGroup` or `IsManifold` instance is postulated here; `Atlas.lean`
constructs the manifold instance from these checked charts.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction Filter
open scoped Topology
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

def transition (Q V : BlockO block) (x : Model block) : Model block :=
  chartMap V (chartInv Q x)

def transitionDomain (Q V : BlockO block) : Set (Model block) :=
  {x | x ∈ parameterDomain block ∧ admissible (V.valᵀ * chartInv Q x)}

theorem transition_smooth_at (Q V : BlockO block) (x : Model block)
    (hx : x ∈ transitionDomain Q V) : ContDiffAt ℝ ⊤ (transition Q V) x :=
  (chartMap_smooth_at V (chartInv Q x) hx.2).comp x (chartInv_smooth_at Q x hx.1)

end GS.CayleyCharts
