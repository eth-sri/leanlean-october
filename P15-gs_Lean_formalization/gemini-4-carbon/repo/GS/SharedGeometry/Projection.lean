module

public import GS.SharedGeometry.Directions
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical continuous projector on each shared orbit

The projector is a function of the matrix point and ambient vector, not of a
chosen factorization.  It equals the existing exact coupled shared projection
at every valid factor pair.  Joint continuity on the actual matrix orbit is
proved by descent through the open orbit map; no continuous choice of factors
and no smooth shared-orbit atlas is assumed.

These statements concern the actual generator range.  Calling it the full
manifold tangent space still requires the shared-orbit atlas.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (right left : Pattern n) (X : Mat n) : Mat n →L[ℝ] Mat n :=
  frobProjection (pointDirections right left X)

theorem pointProjection_mem (X Z : Mat n) :
    pointProjection right left X Z ∈ pointDirections right left X :=
  frobProjection_mem _ _

theorem pointProjection_of_mem (X Y : Mat n)
    (hY : Y ∈ pointDirections right left X) : pointProjection right left X Y = Y :=
  frobProjection_of_mem _ _ hY

theorem pointProjection_normal (X Z Y : Mat n)
    (hY : Y ∈ pointDirections right left X) :
    frobInner (Z - pointProjection right left X Z) Y = 0 :=
  frobProjection_normal _ _ _ hY

theorem pointProjection_self_adjoint (X Z Y : Mat n) :
    frobInner (pointProjection right left X Z) Y =
      frobInner Z (pointProjection right left X Y) :=
  frobProjection_self_adjoint _ _ _

@[simp] theorem pointProjection_idempotent (X Z : Mat n) :
    pointProjection right left X (pointProjection right left X Z) =
      pointProjection right left X Z :=
  pointProjection_of_mem X _ (pointProjection_mem X Z)

/-- Equivariance follows from the actual action isometry and the full range,
not an entrywise overlap mask. -/
theorem pointProjection_equivariant (g : Factors right left) (X Z : Mat n) :
    pointProjection right left (g • X) (g • Z) =
      g • pointProjection right left X Z := by
  apply frobProjection_unique_normal (pointDirections right left (g • X)) (g • Z)
  · exact action_mem_pointDirections g X _ (pointProjection_mem X Z)
  · intro Y hY
    have hback : g⁻¹ • Y ∈ pointDirections right left X := by
      simpa only [inv_smul_smul] using
        action_mem_pointDirections g⁻¹ (g • X) Y hY
    have he := action_frobInner g (Z - pointProjection right left X Z) (g⁻¹ • Y)
    rw [show g • (Z - pointProjection right left X Z) =
        g • Z - g • pointProjection right left X Z from
          (actionLinearEquiv g).map_sub _ _, smul_inv_smul] at he
    rw [he]
    exact pointProjection_normal X Z _ hback

end GS.SharedGeometry
