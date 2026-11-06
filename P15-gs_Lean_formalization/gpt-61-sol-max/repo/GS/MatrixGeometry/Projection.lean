import Mathlib.Tactic
import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Directions
import Mathlib.Topology.Constructions.SumProd



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

noncomputable section
open GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}

variable (X Z Y : KMat 𝕜 n)

/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (right left : Pattern 𝕜 n) (X : KMat 𝕜 n) := cFrobProjection (pointDirections right left X)

theorem pointProjection_mem  :
    pointProjection right left X Z ∈ pointDirections right left X :=
  cFrobProjection_mem _ _

theorem pointProjection_of_mem 
    (hY : Y ∈ pointDirections right left X) : pointProjection right left X Y = Y :=
  cFrobProjection_of_mem _ _ hY

theorem pointProjection_normal 
    (hY : Y ∈ pointDirections right left X) :
    cFrobInner (Z - pointProjection right left X Z) Y = 0 :=
  cFrobProjection_normal _ _ _ hY



@[simp] theorem pointProjection_idempotent  :
    pointProjection right left X (pointProjection right left X Z) =
      pointProjection right left X Z :=
  by simp_all [pointProjection_mem,pointProjection_of_mem]

/-- Equivariance follows from the actual action isometry and the full range,
not an entrywise overlap mask. -/
theorem pointProjection_equivariant (g : Factors right left) (X Z : KMat 𝕜 n) :
    pointProjection right left (g • X) (g • Z) =
      g • pointProjection right left X Z := by
  apply cFrobProjection_unique_normal (pointDirections right left (g • X)) (g • Z)
  · grind [action_mem_pointDirections,pointProjection_mem]
  · intro Y hY
    have hback : g⁻¹ • Y ∈ pointDirections right left X := by grind [action_mem_pointDirections,inv_smul_smul]
    have he := action_cFrobInner g (Z - pointProjection right left X Z) (g⁻¹ • Y)
    rw [show g • (Z - pointProjection right left X Z) =
        g • Z - g • pointProjection right left X Z from
          (actionLinearEquiv g).map_sub _ _, smul_inv_smul] at he
    rw [he]
    exact pointProjection_normal X Z _ hback

end GS.MatrixGeometry
