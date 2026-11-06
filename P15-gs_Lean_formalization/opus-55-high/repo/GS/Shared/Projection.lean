module

public import GS.Shared.Directions
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (right left : Pattern 𝕜 n) (X : 𝕄) : 𝕄 →L[ℝ] 𝕄 :=
  proj (pointDirections right left X)

theorem pointProjection_mem (X Z : 𝕄) :
    pointProjection right left X Z ∈ pointDirections right left X :=
  proj_mem _ _

theorem pointProjection_of_mem (X Y : 𝕄)
    (hY : Y ∈ pointDirections right left X) : pointProjection right left X Y = Y :=
  proj_of_mem _ _ hY

section
variable (X Z Y : 𝕄)
theorem pointProjection_normal (hY : Y ∈ pointDirections right left X) :
    frob (Z - pointProjection right left X Z) Y = 0 :=
  proj_normal _ _ _ hY

theorem pointProjection_self_adjoint :
    frob (pointProjection right left X Z) Y =
      frob Z (pointProjection right left X Y) :=
  proj_self_adjoint _ _ _

end

@[simp] theorem pointProjection_idempotent (X Z : 𝕄) :
    pointProjection right left X (pointProjection right left X Z) =
      pointProjection right left X Z :=
  pointProjection_of_mem X _ (pointProjection_mem X Z)

/-- Equivariance follows from the actual action isometry and the full range,
not an entrywise overlap mask. -/
theorem pointProjection_equivariant (g : Factors right left) (X Z : 𝕄) :
    pointProjection right left (g • X) (g • Z) =
      g • pointProjection right left X Z := by
  apply proj_unique_normal (pointDirections right left (g • X)) (g • Z)
  · exact action_mem_pointDirections g X _ (pointProjection_mem X Z)
  · intro Y hY
    have hback : g⁻¹ • Y ∈ pointDirections right left X := by
      simpa only [inv_smul_smul] using
        action_mem_pointDirections g⁻¹ (g • X) Y hY
    have he := action_frob g (Z - pointProjection right left X Z) (g⁻¹ • Y)
    rw [show g • (Z - pointProjection right left X Z) =
        g • Z - g • pointProjection right left X Z from
          by simp [Matrix.mul_sub, Matrix.sub_mul], smul_inv_smul] at he
    rw [he]
    exact pointProjection_normal X Z _ hback

end GS.Shared
