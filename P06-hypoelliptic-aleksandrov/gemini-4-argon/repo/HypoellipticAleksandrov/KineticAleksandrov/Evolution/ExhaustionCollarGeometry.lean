module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarTransfer

/-!
# The ball containing the finite ellipsoid

Membership in the actual closed ellipsoid implies the Euclidean diffused block radius
bound needed for the collar barrier. No description of the ellipsoid frontier is assumed.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology

/- The closed straightened ellipsoid lies in the closed diffused block ball. -/
theorem vecNormSq_spatialY_le_of_mem_closure_straightenedEllipsoid
    {n : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {x : PDE.Vec (n + n)}
    (hx : x ∈ closure (openEllipsoid (straightenedEllipsoidMatrix n r R))) :
    PDE.vecNormSq (spatialY x) ≤ r ^ 2 := by
  have hc : IsClosed {x : PDE.Vec (n + n) | PDE.vecNormSq (spatialY x) ≤ r ^ 2} :=
    isClosed_le (PDE.continuous_vecNormSq.comp (contDiff_spatialY (m := 0)).continuous)
      continuous_const
  apply closure_minimal (s := openEllipsoid (straightenedEllipsoidMatrix n r R)) ?_ hc hx
  intro y hy
  have hsum := (straightenedEllipsoid_characterization n r R hr hR).2 y |>.mp hy
  have hZ := div_nonneg (PDE.vecNormSq_nonneg (spatialZ y)) (sq_nonneg R)
  exact ((div_lt_one (sq_pos_of_pos hr)).mp (by linarith)).le

/- Future neighbourhoods of active finite-cylinder points remain in the closed cylinder. -/
end HypoellipticAleksandrov.KineticAleksandrov
