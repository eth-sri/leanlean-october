module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareFoundation

/-!
# Time-slice parabolic moment projections

This module fixes the canonical velocity-cube moment-affine projection at each
time separately. It contains only the shared definitions used by the spatial
and temporal parabolic Poincare estimates.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

variable {d : Nat} (u : HypoellipticAleksandrov.Parabolic.ScalarField d)

variable (t : Real)

/-- The normalized velocity-cube average at a fixed time. -/
def parabolicMorreyUnitVelocityAverage   : Real :=
  ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹ *
    ∫ v in velocityCube 0 1, u (t, v)

/-- The normalized `i`th velocity moment coefficient at a fixed time. -/
def parabolicMorreyUnitVelocityCoeffAt   (i : Fin d) : Real :=
  3 * ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹ *
    ∫ v in velocityCube 0 1, u (t, v) * v i

/-- The canonical moment-affine velocity projection, performed separately at
each time. -/
def parabolicMorreyUnitSpatialAffineProjection  : HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => parabolicMorreyUnitVelocityAverage u z.1 +
    ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt u z.1 i * z.2 i

end HypoellipticAleksandrov.Parabolic
