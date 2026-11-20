module

public import HypoellipticAleksandrov.Geometry.Coordinates
public import PDEFoundation.Ambient.Basic

/-!
# Kinetic spacetime points

This module gives an explicit carrier for kinetic spacetime. Its fields make
the time, position, and velocity coordinate order visible in every theorem
surface.

## Main definitions

* `KineticPoint d` is a kinetic spacetime point with time, position, and
  velocity coordinates.
* `KineticPoint.homeomorphProd d` identifies this explicit carrier with
  `ℝ × (PDE.Vec d × PDE.Vec d)` for standard topology infrastructure.

## Implementation note

The transported product metric supplies only the ordinary topology and
uniformity used by sets, continuity, and compactness. It is not the
manuscript's Euclidean kinetic geometry; Euclidean norms and balls must use
the explicit `PDEFoundation` API.
-/

@[expose] public section

namespace HypoellipticAleksandrov

export KineticAleksandrovChallenge (KineticPoint)

attribute [ext] KineticAleksandrovChallenge.KineticPoint

namespace KineticPoint
export KineticAleksandrovChallenge.KineticPoint (time position velocity mk ext equivProd)
end KineticPoint

/-- The coordinate equivalence is an isometry for the transported standard product metric. -/
def KineticPoint.isometryEquivProd (d : ℕ) :
    KineticPoint d ≃ᵢ ℝ × (PDE.Vec d × PDE.Vec d) where
  toEquiv := KineticPoint.equivProd d
  isometry_toFun :=
    MetricSpace.isometry_induced (KineticPoint.equivProd d)
      (KineticPoint.equivProd d).injective

/-- The explicit coordinate homeomorphism with the standard nested product carrier. -/
def KineticPoint.homeomorphProd (d : ℕ) :
    KineticPoint d ≃ₜ ℝ × (PDE.Vec d × PDE.Vec d) :=
  (KineticPoint.isometryEquivProd d).toHomeomorph

section
variable {d : ℕ}

/-- The time projection is continuous for the standard product topology. -/
theorem continuous_time : Continuous (@KineticPoint.time d) :=
  continuous_fst.comp (KineticPoint.homeomorphProd d).continuous

/-- The position projection is continuous for the standard product topology. -/
theorem continuous_position : Continuous (@KineticPoint.position d) :=
  continuous_snd.fst.comp (KineticPoint.homeomorphProd d).continuous

/-- The velocity projection is continuous for the standard product topology. -/
theorem continuous_velocity : Continuous (@KineticPoint.velocity d) :=
  continuous_snd.snd.comp (KineticPoint.homeomorphProd d).continuous

end

/-- Assemble a continuous kinetic point from continuous coordinate functions. -/
theorem KineticPoint.continuous_mk
    {α : Type*} [TopologicalSpace α] {d : ℕ}
    {t : α → ℝ} {x v : α → PDE.Vec d}
    (ht : Continuous t) (hx : Continuous x) (hv : Continuous v) :
    Continuous (fun a => KineticPoint.mk (t a) (x a) (v a)) :=
  (KineticPoint.homeomorphProd d).symm.continuous.comp (ht.prodMk (hx.prodMk hv))

end HypoellipticAleksandrov
