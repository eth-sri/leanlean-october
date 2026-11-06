module

public import HypoellipticAleksandrov.Measure.LpProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure

/-!
# Reverse-time gradient coordinate product representatives

This module gives scalar product representatives for the finitely many
coordinates of the quotient-valued spatial weak gradient of a reverse-time
Bochner curve.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/- The Bochner lift of one scalar coordinate of the spatial weak-gradient
map. -/
noncomputable def reverseTimeGradientCoordCLM
    {d } {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (j : Fin d) :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2H hΩ T :=
  ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp
    (gradientCLM hΩ)).compLpL (2 : ℝ≥0∞) (reverseTimeVolume T)

/- The reverse-time gradient-coordinate lift agrees almost everywhere with
the corresponding timewise spatial coordinate map. -/
end HypoellipticAleksandrov.Parabolic.Dirichlet
