module

public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



/-!
# Weak derivatives on time--velocity space

This module defines the representative-level anisotropic weak-derivative data
used for the time--velocity parabolic regularity surface.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

/-- Product Lebesgue volume restricted to a time--velocity set. -/
abbrev timeVelocityVolumeOn {d : Nat} (U : HypoellipticAleksandrov.Parabolic.Region d) :
    Measure (TimeVelocity d) :=
  volume.restrict U

/-- Restricted-product-volume `L^p` membership on time--velocity space. -/
abbrev ParabolicMemLpOn {d : Nat} (U : HypoellipticAleksandrov.Parabolic.Region d) (p : ℝ≥0∞)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) : Prop :=
  MeasureTheory.MemLp f p (timeVelocityVolumeOn U)

variable {d : Nat} (U : HypoellipticAleksandrov.Parabolic.Region d)

/-- The distributional time derivative relation on a raw time--velocity set. -/
def HasWeakTimeDerivOn
    (u du : HypoellipticAleksandrov.Parabolic.ScalarField d) : Prop :=
  ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d,
    ContDiff ℝ PDE.smoothOrder φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    (∫ z in U, u z * timeDerivative φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      -∫ z in U, du z * φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)

/-- The distributional derivative relation in one velocity coordinate on a raw
time--velocity set. -/
def HasWeakVelocityPartialDerivOn
    (i : Fin d) (u dui : HypoellipticAleksandrov.Parabolic.ScalarField d) : Prop :=
  ∀ φ : HypoellipticAleksandrov.Parabolic.ScalarField d,
    ContDiff ℝ PDE.smoothOrder φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    (∫ z in U, u z * velocityGradient φ z i
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      -∫ z in U, dui z * φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)

/-- A representative-level anisotropic weak `W^{1,2,p}` jet on a raw
time--velocity set. -/
structure ParabolicW12Function (d : Nat) (U : HypoellipticAleksandrov.Parabolic.Region d) (p : ℝ≥0∞) where
  toFun : HypoellipticAleksandrov.Parabolic.ScalarField d
  timeDeriv : HypoellipticAleksandrov.Parabolic.ScalarField d
  velocityGrad : TimeVelocity d → PDE.Vec d
  velocityHessian : TimeVelocity d → PDE.Mat d
  memLp : ParabolicMemLpOn U p toFun
  timeDeriv_memLp : ParabolicMemLpOn U p timeDeriv
  velocityGrad_memLp : ∀ i : Fin d,
    ParabolicMemLpOn U p (fun z => velocityGrad z i)
  velocityHessian_memLp : ∀ i j : Fin d,
    ParabolicMemLpOn U p (fun z => velocityHessian z i j)
  hasWeakTimeDeriv : HasWeakTimeDerivOn U toFun timeDeriv
  hasWeakVelocityPartialDeriv : ∀ i : Fin d,
    HasWeakVelocityPartialDerivOn U i toFun (fun z => velocityGrad z i)
  hasWeakVelocitySecondPartialDeriv : ∀ i j : Fin d,
    HasWeakVelocityPartialDerivOn U j (fun z => velocityGrad z i)
      (fun z => velocityHessian z i j)

end HypoellipticAleksandrov.Parabolic
