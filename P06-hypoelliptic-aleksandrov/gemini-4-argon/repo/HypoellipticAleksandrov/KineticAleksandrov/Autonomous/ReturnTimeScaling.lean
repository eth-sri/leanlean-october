module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters

/-! # Normalization of the actual canonical autonomous solution at arbitrary scales -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory SectionTwo Evolution TheoremA
open HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/- The kinetic scaling keeps physical position translations and does not shift velocity. -/
def returnScaling (r : ℝ) (hr : 0 < r) (X : ℝ) : Scaling.KineticAffineScaling 1 :=
  ⟨r ^ 2, r, r ^ 3, 0, 0, fun _ => X, 0, by positivity, hr, by positivity⟩

/- The scaled autonomous coefficient retains exactly the original ellipticity constants. -/
def returnScaledCoefficient {lam Lam } (A : SmoothAutonomous lam Lam) (r X : ℝ) :
    SmoothAutonomous lam Lam where
  a x v := A.a (X + r ^ 3 * x) (r * v)
  smooth := by
    change ContDiff ℝ (⊤ : ℕ∞)
      ((Function.uncurry A.a) ∘ fun z : ℝ × ℝ => (X + r ^ 3 * z.1, r * z.2))
    exact A.smooth.comp (by fun_prop)
  bounds x v := A.bounds _ _

/- The scaled full coefficient is the literal autonomous coefficient of the scaled scalar. -/
theorem returnScaling_drift (r : ℝ) (hr : 0 < r) (X : ℝ) :
    (returnScaling r hr X).drift (identityDrift 1) = identityDrift 1 := by
  funext y
  ext i
  simp [Scaling.KineticAffineScaling.drift, Scaling.KineticAffineScaling.position,
    returnScaling, identityDrift]
  field_simp

/- A normalized classical homogeneous solution represents the original canonical action.
The existence assertion is proved from the full-space producer; it is not a premise. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
