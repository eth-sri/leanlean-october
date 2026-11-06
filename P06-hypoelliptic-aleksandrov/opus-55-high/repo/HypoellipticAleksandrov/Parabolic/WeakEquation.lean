module

public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Homogeneous weak parabolic equations

This module defines the almost-everywhere ellipticity and homogeneous forward
parabolic equation predicates for selected time--velocity weak jets, together
with their invariance under almost-everywhere changes of value representative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- A lower Loewner bound holding almost everywhere after restriction to `U`. -/
def HasLowerEllipticityAEOn {d : ℕ} (lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ᵐ z ∂timeVelocityVolumeOn U, lam • (1 : PDE.Mat d) ≤ coefficientAt A z

namespace HasLowerEllipticityAEOn

end HasLowerEllipticityAEOn

namespace HasUpperEllipticityAEOn

end HasUpperEllipticityAEOn

namespace IsSymmetricCoefficientAEOn

end IsSymmetricCoefficientAEOn

/-- The selected-jet forward parabolic operator `w_t - A : D_v^2 w`. -/
def weakParabolicOperator {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (A : CoefficientField d) (w : ParabolicW12Function d U p)
    (z : TimeVelocity d) : ℝ :=
  w.timeDeriv z - matrixContraction (coefficientAt A z) (w.velocityHessian z)

/-- Evaluation of the selected-jet forward parabolic operator. -/
@[simp]
theorem weakParabolicOperator_apply {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (A : CoefficientField d) (w : ParabolicW12Function d U p)
    (z : TimeVelocity d) :
    weakParabolicOperator A w z =
      w.timeDeriv z - matrixContraction (coefficientAt A z) (w.velocityHessian z) :=
  rfl

/-- A selected weak jet solves the homogeneous forward equation almost everywhere. -/
def IsWeakParabolicEquationOn {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (A : CoefficientField d) (w : ParabolicW12Function d U p) : Prop :=
  weakParabolicOperator A w =ᵐ[timeVelocityVolumeOn U] 0

/-- A value representative satisfies the homogeneous equation through selected weak
jets on every compactly-contained open subdomain. -/
def IsWeakParabolicEquationLoc {d : ℕ} (A : CoefficientField d)
    (U : Set (TimeVelocity d)) (p : ℝ≥0∞) (u : TimeVelocity d → ℝ) : Prop :=
  ∀ V : Set (TimeVelocity d), IsOpen V → IsCompact (closure V) → closure V ⊆ U →
    ∃ w : ParabolicW12Function d V p,
      w.toFun =ᵐ[timeVelocityVolumeOn V] u ∧ IsWeakParabolicEquationOn A w

/-- A.e.-equal value representatives have a.e.-equal selected-jet operators.
No symmetry of the selected velocity Hessians is assumed. -/
theorem weakParabolicOperator_congr_ae_of_value_ae
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞} (A : CoefficientField d)
    (hU : IsOpen U) (hp : 1 ≤ p) (w w' : ParabolicW12Function d U p)
    (hvalue : w.toFun =ᵐ[timeVelocityVolumeOn U] w'.toFun) :
    weakParabolicOperator A w =ᵐ[timeVelocityVolumeOn U] weakParabolicOperator A w' := by
  rcases w.ae_eq_jet_of_value_ae hU hp w' hvalue with ⟨htime, _hgrad, hhess⟩
  have hhessAll : ∀ᵐ z ∂timeVelocityVolumeOn U,
      ∀ i j : Fin d, w.velocityHessian z i j = w'.velocityHessian z i j := by
    aesop
  filter_upwards [htime, hhessAll] with z htimez hhessz
  unfold weakParabolicOperator
  congr 1
  apply Finset.sum_congr rfl
  simp_all

namespace IsWeakParabolicEquationOn

/-- The homogeneous selected-jet equation is invariant under a.e.-equal values. -/
theorem congr_value_ae_iff {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    {A : CoefficientField d} (hU : IsOpen U) (hp : 1 ≤ p)
    (w w' : ParabolicW12Function d U p)
    (hvalue : w.toFun =ᵐ[timeVelocityVolumeOn U] w'.toFun) :
    IsWeakParabolicEquationOn A w ↔ IsWeakParabolicEquationOn A w' := by
  have hop := weakParabolicOperator_congr_ae_of_value_ae A hU hp w w' hvalue
  constructor
  · intro h
    exact hop.symm.trans h
  · intro h
    exact hop.trans h

end IsWeakParabolicEquationOn

namespace IsWeakParabolicEquationLoc

variable {d : ℕ} {A : CoefficientField d}

/-- A local homogeneous equation supplies the underlying local weak Sobolev data. -/
theorem parabolicW12Loc 
    {U : Set (TimeVelocity d)} {p : ℝ≥0∞} {u : TimeVelocity d → ℝ}
    (h : IsWeakParabolicEquationLoc A U p u) : ParabolicW12Loc U p u := by
  intro V hVOpen hVCompact hVU
  rcases h V hVOpen hVCompact hVU with ⟨w, hwu, _hweq⟩
  grind

/-- Every compatible selected jet on a compactly-contained open subdomain obeys
the local homogeneous equation. -/
theorem equationOn 
    {U V : Set (TimeVelocity d)} {p : ℝ≥0∞} {u : TimeVelocity d → ℝ}
    (h : IsWeakParabolicEquationLoc A U p u) (hVOpen : IsOpen V)
    (hVCompact : IsCompact (closure V)) (hVU : closure V ⊆ U) (hp : 1 ≤ p)
    (w : ParabolicW12Function d V p)
    (hwu : w.toFun =ᵐ[timeVelocityVolumeOn V] u) :
    IsWeakParabolicEquationOn A w := by
  rcases h V hVOpen hVCompact hVU with ⟨w', hw'u, hw'eq⟩
  exact (IsWeakParabolicEquationOn.congr_value_ae_iff hVOpen hp w' w
    (hw'u.trans hwu.symm)).mp hw'eq

end IsWeakParabolicEquationLoc

end HypoellipticAleksandrov.Parabolic
