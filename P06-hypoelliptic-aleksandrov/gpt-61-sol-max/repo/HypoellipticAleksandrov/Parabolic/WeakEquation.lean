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
    (U : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ∀ᵐ z ∂timeVelocityVolumeOn U, lam • (1 : PDE.Mat d) ≤ coefficientAt A z







/-- The selected-jet forward parabolic operator `w_t - A : D_v^2 w`. -/
def weakParabolicOperator {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
    (A : CoefficientField d) (w : ParabolicW12Function d U p)
    (z : TimeVelocity d) : ℝ :=
  w.timeDeriv z - matrixContraction (coefficientAt A z) (w.velocityHessian z)

variable {d : ℕ}

variable {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} (A : CoefficientField d) (w : ParabolicW12Function d U p)



/-- A selected weak jet solves the homogeneous forward equation almost everywhere. -/
def IsWeakParabolicEquationOn   : Prop :=
  weakParabolicOperator A w =ᵐ[timeVelocityVolumeOn U] 0

/-- A value representative satisfies the homogeneous equation through selected weak
jets on every compactly-contained open subdomain. -/
def IsWeakParabolicEquationLoc  (A : CoefficientField d)
    (U : HypoellipticAleksandrov.Parabolic.Region d) (p : ℝ≥0∞) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) : Prop :=
  ∀ V : HypoellipticAleksandrov.Parabolic.Region d, IsOpen V → IsCompact (closure V) → closure V ⊆ U →
    ∃ w : ParabolicW12Function d V p,
      w.toFun =ᵐ[timeVelocityVolumeOn V] u ∧ IsWeakParabolicEquationOn A w

/-- A.e.-equal value representatives have a.e.-equal selected-jet operators.
No symmetry of the selected velocity Hessians is assumed. -/
theorem weakParabolicOperator_congr_ae_of_value_ae
     {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} (A : CoefficientField d)
    (hU : IsOpen U) (hp : 1 ≤ p) (w w' : ParabolicW12Function d U p)
    (hvalue : w.toFun =ᵐ[timeVelocityVolumeOn U] w'.toFun) :
    weakParabolicOperator A w =ᵐ[timeVelocityVolumeOn U] weakParabolicOperator A w' := by
  rcases w.ae_eq_jet_of_value_ae hU hp w' hvalue with ⟨htime, _hgrad, hhess⟩

  filter_upwards [htime, (ae_all_iff.mpr fun i => ae_all_iff.mpr (hhess i))] with z htimez hhessz
  unfold weakParabolicOperator
  rw [htimez]
  congr 1
  unfold matrixContraction
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hhessz i j]

namespace IsWeakParabolicEquationOn

/-- The homogeneous selected-jet equation is invariant under a.e.-equal values. -/
theorem congr_value_ae_iff {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞}
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

/-- A local homogeneous equation supplies the underlying local weak Sobolev data. -/
theorem parabolicW12Loc {d : ℕ} {A : CoefficientField d}
    {U : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (h : IsWeakParabolicEquationLoc A U p u) : ParabolicW12Loc U p u := by
  intro V hVOpen hVCompact hVU
  rcases h V hVOpen hVCompact hVU with ⟨w, hwu, _hweq⟩
  exact ⟨w, hwu⟩

/-- Every compatible selected jet on a compactly-contained open subdomain obeys
the local homogeneous equation. -/
theorem equationOn {d : ℕ} {A : CoefficientField d}
    {U V : HypoellipticAleksandrov.Parabolic.Region d} {p : ℝ≥0∞} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
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
