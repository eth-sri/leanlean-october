module

public import HypoellipticAleksandrov.Parabolic.Operator

/-!
# Local classical parabolic predicates

This module gives the transparent local classical surfaces used by the
parabolic Harnack development.  The predicates below contain only pointwise
regularity, ellipticity, sign, and equation data; they contain no comparison
or estimate.  The `ContDiffOn ℝ 2` surface is the deliberately stronger
smooth, isotropic local `C²` classical leaf relative to the source's
`C^{1,2}` class.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped MatrixOrder

variable {d : ℕ}

/-- A coefficient field is continuous at every point of a prescribed set. -/
def IsContinuousCoefficientOn  (A : CoefficientField d)
    (U : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ContinuousOn (coefficientAt A) U

/-- A coefficient field obeys a lower Loewner ellipticity bound on a set. -/
def HasLowerEllipticityOn  (lam : ℝ) (A : CoefficientField d)
    (U : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt A z

/-- A coefficient field obeys an upper Loewner ellipticity bound on a set. -/
def HasUpperEllipticityOn  (Lam : ℝ) (A : CoefficientField d)
    (U : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ∀ z ∈ U, coefficientAt A z ≤ Lam • (1 : PDE.Mat d)

/-- A scalar function is nonnegative at every point of a set. -/
def IsNonnegativeOn  (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (U : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ∀ z ∈ U, 0 ≤ q z

variable (A : CoefficientField d)

/-- A scalar function is a pointwise supersolution of the forward equation on a set. -/
def IsParabolicSupersolutionOn
    (f u : HypoellipticAleksandrov.Parabolic.ScalarField d) (U : HypoellipticAleksandrov.Parabolic.Region d) : Prop :=
  ∀ z ∈ U, f z ≤ parabolicOperator A u z



namespace IsContinuousCoefficientOn



variable {d : ℕ} {A : CoefficientField d}

/-- Coefficient continuity restricts to a smaller set. -/
theorem mono  {U V : HypoellipticAleksandrov.Parabolic.Region d}
    (h : IsContinuousCoefficientOn A U) (hVU : V ⊆ U) :
    IsContinuousCoefficientOn A V :=
  ContinuousOn.mono h hVU

/-- Global coefficient continuity gives local coefficient continuity on every set. -/
theorem of_global
    (h : IsContinuousCoefficient A) (U : HypoellipticAleksandrov.Parabolic.Region d) :
    IsContinuousCoefficientOn A U :=
  h.continuousOn

end IsContinuousCoefficientOn

namespace HasLowerEllipticityOn

/-- A local lower ellipticity bound can be evaluated at each point of its set. -/
theorem le {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U : HypoellipticAleksandrov.Parabolic.Region d} (h : HasLowerEllipticityOn lam A U)
    {z : TimeVelocity d} (hz : z ∈ U) : type_of% (h z hz) :=
  h z hz

variable {d : ℕ} {lam : ℝ} {A : CoefficientField d}

/-- A lower ellipticity bound restricts to a smaller set. -/
theorem mono
    {U V : HypoellipticAleksandrov.Parabolic.Region d} (h : HasLowerEllipticityOn lam A U)
    (hVU : V ⊆ U) : HasLowerEllipticityOn lam A V :=
  fun z hz => h z (hVU hz)

/-- A global lower ellipticity bound gives the corresponding local bound. -/
theorem of_global
    (h : HasLowerEllipticity lam A) (U : HypoellipticAleksandrov.Parabolic.Region d) :
    HasLowerEllipticityOn lam A U :=
  fun z _ => h z.1 z.2

end HasLowerEllipticityOn

namespace HasUpperEllipticityOn

/-- An upper ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    {U V : HypoellipticAleksandrov.Parabolic.Region d} (h : HasUpperEllipticityOn Lam A U)
    (hVU : V ⊆ U) : HasUpperEllipticityOn Lam A V :=
  fun z hz => h z (hVU hz)

/-- A global upper ellipticity bound gives the corresponding local bound. -/
theorem of_global {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    (h : HasUpperEllipticity Lam A) (U : HypoellipticAleksandrov.Parabolic.Region d) :
    HasUpperEllipticityOn Lam A U :=
  fun z _ => h z.1 z.2

end HasUpperEllipticityOn

namespace IsNonnegativeOn

/-- Nonnegativity restricts to a smaller set. -/
theorem mono {d : ℕ} {q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {U V : HypoellipticAleksandrov.Parabolic.Region d} (h : IsNonnegativeOn q U)
    (hVU : V ⊆ U) : IsNonnegativeOn q V :=
  fun z hz => h z (hVU hz)

end IsNonnegativeOn

namespace IsParabolicSupersolutionOn

/-- A supersolution inequality restricts to a smaller set. -/
theorem mono {d : ℕ} {A : CoefficientField d} {f u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {U V : HypoellipticAleksandrov.Parabolic.Region d} (h : IsParabolicSupersolutionOn A f u U)
    (hVU : V ⊆ U) : IsParabolicSupersolutionOn A f u V :=
  fun z hz => h z (hVU hz)

end IsParabolicSupersolutionOn



/-- A globally `C²` scalar function is `C²` on every prescribed set. -/
theorem contDiffOn_of_global {d : ℕ} {q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (h : ContDiff ℝ 2 q) (U : HypoellipticAleksandrov.Parabolic.Region d) : ContDiffOn ℝ 2 q U :=
  h.contDiffOn

variable {d : ℕ}

/-- On an open set, local `C²` regularity gives pointwise `C²` regularity. -/
theorem contDiffAt_of_contDiffOn_of_isOpen  {q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    {z : TimeVelocity d} (hz : z ∈ U) : ContDiffAt ℝ 2 q z :=
  (hq z hz).contDiffAt (hU.mem_nhds hz)

variable (A : CoefficientField d) (u : HypoellipticAleksandrov.Parabolic.ScalarField d)

/-- Negation reverses the forward parabolic operator. -/
theorem parabolicOperator_neg   (z : TimeVelocity d) :
    parabolicOperator A (fun y => -u y) z = -parabolicOperator A u z := by
  have hfirst : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y := by
    funext y
    exact fderiv_fun_neg
  have htime : timeDerivative (fun y => -u y) z = -timeDerivative u z := by
    unfold timeDerivative
    simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  have hhessian :
      velocityHessian (fun y => -u y) z = -velocityHessian u z := by
    ext i j
    unfold velocityHessian
    rw [hfirst, fderiv_fun_neg]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian,
    HypoellipticAleksandrov.matrixContraction_neg_right]
  ring

/-- Adding a constant preserves the forward parabolic operator. -/
theorem parabolicOperator_add_const   (c : ℝ) (z : TimeVelocity d) :
    parabolicOperator A (fun y => u y + c) z = parabolicOperator A u z := by
  let sharedTerm_b6f4cd8639 := ((fun y => u y + c))
  have hfirst : fderiv ℝ sharedTerm_b6f4cd8639 = fderiv ℝ u := by
    funext y
    exact fderiv_add_const c
  have htime : timeDerivative sharedTerm_b6f4cd8639 z = timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_add_const]
  have hhessian :
      velocityHessian sharedTerm_b6f4cd8639 z = velocityHessian u z := by
    unfold velocityHessian
    rw [hfirst]
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian]







end HypoellipticAleksandrov.Parabolic
