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

/- A coefficient field is continuous at every point of a prescribed set. -/
def IsContinuousCoefficientOn {d : ℕ} (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ContinuousOn (coefficientAt A) U

/- A coefficient field obeys a lower Loewner ellipticity bound on a set. -/
def HasLowerEllipticityOn {d : ℕ} (lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt A z

/- A coefficient field obeys an upper Loewner ellipticity bound on a set. -/
def HasUpperEllipticityOn {d : ℕ} (Lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, coefficientAt A z ≤ Lam • (1 : PDE.Mat d)

/- A scalar function is nonnegative at every point of a set. -/
def IsNonnegativeOn {d : ℕ} (q : TimeVelocity d → ℝ)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, 0 ≤ q z

/- A scalar function is a pointwise supersolution of the forward equation on a set. -/
def IsParabolicSupersolutionOn {d : ℕ} (A : CoefficientField d)
    (f u : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, f z ≤ parabolicOperator A u z

/- A scalar function satisfies the homogeneous forward parabolic equation on a set. -/
def IsParabolicSolutionOn {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, parabolicOperator A u z = 0

namespace IsContinuousCoefficientOn

/- A local coefficient-continuity predicate gives continuity at each of its points. -/
theorem mono {d : ℕ} {A : CoefficientField d} {U V : Set (TimeVelocity d)}
    (h : IsContinuousCoefficientOn A U) (hVU : V ⊆ U) :
    IsContinuousCoefficientOn A V :=
  ContinuousOn.mono h hVU

/- Global coefficient continuity gives local coefficient continuity on every set. -/
theorem of_global {d : ℕ} {A : CoefficientField d}
    (h : IsContinuousCoefficient A) (U : Set (TimeVelocity d)) :
    IsContinuousCoefficientOn A U :=
  h.continuousOn

end IsContinuousCoefficientOn

namespace HasLowerEllipticityOn

/- A local lower ellipticity bound can be evaluated at each point of its set. -/
theorem le {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U : Set (TimeVelocity d)} (h : HasLowerEllipticityOn lam A U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    lam • (1 : PDE.Mat d) ≤ coefficientAt A z :=
  h z hz

/- A lower ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U V : Set (TimeVelocity d)} (h : HasLowerEllipticityOn lam A U)
    (hVU : V ⊆ U) : HasLowerEllipticityOn lam A V :=
  fun z hz => h z (hVU hz)

/- A global lower ellipticity bound gives the corresponding local bound. -/
theorem of_global {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    (h : HasLowerEllipticity lam A) (U : Set (TimeVelocity d)) :
    HasLowerEllipticityOn lam A U :=
  fun z _ => h z.1 z.2

end HasLowerEllipticityOn

namespace HasUpperEllipticityOn

/- An upper ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    {U V : Set (TimeVelocity d)} (h : HasUpperEllipticityOn Lam A U)
    (hVU : V ⊆ U) : HasUpperEllipticityOn Lam A V :=
  fun z hz => h z (hVU hz)

/- A global upper ellipticity bound gives the corresponding local bound. -/
theorem of_global {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    (h : HasUpperEllipticity Lam A) (U : Set (TimeVelocity d)) :
    HasUpperEllipticityOn Lam A U :=
  fun z _ => h z.1 z.2

end HasUpperEllipticityOn

namespace IsNonnegativeOn

/- Nonnegativity restricts to a smaller set. -/
theorem mono {d : ℕ} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsNonnegativeOn q U)
    (hVU : V ⊆ U) : IsNonnegativeOn q V :=
  fun z hz => h z (hVU hz)

end IsNonnegativeOn

namespace IsParabolicSupersolutionOn

/- A supersolution inequality restricts to a smaller set. -/
theorem mono {d : ℕ} {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsParabolicSupersolutionOn A f u U)
    (hVU : V ⊆ U) : IsParabolicSupersolutionOn A f u V :=
  fun z hz => h z (hVU hz)

end IsParabolicSupersolutionOn

namespace IsParabolicSolutionOn

end IsParabolicSolutionOn

/- A globally `C²` scalar function is `C²` on every prescribed set. -/
theorem contDiffOn_of_global {d : ℕ} {q : TimeVelocity d → ℝ}
    (h : ContDiff ℝ 2 q) (U : Set (TimeVelocity d)) : ContDiffOn ℝ 2 q U :=
  h.contDiffOn

/- On an open set, local `C²` regularity gives pointwise `C²` regularity. -/
theorem contDiffAt_of_contDiffOn_of_isOpen {d : ℕ} {q : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    {z : TimeVelocity d} (hz : z ∈ U) : ContDiffAt ℝ 2 q z :=
  (hq z hz).contDiffAt (hU.mem_nhds hz)

/- Negation reverses the forward parabolic operator. -/
theorem parabolicOperator_neg {d } (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
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

/- Adding a constant preserves the forward parabolic operator. -/
theorem parabolicOperator_add_const {d } (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (c : ℝ) (z : TimeVelocity d) :
    parabolicOperator A (fun y => u y + c) z = parabolicOperator A u z := by
  have hfirst : fderiv ℝ (fun y => u y + c) = fderiv ℝ u := by
    funext y
    exact fderiv_add_const c
  have htime : timeDerivative (fun y => u y + c) z = timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_add_const]
  have hhessian :
      velocityHessian (fun y => u y + c) z = velocityHessian u z := by
    unfold velocityHessian
    rw [hfirst]
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian]

namespace IsParabolicSolutionOn

/- Negating a homogeneous local solution preserves its homogeneous equation. -/
end IsParabolicSolutionOn

/- The transparent local nonnegative classical solution surface for the
Harnack leaf.  Its `ContDiffOn ℝ 2` assumption deliberately selects the
stronger smooth, isotropic local `C²` leaf relative to the source's
`C^{1,2}` class. -/
def IsLocalClassicalSolutionOn (d ) (B : CoefficientField d)
    (q : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) (lam Lam : ℝ) : Prop :=
  IsContinuousCoefficientOn B U ∧
    ContDiffOn ℝ 2 q U ∧
    IsNonnegativeOn q U ∧
    HasLowerEllipticityOn lam B U ∧
    HasUpperEllipticityOn Lam B U ∧
    IsParabolicSolutionOn B q U

namespace IsLocalClassicalSolutionOn

/- A local classical solution is `C²` on its domain. -/
theorem contDiffOn {d B q U lam Lam}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : ContDiffOn ℝ 2 q U :=
  h.2.1

end IsLocalClassicalSolutionOn

end HypoellipticAleksandrov.Parabolic
