/-
Genuine second Frechet derivatives and log-Hessian forms.
The arbitrary homogeneous-cubic/polarization correspondence remains a separate
full-scope obligation. No geometric metric positivity or curvature is assumed.
-/
module
public import AlbertGeometry.LinearSimp

public import AlbertGeometry.CubicDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

open scoped BigOperators ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine fully curried continuous trilinear form. -/
def fullyCurried (P : TrilinearForm E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
    (P.curryRight.curryLeft)

@[simp] theorem fullyCurried_apply (P : TrilinearForm E) (x u v : E) :
    fullyCurried P x u v = P ![x, u, v] := by
  simp [fullyCurried, ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.curryRight_apply, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty]

variable (P : SymmetricTrilinearForm E)

theorem hasFDerivAt_fderiv_diagonalCubic (x : E) :
    HasFDerivAt (fun z : E => fderiv ℝ (diagonalCubic P.form) z)
      ((6 : ℝ) • fullyCurried P.form x) x := by
  have hC := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (fullyCurried P.form) (x := x)
  have h : (fun z : E => fderiv ℝ (diagonalCubic P.form) z) =
      (fun z => (3 : ℝ) • fullyCurried P.form z z) := by
    ext z y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply,
      fderiv_diagonalCubic_apply_symmetric]
  rw [h]
  convert (hC.clm_apply (hasFDerivAt_id x)).const_smul (3 : ℝ) using 1
  · rfl
  · ext u v
    simp only [clm_eval, fullyCurried_apply, id_eq, P.swap12 u x v]
    ring

/-- Actual second Frechet derivative, obtained by differentiating actual fderiv.
It is not defined as six times a form or as a desired log-Hessian identity. -/
def cubicHessian  (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (diagonalCubic P.form) z) x

theorem cubicHessian_eq_fullyCurried (x : E) :
    cubicHessian P x = (6 : ℝ) • fullyCurried P.form x :=
  (hasFDerivAt_fderiv_diagonalCubic P x).fderiv

theorem hasFDerivAt_fderiv_diagonalCubic_actual
    (x : E) :
    HasFDerivAt (fun z : E => fderiv ℝ (diagonalCubic P.form) z)
      (cubicHessian P x) x :=
  (hasFDerivAt_fderiv_diagonalCubic P x).differentiableAt.hasFDerivAt

theorem cubicHessian_apply  (x u v : E) :
    cubicHessian P x u v = 6 * P.form ![x, u, v] := by
  simp [cubicHessian_eq_fullyCurried]

/-- Actual derivative of the actual Hessian, proved via its global linear form. -/
theorem hasFDerivAt_cubicHessian  (x : E) :
    HasFDerivAt (cubicHessian P) ((6 : ℝ) • fullyCurried P.form) x := by
  convert ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) ((6 : ℝ) • fullyCurried P.form) (x := x) using 1
  funext z
  exact cubicHessian_eq_fullyCurried P z







theorem cubicHessian_symm  (x u v : E) :
    cubicHessian P x u v = cubicHessian P x v u := by
  rw [cubicHessian_apply, cubicHessian_apply]
  exact congrArg (fun t : ℝ => 6 * t) (P.swap23 x u v)

/-- Second Euler identity for the actual Hessian and actual first derivative. -/
theorem cubicHessian_radial  (x u : E) :
    cubicHessian P x x u = 2 * fderiv ℝ (diagonalCubic P.form) x u := by
  rw [cubicHessian_apply, fderiv_diagonalCubic_apply_symmetric]
  ring

/-- The positive locus is selected from the actual cubic, never assumed globally. -/
def positiveLocus  : Set E :=
  {x | 0 < diagonalCubic P.form x}

theorem isOpen_positiveLocus  :
    IsOpen (positiveLocus P) :=
  isOpen_lt continuous_const (differentiable_diagonalCubic P.form).continuous

variable  {x : E}
    (hx : 0 < diagonalCubic P.form x)

include P x hx in
theorem eventually_positive  :
    ∀ᶠ z in 𝓝 x, 0 < diagonalCubic P.form z :=
  (isOpen_positiveLocus P).mem_nhds hx

/-- Literal log composed with the actual cubic. Identities require positivity. -/
def logCubic  (x : E) : ℝ :=
  Real.log (diagonalCubic P.form x)

include P x hx in
theorem hasFDerivAt_logCubic  :
    HasFDerivAt (logCubic P)
      ((diagonalCubic P.form x)⁻¹ • fderiv ℝ (diagonalCubic P.form) x) x :=
  (differentiable_diagonalCubic P.form x).hasFDerivAt.log (ne_of_gt hx)

include P x hx in
theorem fderiv_logCubic  :
    fderiv ℝ (logCubic P) x =
      (diagonalCubic P.form x)⁻¹ • fderiv ℝ (diagonalCubic P.form) x :=
  (hasFDerivAt_logCubic P hx).fderiv

/-- Explicit inverse-cubic derivative candidate certified by the true chain rule. -/
def inverseCubicDerivative  (x : E) : E →L[ℝ] ℝ :=
  (-(diagonalCubic P.form x ^ 2)⁻¹) • fderiv ℝ (diagonalCubic P.form) x

include P x hx in
theorem hasFDerivAt_inverseCubic  :
    HasFDerivAt (fun z : E => (diagonalCubic P.form z)⁻¹)
      (inverseCubicDerivative P x) x :=
  (hasDerivAt_inv (ne_of_gt hx)).comp_hasFDerivAt x
    (differentiable_diagonalCubic P.form x).hasFDerivAt

/-- Explicit candidate from differentiating inverse N times actual DN. -/
def logHessianFormula  (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (diagonalCubic P.form x)⁻¹ • cubicHessian P x +
    (inverseCubicDerivative P x).smulRight (fderiv ℝ (diagonalCubic P.form) x)

include P x hx in
/-- The first-derivative identity is used on a proved positive neighborhood,
not merely at x, before differentiating it to obtain the actual log Hessian. -/
theorem hasFDerivAt_fderiv_logCubic  :
    HasFDerivAt (fun z : E => fderiv ℝ (logCubic P) z)
      (logHessianFormula P x) x :=
  ((hasFDerivAt_inverseCubic P hx).smul
    (hasFDerivAt_fderiv_diagonalCubic_actual P x)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun z hz => fderiv_logCubic P hz))

/-- Actual second derivative of literal log N, with positivity-gated theorems. -/
def logHessian  (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (logCubic P) z) x

include P x hx in
theorem logHessian_eq_formula  :
    logHessian P x = logHessianFormula P x :=
  (hasFDerivAt_fderiv_logCubic P hx).fderiv

include P x hx in
theorem logHessian_apply  (u v : E) :
    logHessian P x u v = cubicHessian P x u v / diagonalCubic P.form x -
      fderiv ℝ (diagonalCubic P.form) x u * fderiv ℝ (diagonalCubic P.form) x v /
        diagonalCubic P.form x ^ 2 := by
  rw [logHessian_eq_formula P hx]
  simp only [clm_eval, logHessianFormula, inverseCubicDerivative, div_eq_mul_inv]
  ring

/-- The actual normalized log-Hessian bilinear form. Positive definiteness is
not asserted here; the recognition input must establish it at the base point. -/
def logHessianForm  (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • logHessian P x

include P x hx in
theorem logHessianForm_apply  (u v : E) :
    logHessianForm P x u v = -cubicHessian P x u v / (3 * diagonalCubic P.form x) +
      fderiv ℝ (diagonalCubic P.form) x u * fderiv ℝ (diagonalCubic P.form) x v /
        (3 * diagonalCubic P.form x ^ 2) := by
  simp only [logHessianForm, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [logHessian_apply P hx]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

include P x hx in
theorem logHessianForm_symm  (u v : E) :
    logHessianForm P x u v = logHessianForm P x v u := by
  rw [logHessianForm_apply P hx, logHessianForm_apply P hx, cubicHessian_symm P x u v]
  ring

/-- Euler identities derive the radial/tangent metric relation at normalized e. -/
theorem logHessianForm_radial_at_one  (e u : E)
    (he : diagonalCubic P.form e = 1) :
    logHessianForm P e e u = fderiv ℝ (diagonalCubic P.form) e u / 3 := by
  have hpos : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  rw [logHessianForm_apply P hpos, he, cubicHessian_radial,
    fderiv_diagonalCubic_at_one P.form e he]
  ring

end
end AlbertGeometry.Cubic
