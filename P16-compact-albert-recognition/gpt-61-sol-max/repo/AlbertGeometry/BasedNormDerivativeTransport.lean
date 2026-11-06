/-
Actual derivative and log-metric naturality of a based
whole-cubic norm equivalence. No trace, adjoint, product, Jordan or curvature
preservation is an input. Existence of a recognition map remains a separate
full endpoint obligation. The actual homogeneous-carrier representation
producer supplies these forms; they do not restrict the final theorem.
-/
module

public import AlbertGeometry.CubicHessian
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section
namespace AlbertGeometry.BasedNormDerivativeTransport
noncomputable section
open AlbertGeometry.Cubic
open Filter

variable {E G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- ONLY whole norm and distinguished unit preservation are stored. The
continuous equivalence comes from any real linear equivalence in finite dimension. -/
structure BasedNormIso (P : SymmetricTrilinearForm E) (e : E)
    (Q : SymmetricTrilinearForm G) (f : G) where
  equiv : E ≃L[ℝ] G
  map_unit : equiv e = f
  map_norm : ∀ x : E, diagonalCubic Q.form (equiv x) = diagonalCubic P.form x

namespace BasedNormIso

variable {P : SymmetricTrilinearForm E} {e : E}
  {Q : SymmetricTrilinearForm G} {f : G}
  {S : SymmetricTrilinearForm H} {h : H}

variable (I : BasedNormIso P e Q f)

theorem norm_fun_eq  :
    (fun x : E => diagonalCubic Q.form (I.equiv x)) = diagonalCubic P.form :=
  funext I.map_norm

/-- Genuine chain rule for the literal WHOLE function, followed by equality of
functions. No use of total fderiv without a derivative certificate. -/
theorem hasFDerivAt_norm_pull  (x : E) :
    HasFDerivAt (diagonalCubic P.form)
      ((fderiv ℝ (diagonalCubic Q.form) (I.equiv x)).comp I.equiv.toContinuousLinearMap) x := by
  have hd := ((differentiable_diagonalCubic Q.form (I.equiv x)).hasFDerivAt).comp x
    I.equiv.toContinuousLinearMap.hasFDerivAt
  -- hd's function is a Function.comp (from HasFDerivAt.comp), which simp does not
  -- match against the lambda-stated norm_fun_eq; rewrite the goal instead.
  rw [← I.norm_fun_eq]
  exact hd

theorem fderiv_norm_pull  (x : E) :
    fderiv ℝ (diagonalCubic P.form) x =
      (fderiv ℝ (diagonalCubic Q.form) (I.equiv x)).comp I.equiv.toContinuousLinearMap :=
  (I.hasFDerivAt_norm_pull x).fderiv

theorem fderiv_norm_pull_apply  (x u : E) :
    fderiv ℝ (diagonalCubic P.form) x u =
      fderiv ℝ (diagonalCubic Q.form) (I.equiv x) (I.equiv u) := by
  rw [I.fderiv_norm_pull]
  rfl

/-- Actual continuous linear precomposition of covectors. -/
def pullCovector (L : E →L[ℝ] G) : (G →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E G ℝ).flip L

/-- Equality of the COMPLETE actual derivative-map functions before their
next differentiation. This is not a single-point derivative equality. -/
theorem derivative_fun_eq  :
    (fun x : E => fderiv ℝ (diagonalCubic P.form) x) =
      (fun x : E => pullCovector I.equiv.toContinuousLinearMap
        (fderiv ℝ (diagonalCubic Q.form) (I.equiv x))) := by
  funext x
  exact I.fderiv_norm_pull x

theorem hasFDerivAt_derivative_pull  (x : E) :
    HasFDerivAt (fun y : E => fderiv ℝ (diagonalCubic P.form) y)
      ((pullCovector I.equiv.toContinuousLinearMap).comp
        ((cubicHessian Q (I.equiv x)).comp I.equiv.toContinuousLinearMap)) x := by
  have hinner := (hasFDerivAt_fderiv_diagonalCubic_actual Q (I.equiv x)).comp x
    I.equiv.toContinuousLinearMap.hasFDerivAt
  have houter := (pullCovector I.equiv.toContinuousLinearMap).hasFDerivAt.comp x hinner
  exact houter.congr_of_eventuallyEq
    (Eventually.of_forall (fun y : E => congrFun I.derivative_fun_eq y))

theorem cubicHessian_pull  (x : E) :
    cubicHessian P x = (pullCovector I.equiv.toContinuousLinearMap).comp
      ((cubicHessian Q (I.equiv x)).comp I.equiv.toContinuousLinearMap) :=
  (I.hasFDerivAt_derivative_pull x).fderiv

theorem cubicHessian_pull_apply  (x u v : E) :
    cubicHessian P x u v = cubicHessian Q (I.equiv x) (I.equiv u) (I.equiv v) := by
  rw [I.cubicHessian_pull]
  rfl

/-- Actual trace is DN at the distinguished unit, never a stored trace field. -/
def normTrace (P : SymmetricTrilinearForm E) (e : E) : E →L[ℝ] ℝ :=
  fderiv ℝ (diagonalCubic P.form) e

/-- Actual raw bilinear form obtained from DN and D2N, not the prescribed
metric at all points. It equals three times the log-Hessian metric at N(e)=1. -/
def rawTraceForm (P : SymmetricTrilinearForm E) (e : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (normTrace P e).smulRight (normTrace P e) - cubicHessian P e

@[simp] theorem rawTraceForm_apply (P : SymmetricTrilinearForm E) (e u v : E) :
    rawTraceForm P e u v = normTrace P e u * normTrace P e v - cubicHessian P e u v := by
  simp [rawTraceForm, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem normTrace_pull  (u : E) :
    normTrace P e u = normTrace Q f (I.equiv u) := by
  unfold normTrace
  simpa only [I.map_unit] using I.fderiv_norm_pull_apply e u

theorem rawTraceForm_pull  (u v : E) :
    rawTraceForm P e u v = rawTraceForm Q f (I.equiv u) (I.equiv v) := by
  rw [rawTraceForm_apply, rawTraceForm_apply, I.normTrace_pull u, I.normTrace_pull v]
  rw [I.cubicHessian_pull_apply, I.map_unit]

/-- The mandatory raw/geometric scale derives from the actual twice-log
calculus theorem and actual normalization, not from a metric convention. -/
theorem rawTraceForm_eq_three_logMetric (P : SymmetricTrilinearForm E)
    (e : E) (he : diagonalCubic P.form e = 1) (u v : E) :
    rawTraceForm P e u v = 3 * logHessianForm P e u v := by
  have hpos : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  rw [rawTraceForm_apply, logHessianForm_apply P hpos, he]
  simp only [normTrace]
  ring


end BasedNormIso
end
end AlbertGeometry.BasedNormDerivativeTransport
