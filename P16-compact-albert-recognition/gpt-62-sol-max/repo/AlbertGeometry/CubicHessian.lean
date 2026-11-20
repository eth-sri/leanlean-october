module
public import Glennie.Compact.ObservationData
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
@[expose] public section
namespace AlbertGeometry.Cubic
noncomputable section
open Glennie.SubmissionR04Intrinsic
open ContinuousLinearMap Filter
open scoped ContDiff Topology

/-- An actual continuous trilinear form, not a collection of desired jets. -/
abbrev TrilinearForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness of the diagonal through the multilinear form. -/
theorem contDiff_diagonalCubic (P : BasedCubic E) (n : ℕ∞ω) :
    ContDiff ℝ n (cubic P) :=
  P.form.contDiff.comp (ContinuousLinearMap.pi (fun _ : Fin 3 => ContinuousLinearMap.id ℝ E)).contDiff

theorem hasFDerivAt_diagonalCubic (P : BasedCubic E) (x : E) :
    HasFDerivAt (cubic P) (fderiv ℝ (cubic P) x) x :=
  ((contDiff_diagonalCubic P ⊤).differentiable (by simp) x).hasFDerivAt

theorem diagonalCubic_eq (P : BasedCubic E) (x : E) : cubic P x = P.form ![x,x,x] := by
  unfold cubic
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The ordinary currying equivalence, twice, keeps the operator-norm topology. -/
def fullyCurried (P : TrilinearForm E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    P.curryRight.curryLeft

@[simp] theorem fullyCurried_apply (P : TrilinearForm E) (x y z : E) :
    fullyCurried P x y z = P ![x,y,z] := by
  change P (Fin.snoc (Fin.cons x (Fin.snoc (0 : Fin 0 → E) y)) z) = _
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Diagonal differentiation of a symmetric bilinear map, also with operator-valued output. -/
private theorem quadratic_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E →L[ℝ] F) (hs : ∀ x y, L x y = L y x) (x : E) :
    HasFDerivAt (fun w => L w w) ((2 : ℝ) • L x) x := by
  refine (L.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) x)).congr_fderiv ?_
  ext u : 1
  simp only [add_apply, comp_apply, id_apply, flip_apply, id_eq, smul_apply, hs u x, ← two_smul ℝ]

private theorem fullyCurried_comm (P : BasedCubic E) (x y : E) :
    fullyCurried P.form x y = fullyCurried P.form y x := by
  ext z
  simpa only [fullyCurried_apply] using P.swap12 x y z

private theorem fderiv_diagonalCubic_eq_curried (P : BasedCubic E) (x : E) :
    fderiv ℝ (cubic P) x = (3 : ℝ) • fullyCurried P.form x x := by
  have h := (quadratic_deriv (fullyCurried P.form) (fullyCurried_comm P) x).clm_apply
    (hasFDerivAt_id (𝕜 := ℝ) x)
  have h' := h.congr_of_eventuallyEq (f₁ := cubic P)
    (Eventually.of_forall (fun w => by simp only [diagonalCubic_eq, fullyCurried_apply, id_eq]))
  rw [h'.fderiv]
  ext u : 1
  simp only [add_apply, comp_apply, flip_apply, id_apply, id_eq, smul_apply,
    fullyCurried_apply, P.swap23 x u x, smul_eq_mul]
  ring

theorem fderiv_diagonalCubic_apply_symmetric (P : BasedCubic E) (x y : E) :
    fderiv ℝ (cubic P) x y = 3 * P.form ![x,x,y] := by
  simp [fderiv_diagonalCubic_eq_curried, smul_eq_mul]

theorem fderiv_diagonalCubic_at_one (P : BasedCubic E) (e : E)
    (he : cubic P e = 1) : fderiv ℝ (cubic P) e e = 3 := by
  rw [fderiv_diagonalCubic_apply_symmetric, ← diagonalCubic_eq, he, mul_one]

private theorem hasFDerivAt_cubicGradient (P : BasedCubic E) (x : E) :
    HasFDerivAt (fderiv ℝ (cubic P)) ((6 : ℝ) • fullyCurried P.form x) x := by
  change HasFDerivAt (fun y => fderiv ℝ (cubic P) y) _ x
  simp only [fderiv_diagonalCubic_eq_curried]
  convert (quadratic_deriv (fullyCurried P.form) (fullyCurried_comm P) x).const_smul (3 : ℝ) using 1
  rw [smul_smul]
  norm_num

/-- The actual second Fréchet derivative. -/
def cubicHessian (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z => fderiv ℝ (cubic P) z) x

theorem hasFDerivAt_fderiv_diagonalCubic_actual (P : BasedCubic E) (x : E) :
    HasFDerivAt (fderiv ℝ (cubic P)) (cubicHessian P x) x :=
  (hasFDerivAt_cubicGradient P x).differentiableAt.hasFDerivAt

theorem cubicHessian_apply (P : BasedCubic E) (x u v : E) :
    cubicHessian P x u v = 6 * P.form ![x,u,v] := by
  simp [cubicHessian, (hasFDerivAt_cubicGradient P x).fderiv, smul_eq_mul]

theorem hasFDerivAt_cubicHessian (P : BasedCubic E) (x : E) :
    HasFDerivAt (cubicHessian P) ((6 : ℝ) • fullyCurried P.form) x := by
  let L : E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := (6 : ℝ) • fullyCurried P.form
  have h := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) L (x := x)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun z => (hasFDerivAt_cubicGradient P z).fderiv)

theorem eventually_positive (P : BasedCubic E) {x : E} (hx : 0 < cubic P x) :
    ∀ᶠ z in 𝓝 x, 0 < cubic P z :=
  (isOpen_lt continuous_const (contDiff_diagonalCubic P 0).continuous).mem_nhds hx

/-- Literal log composed with the actual cubic. Identities require positivity. -/
def logCubic (P : BasedCubic E) (x : E) : ℝ :=
  Real.log (cubic P x)

abbrev logHessian (P : BasedCubic E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z => fderiv ℝ (logCubic P) z) x

theorem logHessianForm_apply (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) (u v : E) :
    metric P x u v = -cubicHessian P x u v / (3 * cubic P x) +
      fderiv ℝ (cubic P) x u * fderiv ℝ (cubic P) x v /
        (3 * cubic P x ^ 2) := by
  have h := ((hasDerivAt_inv hx.ne').comp_hasFDerivAt x
      (hasFDerivAt_diagonalCubic P x)).smul
    (hasFDerivAt_fderiv_diagonalCubic_actual P x)
  change (-1 / 3 : ℝ) • fderiv ℝ (fun z => fderiv ℝ (logCubic P) z) x u v = _
  unfold logCubic
  rw [(h.congr_of_eventuallyEq ((eventually_positive P hx).mono (fun y hy => ((hasFDerivAt_diagonalCubic P y).log hy.ne').fderiv))).fderiv]
  simp only [Function.comp_apply, add_apply, smul_apply, smulRight_apply,
    smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem logHessianForm_symm (P : BasedCubic E) {x : E}
    (hx : 0 < cubic P x) (u v : E) :
    metric P x u v = metric P x v u := by
  simp only [logHessianForm_apply P hx, cubicHessian_apply, P.swap23 x u v]
  ring

end
end AlbertGeometry.Cubic
