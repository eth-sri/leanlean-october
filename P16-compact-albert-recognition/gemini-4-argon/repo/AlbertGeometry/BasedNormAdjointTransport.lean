module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators ContDiff Topology
open Filter

namespace AlbertGeometry.Cubic

noncomputable section

/-- An actual continuous trilinear form, not a collection of desired jets. -/
abbrev TrilinearForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear diagonal embedding into the three slots. -/
def diagonalEmbedding : E →L[ℝ] (Fin 3 → E) :=
  ContinuousLinearMap.pi (fun _ : Fin 3 => ContinuousLinearMap.id ℝ E)

@[simp] theorem diagonalEmbedding_apply (x : E) (i : Fin 3) :
    diagonalEmbedding (E := E) x i = x := rfl

/-- The literal diagonal degree-three polynomial attached to the form. -/
def diagonalCubic (P : TrilinearForm E) (x : E) : ℝ :=
  P (fun _ : Fin 3 => x)

/-- The explicit slot-sum candidate, subsequently certified by HasFDerivAt.
The derivative itself is never defined by an assumed Euler/gradient identity. -/
def diagonalDerivative (P : TrilinearForm E) (x : E) : E →L[ℝ] ℝ :=
  (P.linearDeriv (fun _ : Fin 3 => x)).comp (diagonalEmbedding (E := E))

/-- The actual derivative follows by the chain rule for the diagonal embedding. -/
theorem hasFDerivAt_diagonalCubic (P : TrilinearForm E) (x : E) :
    HasFDerivAt (diagonalCubic P) (diagonalDerivative P x) x :=
  (P.hasFDerivAt (diagonalEmbedding (E := E) x)).comp x
    (diagonalEmbedding (E := E)).hasFDerivAt

/-- This uses proved differentiability, never the total fderiv fallback. -/
theorem fderiv_diagonalCubic (P : TrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P) x = diagonalDerivative P x :=
  (hasFDerivAt_diagonalCubic P x).fderiv

theorem differentiable_diagonalCubic (P : TrilinearForm E) :
    Differentiable ℝ (diagonalCubic P) :=
  fun x => (hasFDerivAt_diagonalCubic P x).differentiableAt

/-- Smoothness comes from a continuous polynomial and a continuous linear map. -/
theorem contDiff_diagonalCubic (P : TrilinearForm E) (n : ℕ∞ω) :
    ContDiff ℝ n (diagonalCubic P) :=
  P.contDiff.comp (diagonalEmbedding (E := E)).contDiff

/-- The three replacements are the differentiated slots of the true form. -/
theorem diagonalDerivative_apply (P : TrilinearForm E) (x y : E) :
    diagonalDerivative P x y =
      ∑ i : Fin 3, P (Function.update (fun _ : Fin 3 => x) i y) := by
  simp only [diagonalDerivative, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, diagonalEmbedding_apply]

/-- Euler's radial identity requires no symmetry premise. -/
theorem diagonalDerivative_radial (P : TrilinearForm E) (x : E) :
    diagonalDerivative P x x = 3 * diagonalCubic P x := by
  have hu (i : Fin 3) :
      Function.update (fun _ : Fin 3 => x) i x = (fun _ : Fin 3 => x) :=
    Function.update_eq_self i (fun _ : Fin 3 => x)
  rw [diagonalDerivative_apply]
  simp only [hu, Fin.sum_univ_three]
  change P (fun _ : Fin 3 => x) + P (fun _ : Fin 3 => x) +
    P (fun _ : Fin 3 => x) = 3 * P (fun _ : Fin 3 => x)
  ring

/-- Euler is stated for the genuine Fréchet derivative. -/
theorem fderiv_diagonalCubic_radial (P : TrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P) x x = 3 * diagonalCubic P x := by
  rw [fderiv_diagonalCubic, diagonalDerivative_radial]

/-- A normalized base point is a regular point; this is not assumed as a field. -/
theorem fderiv_diagonalCubic_at_one (P : TrilinearForm E) (e : E)
    (he : diagonalCubic P e = 1) :
    fderiv ℝ (diagonalCubic P) e e = 3 := by
  rw [fderiv_diagonalCubic_radial, he]; ring

/-- Symmetry of a trilinear representation. -/
structure SymmetricTrilinearForm (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : TrilinearForm E
  swap12 : ∀ (x y z : E), form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ (x y z : E), form ![x, y, z] = form ![x, z, y]

/-- The true slot-sum derivative simplifies to the expected threefold term. -/
theorem diagonalDerivative_apply_symmetric (P : SymmetricTrilinearForm E)
    (x y : E) :
    diagonalDerivative P.form x y = 3 * P.form ![x, x, y] := by
  have h0 : Function.update (fun _ : Fin 3 => x) 0 y = ![y, x, x] := by ext i; fin_cases i <;> simp
  have h1 : Function.update (fun _ : Fin 3 => x) 1 y = ![x, y, x] := by ext i; fin_cases i <;> simp
  have h2 : Function.update (fun _ : Fin 3 => x) 2 y = ![x, x, y] := by ext i; fin_cases i <;> simp
  rw [diagonalDerivative_apply, Fin.sum_univ_three, h0, h1, h2]
  simp only [P.swap12 y x x, P.swap23 x y x]
  ring

/-- The symmetric formula is identified with actual fderiv, not defined as it. -/
theorem fderiv_diagonalCubic_apply_symmetric (P : SymmetricTrilinearForm E)
    (x y : E) :
    fderiv ℝ (diagonalCubic P.form) x y = 3 * P.form ![x, x, y] := by
  rw [fderiv_diagonalCubic, diagonalDerivative_apply_symmetric]

/-- Genuine currying of the continuous trilinear form, with a CLM-valued result. -/
def rightCurried (P : SymmetricTrilinearForm E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) (E →L[ℝ] ℝ) :=
  P.form.curryRight

private theorem constant_two (x : E) : (fun _ : Fin 2 => x) = ![x, x] := by
  ext i; fin_cases i <;> rfl

@[simp] theorem rightCurried_apply (P : SymmetricTrilinearForm E) (x y z : E) :
    rightCurried P ![x, y] z = P.form ![x, y, z] := by
  change P.form (Fin.snoc ![x, y] z) = P.form ![x, y, z]
  congr 1; ext i; fin_cases i <;> simp

def diagonalEmbeddingTwo : E →L[ℝ] (Fin 2 → E) :=
  ContinuousLinearMap.pi (fun _ : Fin 2 => ContinuousLinearMap.id ℝ E)

/-- Equality of the already proved actual first derivative with a CLM-valued
continuous quadratic expression. This permits differentiating the derivative. -/
theorem fderiv_diagonalCubic_eq_curried (P : SymmetricTrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P.form) x =
      (3 : ℝ) • rightCurried P (fun _ : Fin 2 => x) := by
  ext y
  rw [fderiv_diagonalCubic_apply_symmetric]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hc : rightCurried P (fun _ : Fin 2 => x) y = P.form ![x, x, y] :=
    (congrArg (fun z : Fin 2 → E => rightCurried P z y) (constant_two x)).trans
      (rightCurried_apply P x x y)
  exact congrArg (fun r : ℝ => 3 * r) hc.symm

/-- An explicit continuous bilinear candidate, later identified with true fderiv. -/
def hessianFormula (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (3 : ℝ) • ((rightCurried P).linearDeriv (fun _ : Fin 2 => x)).comp
    (diagonalEmbeddingTwo (E := E))

/-- The derivative of the actual first-derivative map, by multilinear calculus. -/
theorem hasFDerivAt_fderiv_diagonalCubic (P : SymmetricTrilinearForm E) (x : E) :
    HasFDerivAt (fun z : E => fderiv ℝ (diagonalCubic P.form) z)
      (hessianFormula P x) x := by
  simp only [fderiv_diagonalCubic_eq_curried]
  exact (((rightCurried P).hasFDerivAt (diagonalEmbeddingTwo (E := E) x)).comp x
    (diagonalEmbeddingTwo (E := E)).hasFDerivAt).const_smul (3 : ℝ)

/-- Actual second Frechet derivative, obtained by differentiating actual fderiv. -/
def cubicHessian (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (diagonalCubic P.form) z) x

theorem cubicHessian_eq_formula (P : SymmetricTrilinearForm E) (x : E) :
    cubicHessian P x = hessianFormula P x :=
  (hasFDerivAt_fderiv_diagonalCubic P x).fderiv

theorem hasFDerivAt_fderiv_diagonalCubic_actual (P : SymmetricTrilinearForm E)
    (x : E) :
    HasFDerivAt (fun z : E => fderiv ℝ (diagonalCubic P.form) z)
      (cubicHessian P x) x :=
  (hasFDerivAt_fderiv_diagonalCubic P x).congr_fderiv
    (cubicHessian_eq_formula P x).symm

theorem hessianFormula_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    hessianFormula P x u v = 6 * P.form ![x, u, v] := by
  have h0 : Function.update (fun _ : Fin 2 => x) 0 u = ![u, x] := by ext i; fin_cases i <;> simp
  have h1 : Function.update (fun _ : Fin 2 => x) 1 u = ![x, u] := by ext i; fin_cases i <;> simp
  change 3 * (((rightCurried P).linearDeriv
    (fun _ : Fin 2 => x) (fun _ : Fin 2 => u)) v) = 6 * P.form ![x, u, v]
  rw [ContinuousMultilinearMap.linearDeriv_apply, Fin.sum_univ_two, h0, h1]
  simp only [ContinuousLinearMap.add_apply, rightCurried_apply, P.swap12 u x v]
  ring

theorem cubicHessian_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    cubicHessian P x u v = 6 * P.form ![x, u, v] := by
  rw [cubicHessian_eq_formula, hessianFormula_apply]

theorem cubicHessian_symm (P : SymmetricTrilinearForm E) (x u v : E) :
    cubicHessian P x u v = cubicHessian P x v u := by
  rw [cubicHessian_apply, cubicHessian_apply]
  exact congrArg (fun t : ℝ => 6 * t) (P.swap23 x u v)

/-- Second Euler identity for the actual Hessian and actual first derivative. -/
theorem cubicHessian_radial (P : SymmetricTrilinearForm E) (x u : E) :
    cubicHessian P x x u = 2 * fderiv ℝ (diagonalCubic P.form) x u := by
  rw [cubicHessian_apply, fderiv_diagonalCubic_apply_symmetric]; ring

/-- The positive locus is selected from the actual cubic, never assumed globally. -/
def positiveLocus (P : SymmetricTrilinearForm E) : Set E :=
  {x | 0 < diagonalCubic P.form x}

theorem isOpen_positiveLocus (P : SymmetricTrilinearForm E) :
    IsOpen (positiveLocus P) :=
  isOpen_lt continuous_const (differentiable_diagonalCubic P.form).continuous

theorem eventually_positive (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    ∀ᶠ z in 𝓝 x, 0 < diagonalCubic P.form z :=
  (isOpen_positiveLocus P).mem_nhds hx

/-- Literal log composed with the actual cubic. Identities require positivity. -/
def logCubic (P : SymmetricTrilinearForm E) (x : E) : ℝ :=
  Real.log (diagonalCubic P.form x)

theorem hasFDerivAt_logCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (logCubic P)
      ((diagonalCubic P.form x)⁻¹ • fderiv ℝ (diagonalCubic P.form) x) x :=
  ((hasFDerivAt_diagonalCubic P.form x).congr_fderiv
    (fderiv_diagonalCubic P.form x).symm).log (ne_of_gt hx)

theorem fderiv_logCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    fderiv ℝ (logCubic P) x =
      (diagonalCubic P.form x)⁻¹ • fderiv ℝ (diagonalCubic P.form) x :=
  (hasFDerivAt_logCubic P hx).fderiv

/-- Explicit inverse-cubic derivative candidate certified by the true chain rule. -/
def inverseCubicDerivative (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] ℝ :=
  (-(diagonalCubic P.form x ^ 2)⁻¹) • fderiv ℝ (diagonalCubic P.form) x

theorem hasFDerivAt_inverseCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (fun z : E => (diagonalCubic P.form z)⁻¹)
      (inverseCubicDerivative P x) x :=
  (hasDerivAt_inv (ne_of_gt hx)).comp_hasFDerivAt x
    ((hasFDerivAt_diagonalCubic P.form x).congr_fderiv (fderiv_diagonalCubic P.form x).symm)

/-- Explicit candidate from differentiating inverse N times actual DN. -/
def logHessianFormula (P : SymmetricTrilinearForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (diagonalCubic P.form x)⁻¹ • cubicHessian P x +
    (inverseCubicDerivative P x).smulRight (fderiv ℝ (diagonalCubic P.form) x)

/-- The first-derivative identity is used on a proved positive neighborhood,
not merely at x, before differentiating it to obtain the actual log Hessian. -/
theorem hasFDerivAt_fderiv_logCubic (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    HasFDerivAt (fun z : E => fderiv ℝ (logCubic P) z)
      (logHessianFormula P x) x :=
  ((hasFDerivAt_inverseCubic P hx).smul
    (hasFDerivAt_fderiv_diagonalCubic_actual P x)).congr_of_eventuallyEq
      ((eventually_positive P hx).mono (fun _ hz => fderiv_logCubic P hz))

/-- Actual second derivative of literal log N, with positivity-gated theorems. -/
def logHessian (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun z : E => fderiv ℝ (logCubic P) z) x

theorem logHessian_eq_formula (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) :
    logHessian P x = logHessianFormula P x :=
  (hasFDerivAt_fderiv_logCubic P hx).fderiv

theorem logHessian_apply (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v : E) :
    logHessian P x u v = cubicHessian P x u v / diagonalCubic P.form x -
      fderiv ℝ (diagonalCubic P.form) x u * fderiv ℝ (diagonalCubic P.form) x v /
        diagonalCubic P.form x ^ 2 := by
  rw [logHessian_eq_formula P hx]
  simp only [logHessianFormula, inverseCubicDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, div_eq_mul_inv]
  ring

/-- The actual normalized log-Hessian bilinear form. -/
def logHessianForm (P : SymmetricTrilinearForm E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 3 : ℝ) • logHessian P x

theorem logHessianForm_apply (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v : E) :
    logHessianForm P x u v = -cubicHessian P x u v / (3 * diagonalCubic P.form x) +
      fderiv ℝ (diagonalCubic P.form) x u * fderiv ℝ (diagonalCubic P.form) x v /
        (3 * diagonalCubic P.form x ^ 2) := by
  simp only [logHessianForm, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [logHessian_apply P hx]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem logHessianForm_symm (P : SymmetricTrilinearForm E) {x : E}
    (hx : 0 < diagonalCubic P.form x) (u v : E) :
    logHessianForm P x u v = logHessianForm P x v u := by
  rw [logHessianForm_apply P hx, logHessianForm_apply P hx, cubicHessian_symm P x u v]
  ring

/-- Euler identities derive the radial/tangent metric relation at normalized e. -/
theorem logHessianForm_radial_at_one (P : SymmetricTrilinearForm E) (e u : E)
    (he : diagonalCubic P.form e = 1) :
    logHessianForm P e e u = fderiv ℝ (diagonalCubic P.form) e u / 3 := by
  have hpos : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  rw [logHessianForm_apply P hpos, he, cubicHessian_radial,
    fderiv_diagonalCubic_at_one P.form e he]
  ring

/-- The genuine fully curried continuous trilinear form. -/
def fullyCurried (P : SymmetricTrilinearForm E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (((continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).toContinuousLinearEquiv).toContinuousLinearMap).comp
    ((rightCurried P).curryLeft)

@[simp] theorem fullyCurried_apply (P : SymmetricTrilinearForm E) (x u v : E) :
    fullyCurried P x u v = P.form ![x, u, v] := by
  change continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    ((rightCurried P).curryLeft x) u v = P.form ![x, u, v]
  rw [continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  have h : Fin.cons x (Fin.snoc (0 : Fin 0 → E) u) = ![x, u] := by ext i; fin_cases i <;> simp
  rw [h, rightCurried_apply]

/-- Whole-function identification is obtained from the true Hessian theorem. -/
theorem cubicHessian_eq_fullyCurried (P : SymmetricTrilinearForm E) (x : E) :
    cubicHessian P x = (6 : ℝ) • fullyCurried P x := by
  ext u v
  rw [cubicHessian_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]

/-- Actual derivative of the actual Hessian, proved via its global linear form. -/
theorem hasFDerivAt_cubicHessian (P : SymmetricTrilinearForm E) (x : E) :
    HasFDerivAt (cubicHessian P) ((6 : ℝ) • fullyCurried P) x := by
  let L : E →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := fullyCurried P
  have hlinear := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) ((6 : ℝ) • L) (x := x)
  have hfun : (fun z : E => (6 : ℝ) • L z) = (((6 : ℝ) • L) : E → (E →L[ℝ] E →L[ℝ] ℝ)) :=
    (funext fun z => (Pi.smul_apply (6 : ℝ) (L : E → (E →L[ℝ] E →L[ℝ] ℝ)) z).symm).trans
      (FunLike.coe_smul (6 : ℝ) L).symm
  exact (hlinear.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (congrFun hfun))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (cubicHessian_eq_fullyCurried P))

end
end AlbertGeometry.Cubic

namespace AlbertGeometry.BasedNormDerivativeTransport
noncomputable section
open AlbertGeometry.Cubic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace BasedNormIso

def normTrace (P : SymmetricTrilinearForm E) (e : E) : E →L[ℝ] ℝ :=
  fderiv ℝ (diagonalCubic P.form) e

def rawTraceForm (P : SymmetricTrilinearForm E) (e : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (normTrace P e).smulRight (normTrace P e) - cubicHessian P e

@[simp] theorem rawTraceForm_apply (P : SymmetricTrilinearForm E) (e u v : E) :
    rawTraceForm P e u v = normTrace P e u * normTrace P e v - cubicHessian P e u v := by
  simp [rawTraceForm, ContinuousLinearMap.smulRight_apply, smul_eq_mul]

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

namespace AlbertGeometry.BasedNormAdjointTransport
noncomputable section
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def rawBilinearForm (P : SymmetricTrilinearForm E) (e : E) :
    LinearMap.BilinForm ℝ E where
  toFun x := (rawTraceForm P e x).toLinearMap
  map_add' x y := by
    ext z; change rawTraceForm P e (x + y) z = rawTraceForm P e x z + rawTraceForm P e y z
    simp only [map_add, ContinuousLinearMap.add_apply]
  map_smul' t x := by
    ext z; change rawTraceForm P e (t • x) z = t * rawTraceForm P e x z
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem rawBilinearForm_nondegenerate (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1)
    (hpos : ∀ x : E, x ≠ 0 → 0 < logHessianForm P e x x) :
    (rawBilinearForm P e).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> {
    by_contra hne
    have hp := hpos x hne
    have hz : rawTraceForm P e x x = 0 := hx x
    rw [rawTraceForm_eq_three_logMetric P e he x x] at hz
    linarith }

def intrinsicAdjoint (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x : E) : E :=
  ((rawBilinearForm P e).toDual hB).symm (fderiv ℝ (diagonalCubic P.form) x).toLinearMap

theorem intrinsicAdjoint_pairing (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x y : E) :
    rawTraceForm P e (intrinsicAdjoint P e hB x) y = fderiv ℝ (diagonalCubic P.form) x y := by
  change rawBilinearForm P e
    (((rawBilinearForm P e).toDual hB).symm (fderiv ℝ (diagonalCubic P.form) x).toLinearMap) y = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ y

theorem intrinsicAdjoint_unique (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x z : E)
    (hz : ∀ y : E, rawTraceForm P e z y = fderiv ℝ (diagonalCubic P.form) x y) :
    z = intrinsicAdjoint P e hB x := by
  apply ((rawBilinearForm P e).toDual hB).injective
  ext y
  change rawTraceForm P e z y = rawTraceForm P e (intrinsicAdjoint P e hB x) y
  rw [hz, intrinsicAdjoint_pairing]

def intrinsicCross (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x y : E) : E :=
  intrinsicAdjoint P e hB (x + y) - intrinsicAdjoint P e hB x - intrinsicAdjoint P e hB y

def intrinsicS (P : SymmetricTrilinearForm E) (e x y : E) : ℝ :=
  normTrace P e x * normTrace P e y - rawTraceForm P e x y

def intrinsicProduct (P : SymmetricTrilinearForm E) (e : E)
    (hB : (rawBilinearForm P e).Nondegenerate) (x y : E) : E :=
  (1 / 2 : ℝ) • (intrinsicCross P e hB x y + normTrace P e x • y +
    normTrace P e y • x - intrinsicS P e x y • e)

end
end AlbertGeometry.BasedNormAdjointTransport
