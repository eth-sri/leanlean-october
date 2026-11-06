/-
Geometric foundation. No geometric recognition or arbitrary-polynomial representation
correspondence is claimed here.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators ContDiff

namespace AlbertGeometry.Cubic


/-- An actual continuous trilinear form, not a collection of desired jets. -/
abbrev TrilinearForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ

theorem eval_const_hasFDerivAt {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y →L[ℝ] Z} {f' : X →L[ℝ] Y →L[ℝ] Z} {x : X} (hf : HasFDerivAt f f' x) (u : Y) :
    HasFDerivAt (fun y => f y u) (f'.flip u) x := by
  simpa using hf.clm_apply (hasFDerivAt_const u x)

theorem injective_of_pos {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hp : ∀ u, u ≠ 0 → 0 < B u u) : Function.Injective B :=
  fun u v huv => by_contra fun h => by simpa [huv] using hp _ (sub_ne_zero.2 h)

theorem isInvertible_of_pos {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {B : V →L[ℝ] V →L[ℝ] ℝ} (hp : ∀ u, u ≠ 0 → 0 < B u u) :
    B.IsInvertible :=
  let d := LinearMap.toContinuousLinearMap
  have := d.finiteDimensional
  ⟨(LinearEquiv.ofInjectiveOfFinrankEq B.toLinearMap (injective_of_pos hp)
    (Subspace.dual_finrank_eq.symm.trans d.finrank_eq)).toContinuousLinearEquiv, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous linear diagonal embedding into the three slots. -/
def diagonalEmbedding : E →L[ℝ] (Fin 3 → E) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E)

@[simp] theorem diagonalEmbedding_apply (x : E) (i : Fin 3) :
    diagonalEmbedding x i = x := rfl

/-- The literal diagonal degree-three polynomial attached to the form. -/
def diagonalCubic (P : TrilinearForm E) (x : E) : ℝ :=
  P (fun _ : Fin 3 => x)

/-- The explicit slot-sum candidate, subsequently certified by HasFDerivAt.
The derivative itself is never defined by an assumed Euler/gradient identity. -/
def diagonalDerivative (P : TrilinearForm E) (x : E) : E →L[ℝ] ℝ :=
  (P.linearDeriv (fun _ => x)).comp (diagonalEmbedding)

/-- The actual derivative follows by the chain rule for the diagonal embedding. -/
theorem hasFDerivAt_diagonalCubic (P : TrilinearForm E) (x : E) :
    HasFDerivAt (diagonalCubic P) (diagonalDerivative P x) x := by
  change HasFDerivAt
    (fun z : E => P (diagonalEmbedding z))
    ((P.linearDeriv (diagonalEmbedding x)).comp
      (diagonalEmbedding)) x
  exact (P.hasFDerivAt (diagonalEmbedding x)).comp x
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
    ContDiff ℝ n (diagonalCubic P) := by
  exact P.contDiff.comp (diagonalEmbedding (E := E)).contDiff

/-- The three replacements are the differentiated slots of the true form. -/
theorem diagonalDerivative_apply (P : TrilinearForm E) (x y : E) :
    diagonalDerivative P x y =
      ∑ i : Fin 3, P (Function.update (fun _ : Fin 3 => x) i y) := by rfl

/-- Euler's radial identity requires no symmetry premise. -/
theorem diagonalDerivative_radial (P : TrilinearForm E) (x : E) :
    diagonalDerivative P x x = 3 * diagonalCubic P x := by
  have hu (i : Fin 3) :
      Function.update (fun _ => x) i x = (fun _ => x) :=
    Function.update_eq_self i (fun _ => x)
  rw [diagonalDerivative_apply]
  simp only [hu, Fin.sum_univ_three]
  change P (fun _ : Fin 3 => x) + P (fun _ => x) +
    P (fun _ => x) = 3 * P (fun _ => x)
  ring

/-- Euler is stated for the genuine Fréchet derivative. -/
theorem fderiv_diagonalCubic_radial (P : TrilinearForm E) (x : E) :
    fderiv ℝ (diagonalCubic P) x x = 3 * diagonalCubic P x := by
  rw [fderiv_diagonalCubic, diagonalDerivative_radial]

/-- A normalized base point is a regular point; this is not assumed as a field. -/
theorem fderiv_diagonalCubic_at_one (P : TrilinearForm E) (e : E)
    (he : diagonalCubic P e = 1) :
    fderiv ℝ (diagonalCubic P) e e = 3 := by
  rw [fderiv_diagonalCubic_radial, he]
  ring

/-- Symmetry of a trilinear representation. The full arbitrary homogeneous-cubic
correspondence with such representations is not part of this structure definition;
this structure is not a replacement recognition endpoint or a Jordan premise. -/
structure SymmetricTrilinearForm (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : TrilinearForm E
  swap12 : ∀ (x y z : E), form ![x, y, z] = form ![y, x, z]
  swap23 : ∀ (x y z : E), form ![x, y, z] = form ![x, z, y]

/-- The true slot-sum derivative simplifies to the expected threefold term. -/
theorem diagonalDerivative_apply_symmetric (P : SymmetricTrilinearForm E)
    (x y : E) :
    diagonalDerivative P.form x y = 3 * P.form ![x, x, y] := by
  have h0 : Function.update (fun _ : Fin 3 => x) 0 y = ![y, x, x] := by
    ext i
    fin_cases i <;> simp
  have h1 : Function.update (fun _ : Fin 3 => x) 1 y = ![x, y, x] := by
    ext i
    fin_cases i <;> simp
  have h2 : Function.update (fun _ : Fin 3 => x) 2 y = ![x, x, y] := by
    ext i
    fin_cases i <;> simp
  rw [diagonalDerivative_apply, Fin.sum_univ_three, h0, h1, h2]
  simp [P.swap12 y x x, P.swap23 x y x]
  ring

/-- The symmetric formula is identified with actual fderiv, not defined as it. -/
theorem fderiv_diagonalCubic_apply_symmetric (P : SymmetricTrilinearForm E)
    (x y : E) :
    fderiv ℝ (diagonalCubic P.form) x y = 3 * P.form ![x, x, y] := by
  rw [fderiv_diagonalCubic, diagonalDerivative_apply_symmetric]

end AlbertGeometry.Cubic
