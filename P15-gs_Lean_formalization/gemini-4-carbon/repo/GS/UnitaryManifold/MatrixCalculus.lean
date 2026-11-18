module

public import GS.Unitary.GeometryAlgebra
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

theorem hasDerivAt_matrix_conjTranspose {f : ℝ → Matrix (Fin n) (Fin n) 𝕂}
    {u : Matrix (Fin n) (Fin n) 𝕂} {t₀ : ℝ} (hf : HasDerivAt f u t₀) :
    HasDerivAt (fun t => (f t)ᴴ) uᴴ t₀ :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j)) i).star

theorem hasDerivAt_matrix_mul {f g : ℝ → Matrix (Fin n) (Fin n) 𝕂}
    {u v : Matrix (Fin n) (Fin n) 𝕂} {t₀ : ℝ} (hf : HasDerivAt f u t₀) (hg : HasDerivAt g v t₀) :
    HasDerivAt (fun t => f t * g t) (u * g t₀ + f t₀ * v) t₀ := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  simpa only [Finset.sum_apply, Finset.sum_fn, Pi.mul_apply, Pi.mul_def] using
    HasDerivAt.sum (u := Finset.univ) fun k _ =>
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) k).mul
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k)) j)

theorem hasDerivAt_product2 (P : Matrix (Fin n) (Fin n) 𝕂)
    {f g : ℝ → Matrix (Fin n) (Fin n) 𝕂} {u v : Matrix (Fin n) (Fin n) 𝕂} {t₀ : ℝ}
    (hf : HasDerivAt f u t₀) (hg : HasDerivAt g v t₀) :
    HasDerivAt (fun t => GS.UnitaryGeometry.kProduct2 (f t) P (g t))
      (u * P * g t₀ + f t₀ * P * v) t₀ := by
  simpa only [GS.UnitaryGeometry.kProduct2, Matrix.mul_zero, add_zero] using
    hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hf (hasDerivAt_const t₀ P)) hg

end GS.UnitaryManifold
