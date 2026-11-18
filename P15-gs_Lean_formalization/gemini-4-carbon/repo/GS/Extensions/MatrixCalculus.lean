module

public import GS.Extensions.ProjectionSmooth
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Analytic derivatives, rather than only polynomial Taylor identities

Matrix differentiation is reduced to finite
scalar sums, avoiding the need to silently change the matrix norm instance.
The final AD theorem starts with an actual HasFDerivAt hypothesis for the loss.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 theorem hasDerivAt_matrix_mul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hterm : ∀ k : Fin n,
      HasDerivAt (fun s => A s i k * B s k j)
        (A' i k * B t k j + A t i k * B' k j) t := by
    intro k
    exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_fn] using hs

 theorem hasDerivAt_matrix_transpose {A : ℝ → Mat n} {A' : Mat n} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s)ᵀ) A'ᵀ t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA j) i

 theorem hasDerivAt_product2 {B₂ B₁ : ℝ → Mat n} (P : Mat n)
    {η₂ η₁ : Mat n} {t : ℝ}
    (h₂ : HasDerivAt B₂ η₂ t) (h₁ : HasDerivAt B₁ η₁ t) :
    HasDerivAt (fun s => product2 (B₂ s) P (B₁ s))
      (η₂ * P * B₁ t + B₂ t * P * η₁) t := by
  have hleft := hasDerivAt_matrix_mul h₂ (hasDerivAt_const t P)
  have h := hasDerivAt_matrix_mul hleft h₁
  simpa only [product2, Matrix.mul_zero, add_zero] using h

 theorem hasDerivAt_affine_matrix (B η : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => B + s • η) η t := by
  have h := (hasDerivAt_id t).smul_const η
  simpa only [Pi.add_apply, Pi.add_def, id_eq, one_smul, zero_add] using (hasDerivAt_const t B).add h

end GS.Extensions
