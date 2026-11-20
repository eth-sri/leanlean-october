module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! Matrix operations used in both the orthogonal and the unitary orbit.
All smoothness and linearity statements are over the reals, for the entrywise topology. -/
noncomputable section
open Matrix
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Isometric
abbrev Square (𝕜 : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕜
abbrev Layer (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := StarSubalgebra ℝ (Square 𝕜 n)
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

abbrev Skew (A : Square 𝕜 n) := Aᴴ = -A
abbrev IsU {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι 𝕜) := Aᴴ * A = 1 ∧ A * Aᴴ = 1
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma IsU.conjTranspose {A : Matrix ι ι 𝕜} (h : IsU A) : IsU Aᴴ := Unitary.star_mem h
lemma IsU.mul {A B : Matrix ι ι 𝕜} (h : IsU A) (h' : IsU B) : IsU (A*B) :=
  (unitary _).mul_mem h h'

lemma IsU.of_left {A : Matrix ι ι 𝕜} (h : Aᴴ * A = 1) : IsU A := ⟨h, mul_eq_one_comm.mp h⟩
lemma IsU.one : IsU (1 : Matrix ι ι 𝕜) := (unitary _).one_mem

def product₂ (L P R : Square 𝕜 n) := L * P * R

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → Square 𝕜 n} {x : E}

@[fun_prop] theorem smooth_mul_at (hA : ContDiffAt ℝ ⊤ A x) (hB : ContDiffAt ℝ ⊤ B x) :
    ContDiffAt ℝ ⊤ (fun y => A y * B y) x := by
  apply contDiffAt_pi.mpr; intro i; apply contDiffAt_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hB k) j)

@[fun_prop] theorem smooth_matrix_product (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun y => A y * B y) :=
  contDiff_iff_contDiffAt.mpr fun _ => smooth_mul_at hA.contDiffAt hB.contDiffAt

@[fun_prop] theorem smooth_conjTranspose_at (hA : ContDiffAt ℝ ⊤ A x) :
    ContDiffAt ℝ ⊤ (fun y => (A y)ᴴ) x := by
  apply contDiffAt_pi.mpr; intro i; apply contDiffAt_pi.mpr; intro j
  exact (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).contDiff.contDiffAt.comp x
    (contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i)

variable {f g : ℝ → Square 𝕜 n} {u v : Square 𝕜 n} {t : ℝ}

theorem hasDerivAt_matrix_conjTranspose (hf : HasDerivAt f u t) :
    HasDerivAt (fun r => (f r)ᴴ) uᴴ t :=
  hf.star

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_matrix_mul (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun r => f r * g r) (u * g t + f t * v) t := hf.mul hg

theorem hasDerivAt_product2 (P : Square 𝕜 n) (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun r => product₂ (f r) P (g r)) (u * P * g t + f t * P * v) t := by
  simpa [product₂] using
    hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hf (hasDerivAt_const t P)) hg

end GS.Isometric
