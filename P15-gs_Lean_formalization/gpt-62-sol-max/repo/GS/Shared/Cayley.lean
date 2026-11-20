module

public import GS.Shared.Basic

public import Mathlib.Analysis.Calculus.Deriv.Mul

public import Mathlib.Analysis.Calculus.ContDiff.RCLike

public import Mathlib.Analysis.Calculus.Deriv.Add

public import Mathlib.Analysis.Calculus.Deriv.Star

public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Matrix ContinuousLinearMap Filter
open scoped ComplexOrder ContDiff Topology

namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

def cayley (A : M 𝕜 n) : M 𝕜 n := (2 : ℝ) • Ring.inverse (1 + A) - 1

def admissible (A : M 𝕜 n) : Prop := IsUnit (1 + A)

theorem one_add_cayley (A : M 𝕜 n) : 1 + cayley A = (2 : ℝ) • Ring.inverse (1 + A) := by
  unfold cayley; abel

theorem cayley_mul (A : M 𝕜 n) (hA : admissible A) : cayley A * (1 + A) = 1 - A := by
  rw [cayley, Matrix.sub_mul, Matrix.smul_mul, Ring.inverse_mul_cancel _ hA, Matrix.one_mul, two_smul]
  abel

theorem admissible_cayley (A : M 𝕜 n) (hA : admissible A) : admissible (cayley A) := by
  unfold admissible
  rw [one_add_cayley]
  exact hA.ringInverse.smul (Units.mk0 (2 : ℝ) (by norm_num))

theorem cayley_involutive (A : M 𝕜 n) (hA : admissible A) : cayley (cayley A) = A := by
  have hc := admissible_cayley A hA
  apply hc.mul_right_cancel
  have h : (1+A) * (1+cayley A) = (2 : ℝ) • 1 := by
    rw [one_add_cayley, Matrix.mul_smul, Ring.mul_inverse_cancel _ hA]
  grind [Matrix.add_mul, Matrix.one_mul, cayley_mul, eq_sub_of_add_eq', two_smul]

theorem cayley_unitary_iff (A : M 𝕜 n) (hA : admissible A) :
    Unitary (cayley A) ↔ IsSkewHermitian A := by
  let B := 1 + A
  let U := cayley A
  have h : Bᴴ * (Uᴴ * U) * B = (U * B)ᴴ * (U * B) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [show Unitary U ↔ Uᴴ * U = 1 from ⟨And.left, Unitary.of_conjTranspose_mul⟩,
    ← (show IsUnit B from hA).mul_left_inj, ← (show IsUnit Bᴴ from (show IsUnit B from hA).star).mul_right_inj,
    ← Matrix.mul_assoc Bᴴ (Uᴴ * U), ← Matrix.mul_assoc Bᴴ 1,
    h, cayley_mul A hA, Matrix.mul_one, ← sub_eq_zero]
  have he : (1-A)ᴴ * (1-A) - Bᴴ * B = -(2 : ℝ) • (Aᴴ + A) := by
    simp only [B, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      neg_smul, two_smul]
    noncomm_ring
  grind [smul_eq_zero, IsSkewHermitian, add_eq_zero_iff_eq_neg]

@[simp] theorem admissible_zero : admissible (0 : M 𝕜 n) := by
  simp [admissible]

@[simp] theorem cayley_zero : cayley (0 : M 𝕜 n) = 1 := by
  simp [cayley, two_smul]

@[simp] theorem admissible_one : admissible (1 : M 𝕜 n) := by
  simpa only [cayley_zero] using admissible_cayley (0 : M 𝕜 n) admissible_zero

/-- A skew-Hermitian matrix has an invertible Cayley denominator. -/
theorem admissible_of_isSkew (A : M 𝕜 n) (hA : IsSkewHermitian A) : admissible A := by
  have hpos : (1 + Aᴴ * A).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have he : (1 - A) * (1 + A) = 1 + Aᴴ * A := by
    rw [hA]
    noncomm_ring
  exact isUnit_of_mul_isUnit_right (he.symm ▸ hpos.isUnit : IsUnit ((1-A)*(1+A)))

theorem cayley_intertwine (A B P : M 𝕜 n) (hA : admissible A)
    (hB : admissible B) (h : A * P = P * B) :
    cayley A * P = P * cayley B := by
  apply IsUnit.mul_right_cancel (show IsUnit (1+B) from hB)
  have hp : P * (1 + B) = (1 + A) * P := by simp [Matrix.mul_add, Matrix.add_mul, h]
  rw [Matrix.mul_assoc (cayley A), hp, ← Matrix.mul_assoc, cayley_mul A hA,
    Matrix.mul_assoc P, cayley_mul B hB]
  simp [Matrix.sub_mul, Matrix.mul_sub, h]

/-- The operator norm is needed for analytic inversion and exponentiation. -/
def OpMatrix (𝕜 : Type*) (n : ℕ) := M 𝕜 n

instance : NormedRing (OpMatrix 𝕜 n) := Matrix.linftyOpNormedRing
instance : NormedAlgebra ℝ (OpMatrix 𝕜 n) := Matrix.linftyOpNormedAlgebra
instance : FiniteDimensional ℝ (OpMatrix 𝕜 n) := inferInstanceAs (FiniteDimensional ℝ (M 𝕜 n))

def asOp : M 𝕜 n ≃L[ℝ] OpMatrix 𝕜 n := (LinearEquiv.refl ℝ (M 𝕜 n)).toContinuousLinearEquiv

private theorem smooth_inverse_at (A : M 𝕜 n) (hA : IsUnit A) :
    ContDiffAt ℝ ⊤ Ring.inverse A := by
  obtain ⟨u,rfl⟩ := hA
  let e := asOp (𝕜 := 𝕜) (n := n)
  exact e.symm.contDiff.contDiffAt.comp (u : M 𝕜 n)
    ((contDiffAt_ringInverse ℝ (n := ⊤) (show (OpMatrix 𝕜 n)ˣ from u)).comp (u : M 𝕜 n) e.contDiff.contDiffAt)

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_cayley_at (A : M 𝕜 n) (hA : admissible A) :
    ContDiffAt ℝ ⊤ cayley A :=
  (((smooth_inverse_at _ hA).comp A (contDiffAt_const.add contDiffAt_id)).const_smul (2 : ℝ)).sub contDiffAt_const

theorem smooth_cayley_comp_at {A : E → M 𝕜 n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : admissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => cayley (A y)) x :=
  (smooth_cayley_at (A x) hd).comp x hA

theorem admissible_open : IsOpen {A : M 𝕜 n | admissible A} :=
  (Units.isOpen (R := OpMatrix 𝕜 n)).preimage (continuous_const.add asOp.continuous)
end Smooth

theorem cayley_hasFDerivAt_zero :
    HasFDerivAt (cayley (𝕜 := 𝕜) (n := n)) ((-2 : ℝ) • (1 : M 𝕜 n →L[ℝ] M 𝕜 n)) 0 := by
  let R := OpMatrix 𝕜 n
  let e := asOp (𝕜 := 𝕜) (n := n)
  have hi : HasFDerivAt Ring.inverse (-mulLeftRight ℝ R 1 1) (1 + e 0) := by
    simpa using hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Rˣ)
  have h := hi.comp 0 (e.hasFDerivAt.const_add (1 : R))
  have hc := (e.symm.hasFDerivAt.comp 0 h).const_smul (2 : ℝ) |>.sub_const 1
  exact hc.congr_fderiv (by aesop)

end GS.Shared
