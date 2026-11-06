import Mathlib.Tactic
import GS.MatrixGeometry.Base
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped ComplexOrder
namespace GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]
variable (A : KMat 𝕜 n)


/-- The actual nonsingular matrix inverse is used, not a chosen inverse. -/
theorem inv_mul  (hA : A.det ≠ 0) : A⁻¹ * A = 1 := by aesop

theorem cancel_right (X Y : KMat 𝕜 n) (hA : A.det ≠ 0)
    (h : X * A = Y * A) : X = Y := ((A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA))).mul_right_cancel h

theorem cancel_left (X Y : KMat 𝕜 n) (hA : A.det ≠ 0)
    (h : A * X = A * Y) : X = Y := ((A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA))).mul_left_cancel h

/-- Cancelling an invertible congruence does not assume symmetry of X or Y. -/
theorem cancel_congruence (X Y : KMat 𝕜 n) (hA : A.det ≠ 0)
    (h : Aᴴ * X * A = Aᴴ * Y * A) : X = Y := by
  apply cancel_left Aᴴ X Y (by aesop)
  exact cancel_right A (Aᴴ * X) (Aᴴ * Y) hA h









def cayley  : KMat 𝕜 n := (1 - A) * (1 + A)⁻¹

def admissible  : Prop := (1 + A).det ≠ 0

theorem cayley_mul  (hA : admissible A) :
    cayley A * (1 + A) = 1 - A := by
  simp only [cayley, Matrix.mul_assoc, inv_mul (1 + A) hA, Matrix.mul_one]

theorem one_add_cayley_mul  (hA : admissible A) :
    (1 + cayley A) * (1 + A) = (2 : ℝ) • (1 : KMat 𝕜 n) := by simp_all [cayley_mul,two_smul,Matrix.add_mul]

/-- The other Cayley denominator has an explicit right inverse. -/
theorem admissible_cayley  (hA : admissible A) :
    admissible (cayley A) := by
  have he : (1 + cayley A) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [Matrix.mul_smul, one_add_cayley_mul A hA, smul_smul]
    norm_num
  exact Matrix.det_ne_zero_of_right_inverse he

theorem cayley_involutive  (hA : admissible A) :
    cayley (cayley A) = A := by
  apply cancel_right (1 + cayley A) _ _ (admissible_cayley A hA)
  rw [cayley_mul (cayley A) (admissible_cayley A hA)]
  apply cancel_right (1 + A) _ _ hA
  linear_combination (norm := noncomm_ring)
    -cayley_mul A hA - A * cayley_mul A hA



theorem cayley_unitary  (hs : GS.MatrixBase.IsSkewHermitian A)
    (hA : admissible A) : Unitary (cayley A) := by
  apply Unitary.of_conjTranspose_mul
  apply cancel_congruence (1 + A) _ 1 hA
  have he := cayley_mul A hA
  have ht := congrArg Matrix.conjTranspose he
  simp only [Matrix.conjTranspose_mul] at ht
  change Aᴴ = -A at hs
  simp only [← Matrix.mul_assoc] at *
  rw [ht, Matrix.mul_assoc, he]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, hs]
  noncomm_ring


theorem cayley_isSkew (Q : KMat 𝕜 n) (hQ : Unitary Q)
    (hd : admissible Q) : GS.MatrixBase.IsSkewHermitian (cayley Q) := by
  have he := cayley_mul Q hd
  have ht := congrArg Matrix.conjTranspose he
  simp only [Matrix.conjTranspose_mul] at ht
  apply eq_neg_of_add_eq_zero_left
  apply cancel_congruence (1 + Q) _ 0 hd
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one] at ht ⊢
  linear_combination (norm := noncomm_ring)
    ht * (1 + Q) + (1 + Qᴴ) * he - 2 * hQ.1

@[simp] theorem admissible_zero : admissible (0 : KMat 𝕜 n) := by
  simp [admissible]

@[simp] theorem cayley_zero : cayley (0 : KMat 𝕜 n) = 1 := by
  simp [cayley]

@[simp] theorem admissible_one : admissible (1 : KMat 𝕜 n) := by
  simpa only [cayley_zero] using admissible_cayley (0 : KMat 𝕜 n) admissible_zero



/-- A skew-Hermitian matrix has an invertible Cayley denominator. -/
theorem admissible_of_isSkew  (hA : GS.MatrixBase.IsSkewHermitian A) : admissible A := by
  have hpos :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have he : (1 - A) * (1 + A) = 1 + Aᴴ * A := by
    rw [hA]
    noncomm_ring
  have hdet : ((1 - A) * (1 + A)).det ≠ 0 := by
    rw [he]
    exact (hpos.isUnit.map Matrix.detMonoidHom).ne_zero
  rw [Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2



/-- Matrix multiplication as a continuous bilinear map for the inherited pi norm. -/
def matrixMulCLM : KMat 𝕜 n →L[ℝ] KMat 𝕜 n →L[ℝ] KMat 𝕜 n :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (LinearMap.mul ℝ _)).toContinuousLinearMap

def matrixConjTransposeCLM := (Matrix.conjTransposeLinearEquiv (Fin n) (Fin n) ℝ 𝕜).toLinearMap.toContinuousLinearMap

@[fun_prop] theorem smooth_submodule_val {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) {r : WithTop ℕ∞} : ContDiff ℝ r (Subtype.val : S → F) :=
  S.subtypeL.contDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coordinatewise proof avoids a noncanonical matrix norm. -/
@[fun_prop] theorem smooth_mul_at {r : WithTop ℕ∞} {A B : E → KMat 𝕜 n} {x : E}
    (hA : ContDiffAt ℝ r A x) (hB : ContDiffAt ℝ r B x) :
    ContDiffAt ℝ r (fun y => A y * B y) x :=
  (matrixMulCLM (𝕜 := 𝕜) ).isBoundedBilinearMap.contDiff.contDiffAt.comp x (hA.prodMk hB)

@[fun_prop] theorem smooth_conjTranspose {r : WithTop ℕ∞} {A : E → KMat 𝕜 n}
    (hA : ContDiff ℝ r A) : ContDiff ℝ r (fun x => (A x)ᴴ) :=
  (matrixConjTransposeCLM (𝕜 := 𝕜) ).contDiff.comp hA

theorem smooth_det : ContDiff ℝ ⊤ (fun A : KMat 𝕜 n => A.det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem smooth_adjugate : ContDiff ℝ ⊤ (fun A : KMat 𝕜 n => A.adjugate) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [Matrix.adjugate_apply]
  apply smooth_det.comp
  apply contDiff_pi.mpr; intro a
  apply contDiff_pi.mpr; intro b
  by_cases ha : a = j <;> simp [Matrix.updateRow,ha] <;> fun_prop

/-- Inverse is smooth exactly where it is needed in all subsequent charts. -/
theorem smooth_inverse_at  (hA : A.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun B : KMat 𝕜 n => B⁻¹) A := by
  simpa only [Matrix.inv_def,Ring.inverse_eq_inv,Pi.smul_def',Pi.inv_def] using
    (smooth_det.contDiffAt.inv hA).smul smooth_adjugate.contDiffAt

theorem smooth_inverse_comp_at {A : E → KMat 𝕜 n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : (A x).det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun y => (A y)⁻¹) x :=
  (smooth_inverse_at (A x) hd).comp x hA

theorem smooth_cayley_at  (hA : admissible A) :
    ContDiffAt ℝ ⊤ cayley A := smooth_mul_at (contDiffAt_const.sub contDiffAt_id)
    (smooth_inverse_comp_at (contDiffAt_const.add contDiffAt_id) hA)

theorem smooth_cayley_comp_at {A : E → KMat 𝕜 n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : admissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => cayley (A y)) x :=
  (smooth_cayley_at (A x) hd).comp x hA

theorem admissible_open : IsOpen {A : KMat 𝕜 n | admissible A} := isOpen_ne.preimage (smooth_det.continuous.comp
    (continuous_const.add continuous_id))



theorem hasDerivAt_matrix_mul {f g : ℝ → KMat 𝕜 n} {u v : KMat 𝕜 n} {t : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => f s * g s) (u * g t + f t * v) t := by
  convert ((matrixMulCLM  ).isBoundedBilinearMap.hasFDerivAt (f t,g t)).comp_hasDerivAt t (hf.prodMk hg) using 1 <;> try rfl
  
  exact add_comm _ _


end GS.MatrixBase

namespace GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]
variable (A : KMat 𝕜 n)

@[fun_prop] theorem smooth_matrix_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : WithTop ℕ∞} {A B : E → KMat 𝕜 n} (hA : ContDiff ℝ r A) (hB : ContDiff ℝ r B) :
    ContDiff ℝ r (fun x => A x * B x) :=
  (matrixMulCLM (𝕜 := 𝕜) ).isBoundedBilinearMap.contDiff.comp (hA.prodMk hB)

attribute [-instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem chartInv_line_hasDerivAt_zero (Q A : KMat 𝕜 n) (hA : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => Q * cayley (t • A)) ((-2 : ℝ) • (Q * A)) 0 := by
  letI : NormedRing (KMat 𝕜 n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (KMat 𝕜 n) := Matrix.linftyOpNormedAlgebra
  have ha := (hasDerivAt_id (0 : ℝ)).smul_const A
  have hi := (hasFDerivAt_ringInverse  (1 : (KMat 𝕜 n)ˣ)).comp_hasDerivAt_of_eq
    0 ((hasDerivAt_const (0 : ℝ) (1 : KMat 𝕜 n)).add ha) (by simp)
  have h := (hasDerivAt_const (0 : ℝ) Q).mul
    (((hasDerivAt_const (0 : ℝ) (1 : KMat 𝕜 n)).sub ha).mul hi)
  simpa [cayley, Matrix.nonsing_inv_eq_ringInverse, Pi.mul_def, Pi.sub_def, Pi.add_def, Function.comp_def, neg_smul, two_smul,
    Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul] using! h


def unitCayley  := cayley ((-1 / 2 : ℝ) • A)
@[simp] theorem unitCayley_zero : unitCayley (0 : KMat 𝕜 n) = 1 := by simp [unitCayley]

@[fun_prop] theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → KMat 𝕜 n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, IsSkewHermitian (A x)) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
      (admissible_of_isSkew _ (skewAdjoint.smul_mem _ (hk x)))

theorem unitCayley_line_derivative  (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := chartInv_line_hasDerivAt_zero 1 ((-1 / 2 : ℝ) • A)
    (skewAdjoint.smul_mem _ hk)
  simpa only [unitCayley, smul_smul, mul_comm (-1 / 2 : ℝ), Matrix.one_mul,
    show (-2 : ℝ) * (-1 / 2) = 1 by norm_num, one_smul] using hd
end GS.MatrixBase
