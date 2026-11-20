module

public import GS.Isometric.Matrix
public import Mathlib.Topology.Algebra.Group.Matrix

@[expose] public section

/-! The Cayley transform on a real or complex finite matrix algebra. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

open scoped ComplexOrder
lemma skew_smul (a : ℝ) {A : Square 𝕜 n} (h : Skew A) : Skew (a • A) := by simp [Skew, h]

def cayley (A : Square 𝕜 n) : Square 𝕜 n := (1 - A) * (1 + A)⁻¹

abbrev admissible (A : Square 𝕜 n) := IsUnit (1 + A)

theorem cayley_mul (A : Square 𝕜 n) (hA : admissible A) :
    cayley A * (1 + A) = 1 - A := by
  exact nonsing_inv_mul_cancel_right _ _ ((isUnit_iff_isUnit_det _).mp hA)

theorem one_add_cayley_mul (A : Square 𝕜 n) (hA : admissible A) :
    (1 + cayley A) * (1 + A) = (2 : ℝ) • (1 : Square 𝕜 n) := by
  rw [Matrix.add_mul, Matrix.one_mul, cayley_mul A hA]
  rw [two_smul ℝ]
  abel

/-- The other Cayley denominator has an explicit right inverse. -/
theorem admissible_cayley (A : Square 𝕜 n) (hA : admissible A) :
    admissible (cayley A) := by
  have he : (1 + cayley A) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [Matrix.mul_smul, one_add_cayley_mul A hA, smul_smul]
    norm_num
  exact IsUnit.of_mul_eq_one _ he

theorem cayley_involutive (A : Square 𝕜 n) (h : admissible A) : cayley (cayley A) = A := by
  apply (admissible_cayley A h).mul_left_inj.mp
  rw [cayley_mul _ (admissible_cayley A h)]
  apply h.mul_left_inj.mp
  rw [sub_mul, one_mul, cayley_mul _ h, mul_assoc, one_add_cayley_mul _ h, two_smul]
  noncomm_ring

/-- Cancelling the denominator reduces the Gram identity to the vanishing
of twice the Hermitian part; involutivity gives the converse transform. -/
theorem cayley_iff (A : Square 𝕜 n) (h : admissible A) : IsU (cayley A) ↔ Skew A := by
  have hstar : IsUnit (1+A)ᴴ := h.star
  have eq : (1+A)ᴴ * ((cayley A)ᴴ * cayley A) * (1+A) = (1-A)ᴴ * (1-A) := by
    rw [← mul_assoc, mul_assoc _ (cayley A), ← conjTranspose_mul, cayley_mul _ h]
  have diff : (1-A)ᴴ * (1-A) - (1+A)ᴴ * (1+A) = (-2:ℝ) • (Aᴴ + A) := by
    simp only [conjTranspose_sub,conjTranspose_add,conjTranspose_one,neg_smul,two_smul]; noncomm_ring
  rw [show IsU (cayley A) ↔ (cayley A)ᴴ * cayley A = 1 from ⟨And.left,IsU.of_left⟩,
    ← hstar.mul_right_inj, ← h.mul_left_inj, eq, mul_one, ← sub_eq_zero, diff]
  rw [smul_eq_zero, or_iff_right (by norm_num), add_eq_zero_iff_eq_neg]

theorem cayley_unitary (A : Square 𝕜 n) (hs : Skew A) (h : admissible A) : IsU (cayley A) := (cayley_iff A h).2 hs

theorem cayley_isSkew (A : Square 𝕜 n) (hu : IsU A) (h : admissible A) : Skew (cayley A) :=
  (cayley_iff _ (admissible_cayley A h)).1 (by rwa [cayley_involutive A h])

@[simp] theorem admissible_zero : admissible (0 : Square 𝕜 n) := by
  simp [admissible]

@[simp] theorem cayley_zero : cayley (0 : Square 𝕜 n) = 1 := by
  simp [cayley]

@[simp] theorem admissible_one : admissible (1 : Square 𝕜 n) := by
  simpa using admissible_cayley (0 : Square 𝕜 n) admissible_zero

/-- A skew-Hermitian matrix has an invertible Cayley denominator. -/
theorem admissible_of_isSkew (A : Square 𝕜 n) (hA : Skew A) : admissible A := by
  have hpos : (1 + Aᴴ * A).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)
  have he : (1 - A) * (1 + A) = 1 + Aᴴ * A := by
    rw [hA]
    noncomm_ring
  exact isUnit_of_mul_isUnit_right (he ▸ hpos.isUnit)

theorem cayley_intertwine (A B P : Square 𝕜 n) (hA : admissible A)
    (hB : admissible B) (h : A * P = P * B) :
    cayley A * P = P * cayley B := by
  apply hB.mul_left_inj.mp
  rw [mul_assoc, show P*(1+B) = (1+A)*P by noncomm_ring [h], ← mul_assoc, cayley_mul _ hA, mul_assoc, cayley_mul _ hB]
  noncomm_ring [h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Use a synonym to keep the two standard matrix norm instances separate.
private def Op (𝕜 : Type*) (n : ℕ) := Square 𝕜 n
private instance : NormedAddCommGroup (Op 𝕜 n) := Matrix.linftyOpNormedAddCommGroup
private instance : NormedSpace ℝ (Op 𝕜 n) := Matrix.linftyOpNormedSpace

open scoped Matrix.Norms.Operator in
private lemma op_inverse (A : Square 𝕜 n) (h : IsUnit A) :
    ContDiffAt ℝ ⊤ (fun B : Square 𝕜 n => B⁻¹) A := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]; exact contDiffAt_ringInverse ℝ h.unit

lemma smooth_inverse_at (A : Square 𝕜 n) (h : IsUnit A) :
    ContDiffAt ℝ ⊤ (fun B : Square 𝕜 n => B⁻¹) A := by
  let e : Square 𝕜 n ≃L[ℝ] Op 𝕜 n := ContinuousLinearEquiv.refl ℝ _
  have ho : ContDiffAt ℝ ⊤ (fun B : Op 𝕜 n => e (e.symm B)⁻¹) (e A) := op_inverse A h
  exact e.symm.contDiff.contDiffAt.comp A (ho.comp A e.contDiff.contDiffAt)

theorem smooth_cayley_at (A : Square 𝕜 n) (h : admissible A) : ContDiffAt ℝ ⊤ cayley A :=
  smooth_mul_at (contDiffAt_const.sub contDiffAt_id) ((smooth_inverse_at _ h).comp A (contDiffAt_const.add contDiffAt_id))

theorem smooth_cayley_comp_at {A : E → Square 𝕜 n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : admissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => cayley (A y)) x :=
  (smooth_cayley_at (A x) hd).comp x hA

theorem admissible_open : IsOpen {A : Square 𝕜 n | admissible A} := by
  simp only [admissible, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact isOpen_ne_fun (by fun_prop) continuous_const

open scoped Matrix.Norms.Operator in
theorem cayley_deriv {f : ℝ → Square 𝕜 n} {A : Square 𝕜 n} {t : ℝ} (hf : HasDerivAt f A t) (hz : f t = 0) :
    HasDerivAt (fun r => cayley (f r)) ((-2:ℝ) • A) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Square 𝕜 n)ˣ)).comp_hasDerivAt_of_eq t
    ((hasDerivAt_const t 1).add hf) (by simp [hz])
  simpa [cayley,nonsing_inv_eq_ringInverse,hz,neg_smul,two_smul,Pi.sub_def,Pi.add_def] using!
    ((hasDerivAt_const t 1).sub hf).mul hi

theorem cayley_line_derivative (A : Square 𝕜 n) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2:ℝ) • A) 0 := by
  apply cayley_deriv _ (zero_smul _ A); simpa using (hasDerivAt_id (0:ℝ)).smul_const A

/-- Cayley normalization with derivative +identity at zero. -/
def unitCayley (A : Square 𝕜 n) : Square 𝕜 n := cayley ((-1 / 2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : Square 𝕜 n) = 1 := by
  simp [unitCayley]

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Square 𝕜 n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, Skew (A x)) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  apply smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
  exact admissible_of_isSkew _ (by simp [Skew, hk x])

theorem unitCayley_line_derivative (A : Square 𝕜 n) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  simpa [unitCayley,← smul_comm _ (-1/2:ℝ),smul_smul,show (2:ℝ)*(-1/2) = -1 by norm_num] using cayley_line_derivative ((-1/2:ℝ) • A)

end GS.Isometric
