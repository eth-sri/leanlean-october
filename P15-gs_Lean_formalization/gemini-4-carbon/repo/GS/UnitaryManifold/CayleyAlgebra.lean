module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import GS.Unitary.Projection
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

theorem inv_mul (A : Matrix (Fin n) (Fin n) 𝕂) (hA : A.det ≠ 0) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)

theorem mul_inv (A : Matrix (Fin n) (Fin n) 𝕂) (hA : A.det ≠ 0) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)

theorem cancel_right (A X Y : Matrix (Fin n) (Fin n) 𝕂) (hA : A.det ≠ 0)
    (h : X * A = Y * A) : X = Y := by
  simpa only [Matrix.mul_assoc, mul_inv A hA, Matrix.mul_one] using congrArg (· * A⁻¹) h

theorem cancel_left (A X Y : Matrix (Fin n) (Fin n) 𝕂) (hA : A.det ≠ 0)
    (h : A * X = A * Y) : X = Y := by
  simpa only [← Matrix.mul_assoc, inv_mul A hA, Matrix.one_mul] using congrArg (A⁻¹ * ·) h

theorem cancel_congruence (A X Y : Matrix (Fin n) (Fin n) 𝕂) (hA : A.det ≠ 0)
    (h : Aᴴ * X * A = Aᴴ * Y * A) : X = Y :=
  cancel_left Aᴴ X Y (by simpa only [Matrix.det_conjTranspose, star_ne_zero] using hA)
    (cancel_right A (Aᴴ * X) (Aᴴ * Y) hA h)

theorem supported_sub (block : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) 𝕂)
    (hA : KSSupported block A) (hB : KSSupported block B) : KSSupported block (A - B) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

theorem blockProjection_eq_self (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂)
    (hA : KSSupported block A) : cBlockProjection block A = A := by
  ext i j; by_cases h : block i = block j <;> simp [cBlockProjection, cMask, h, hA i j]

theorem supported_of_blockProjection_eq (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂)
    (hA : cBlockProjection block A = A) : KSSupported block A := fun i j hij => by
  simpa [cBlockProjection, cMask, hij] using (congrArg (fun M => M i j) hA).symm

theorem supported_inverse (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂)
    (hA : KSSupported block A) (hdet : A.det ≠ 0) : KSSupported block A⁻¹ := by
  apply supported_of_blockProjection_eq block A⁻¹
  apply cancel_left A _ _ hdet
  calc A * cBlockProjection block A⁻¹ = cBlockProjection block (A * A⁻¹) :=
        (cBlockProjection_mul_left block A A⁻¹ hA).symm
    _ = cBlockProjection block 1 := by rw [mul_inv A hdet]
    _ = 1 := blockProjection_eq_self block 1 KSSupported.one
    _ = A * A⁻¹ := (mul_inv A hdet).symm

def cayley (A : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 := (1 - A) * (1 + A)⁻¹

def admissible (A : Matrix (Fin n) (Fin n) 𝕂) : Prop := (1 + A).det ≠ 0

theorem cayley_mul (A : Matrix (Fin n) (Fin n) 𝕂) (hA : admissible A) :
    cayley A * (1 + A) = 1 - A := by
  simp only [cayley, Matrix.mul_assoc, inv_mul (1 + A) hA, Matrix.mul_one]

theorem one_add_cayley_mul (A : Matrix (Fin n) (Fin n) 𝕂) (hA : admissible A) :
    (1 + cayley A) * (1 + A) = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) 𝕂) := by
  rw [Matrix.add_mul, Matrix.one_mul, cayley_mul A hA, two_smul ℝ]; abel

theorem admissible_cayley (A : Matrix (Fin n) (Fin n) 𝕂) (hA : admissible A) :
    admissible (cayley A) := by
  have he : (1 + cayley A) * ((1 / 2 : ℝ) • (1 + A)) = 1 := by
    rw [Matrix.mul_smul, one_add_cayley_mul A hA, smul_smul]; norm_num
  exact Matrix.det_ne_zero_of_right_inverse he

theorem cayley_involutive (A : Matrix (Fin n) (Fin n) 𝕂) (hA : admissible A) :
    cayley (cayley A) = A := by
  apply cancel_right (1 + cayley A) _ _ (admissible_cayley A hA)
  rw [cayley_mul (cayley A) (admissible_cayley A hA)]
  apply cancel_right (1 + A) _ _ hA
  calc (1 - cayley A) * (1 + A) = (1 + A) - (1 - A) := by
        rw [Matrix.sub_mul, Matrix.one_mul, cayley_mul A hA]
    _ = A * ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) 𝕂)) := by rw [two_smul ℝ]; noncomm_ring
    _ = A * ((1 + cayley A) * (1 + A)) := by rw [one_add_cayley_mul A hA]
    _ = A * (1 + cayley A) * (1 + A) := (Matrix.mul_assoc _ _ _).symm

theorem cayley_supported (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂)
    (hs : KSSupported block A) (hA : admissible A) : KSSupported block (cayley A) :=
  (supported_sub block 1 A KSSupported.one hs).mul
    (supported_inverse block (1 + A) (KSSupported.one.add hs) hA)

theorem cayley_unitary (A : Matrix (Fin n) (Fin n) 𝕂) (hs : GS.IsSkewHermitian A)
    (hA : admissible A) : GS.KUnitary (cayley A) := by
  suffices hh : (cayley A)ᴴ * cayley A = 1 from ⟨hh, mul_eq_one_comm.mp hh⟩
  apply cancel_congruence (1 + A) _ 1 hA
  have he := cayley_mul A hA
  have ht : (1 + A)ᴴ * (cayley A)ᴴ = (1 - A)ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose he
  calc (1 + A)ᴴ * ((cayley A)ᴴ * cayley A) * (1 + A)
    _ = ((1 + A)ᴴ * (cayley A)ᴴ) * (cayley A * (1 + A)) := by noncomm_ring
    _ = (1 - A)ᴴ * (1 - A) := by rw [ht, he]
    _ = (1 + A)ᴴ * (1 : Matrix (Fin n) (Fin n) 𝕂) * (1 + A) := by
      change Aᴴ = -A at hs
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hs]
      noncomm_ring

theorem cayley_isSkew (Q : Matrix (Fin n) (Fin n) 𝕂) (hQ : GS.KUnitary Q)
    (hd : admissible Q) : GS.IsSkewHermitian (cayley Q) := by
  have he := cayley_mul Q hd
  have ht : (1 + Q)ᴴ * (cayley Q)ᴴ = (1 - Q)ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose he
  refine eq_neg_of_add_eq_zero_left (cancel_congruence (1 + Q) _ 0 hd ?_)
  calc (1 + Q)ᴴ * ((cayley Q)ᴴ + cayley Q) * (1 + Q)
    _ = ((1 + Q)ᴴ * (cayley Q)ᴴ) * (1 + Q) + (1 + Q)ᴴ * (cayley Q * (1 + Q)) := by noncomm_ring
    _ = (1 - Q)ᴴ * (1 + Q) + (1 + Q)ᴴ * (1 - Q) := by rw [ht, he]
    _ = (2 : ℝ) • (1 - Qᴴ * Q) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, two_smul ℝ]
      noncomm_ring
    _ = (1 + Q)ᴴ * (0 : Matrix (Fin n) (Fin n) 𝕂) * (1 + Q) := by rw [hQ.1]; simp

@[simp] theorem admissible_zero : admissible (0 : Matrix (Fin n) (Fin n) 𝕂) := by simp [admissible]
@[simp] theorem cayley_zero : cayley (0 : Matrix (Fin n) (Fin n) 𝕂) = 1 := by simp [cayley]
@[simp] theorem admissible_one : admissible (1 : Matrix (Fin n) (Fin n) 𝕂) := by
  simpa only [cayley_zero] using admissible_cayley (0 : Matrix (Fin n) (Fin n) 𝕂) admissible_zero
@[simp] theorem cayley_one : cayley (1 : Matrix (Fin n) (Fin n) 𝕂) = 0 := by simp [cayley]

theorem admissible_of_isSkew (A : Matrix (Fin n) (Fin n) 𝕂) (hA : GS.IsSkewHermitian A) :
    admissible A := by
  intro hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have h2 : ((1 + Aᴴ * A) *ᵥ v) = 0 := by
    have he : 1 + Aᴴ * A = (1 - A) * (1 + A) := by change Aᴴ = -A at hA; rw [hA]; noncomm_ring
    rw [he, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hd := congrArg (fun w => RCLike.re (star v ⬝ᵥ w)) h2
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_zero,
    RCLike.zero_re, map_add, ← Matrix.mulVec_mulVec] at hd
  have hAv : star v ⬝ᵥ (Aᴴ *ᵥ (A *ᵥ v)) = star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rw [hAv] at hd
  have hsq (u : Fin n → 𝕂) : RCLike.re (star u ⬝ᵥ u) = ∑ i, ‖u i‖ ^ 2 := by
    simp only [dotProduct, Pi.star_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [hsq v, hsq (A *ᵥ v)] at hd
  have hv_norm : ∑ i, ‖v i‖ ^ 2 = 0 :=
    le_antisymm (by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖(A *ᵥ v) i‖])
      (Finset.sum_nonneg fun i _ => sq_nonneg ‖v i‖)
  apply hv0; ext i
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖v j‖).mp hv_norm i (Finset.mem_univ i)))

end GS.UnitaryManifold
