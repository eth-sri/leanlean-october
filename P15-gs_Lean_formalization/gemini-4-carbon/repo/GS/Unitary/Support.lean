module

public import GS.ComplexAlgebra
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

def CSupported {n : ℕ} (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

def KSSupported (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

@[simp] theorem ksSupported_complex_iff (block : Fin n → ℕ) (A : CMat n) :
    KSSupported block A ↔ CSupported block A := Iff.rfl

namespace CSupported
variable {block : Fin n → ℕ} {A B : CMat n}
@[simp] theorem zero : CSupported block (0 : CMat n) := fun _ _ _ => rfl
@[simp] theorem one : CSupported block (1 : CMat n) := fun i j hij => by
  simp [show i ≠ j from fun h => hij (congrArg block h)]
theorem conjTranspose (h : CSupported block A) : CSupported block Aᴴ := fun i j hij => by
  simp [Matrix.conjTranspose_apply, h j i (Ne.symm hij)]
theorem add (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A + B) := fun i j hij => by simp [hA i j hij, hB i j hij]
theorem neg (hA : CSupported block A) : CSupported block (-A) := fun i j hij => by simp [hA i j hij]
theorem real_smul (a : ℝ) (hA : CSupported block A) : CSupported block (a • A) := fun i j hij => by
  simp [hA i j hij]
theorem mul (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A * B) := fun i j hij => by
  rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : block i = block k
  · rw [hB k j (fun h => hij (hik.trans h)), mul_zero]
  · rw [hA i k hik, zero_mul]
end CSupported

namespace KSSupported
variable {block : Fin n → ℕ} {A B : Matrix (Fin n) (Fin n) 𝕂}
@[simp] theorem zero : KSSupported block (0 : Matrix (Fin n) (Fin n) 𝕂) := fun _ _ _ => rfl
@[simp] theorem one : KSSupported block (1 : Matrix (Fin n) (Fin n) 𝕂) := fun i j hij => by
  simp [show i ≠ j from fun h => hij (congrArg block h)]
theorem conjTranspose (h : KSSupported block A) : KSSupported block Aᴴ := fun i j hij => by
  simp [Matrix.conjTranspose_apply, h j i (Ne.symm hij)]
theorem add (hA : KSSupported block A) (hB : KSSupported block B) :
    KSSupported block (A + B) := fun i j hij => by simp [hA i j hij, hB i j hij]
theorem neg (hA : KSSupported block A) : KSSupported block (-A) := fun i j hij => by
  simp [hA i j hij]
theorem real_smul (a : ℝ) (hA : KSSupported block A) : KSSupported block (a • A) := fun i j hij => by
  simp [hA i j hij]
theorem mul (hA : KSSupported block A) (hB : KSSupported block B) :
    KSSupported block (A * B) := fun i j hij => by
  rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : block i = block k
  · rw [hB k j (fun h => hij (hik.trans h)), mul_zero]
  · rw [hA i k hik, zero_mul]
end KSSupported

def cMask (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  fun i j => if p i j then A i j else 0

def CMaskSymmetric (p : Fin n → Fin n → Prop) : Prop := ∀ i j, p i j ↔ p j i

theorem cMask_add (p : Fin n → Fin n → Prop) [DecidableRel p] (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cMask p (A + B) = cMask p A + cMask p B := by
  ext i j; by_cases hp : p i j <;> simp [cMask, hp]
theorem cMask_real_smul (p : Fin n → Fin n → Prop) [DecidableRel p]
    (a : ℝ) (A : Matrix (Fin n) (Fin n) 𝕂) : cMask p (a • A) = a • cMask p A := by
  ext i j; by_cases hp : p i j <;> simp [cMask, hp]
theorem cMask_conjTranspose {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : Matrix (Fin n) (Fin n) 𝕂) : (cMask p A)ᴴ = cMask p Aᴴ := by
  ext i j
  by_cases h : p i j
  · simp [cMask, Matrix.conjTranspose_apply, h, (hp i j).mp h]
  · simp [cMask, Matrix.conjTranspose_apply, h, show ¬p j i from fun hh => h ((hp i j).mpr hh)]

def cBlockProjection (block : Fin n → ℕ) (A : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  cMask (fun i j => block i = block j) A

theorem cBlockProjection_mul_left (block : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) 𝕂)
    (hA : KSSupported block A) :
    cBlockProjection block (A * B) = A * cBlockProjection block B := by
  ext i j
  by_cases hij : block i = block j
  · simp only [cBlockProjection, cMask, hij, ↓reduceIte, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : block i = block k
    · simp [hik.symm.trans hij]
    · rw [hA i k hik]; simp
  · simp only [cBlockProjection, cMask, hij, ↓reduceIte, Matrix.mul_apply]
    symm; refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : block i = block k
    · simp [show block k ≠ block j from fun h => hij (hik.trans h)]
    · rw [hA i k hik]; simp

end GS.UnitaryGeometry
