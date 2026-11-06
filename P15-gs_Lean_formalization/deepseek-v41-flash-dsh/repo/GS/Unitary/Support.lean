module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.ComplexAlgebra
public import GS.Core


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Complex support algebra uses conjugate transpose throughout. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {n : ℕ}

/-- A complex matrix with entries only within equal block labels. -/
def CSupported (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

namespace CSupported
variable {block : Fin n → ℕ} {A B : CMat n}
@[simp] theorem zero : CSupported block (0 : CMat n) := by intro i j hij; rfl
@[simp] theorem one : CSupported block (1 : CMat n) := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (congrArg block h)
  simp [Matrix.one_apply, hne]
theorem conjTranspose (h : CSupported block A) : CSupported block Aᴴ := by
  intro i j hij
  simp [Matrix.conjTranspose_apply, h j i (Ne.symm hij)]
theorem add (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A+B) := by
  intro i j hij
  simp [Matrix.add_apply, hA i j hij, hB i j hij]
theorem neg (hA : CSupported block A) : CSupported block (-A) := by
  intro i j hij
  simp [Matrix.neg_apply, hA i j hij]
theorem real_smul (a : ℝ) (hA : CSupported block A) : CSupported block (a • A) := by
  intro i j hij
  simp [Matrix.smul_apply, hA i j hij]
theorem mul (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A*B) := by
  intro i j hij
  change (∑ k, A i k * B k j) = 0
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : block i = block k
  · have hkj : block k ≠ block j := fun h => hij (hik.trans h)
    rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]
end CSupported

/-- Arbitrary entry masks may describe unions of block supports. -/
def cMask (p : Fin n → Fin n → Prop) [DecidableRel p] (A : CMat n) : CMat n :=
  fun i j => if p i j then A i j else 0

def CMaskSymmetric (p : Fin n → Fin n → Prop) : Prop := ∀ i j, p i j ↔ p j i

theorem cMask_add (p : Fin n → Fin n → Prop) [DecidableRel p] (A B : CMat n) :
    cMask p (A+B) = cMask p A + cMask p B := by
  ext i j; by_cases hp : p i j <;> simp [cMask, hp]
theorem cMask_real_smul (p : Fin n → Fin n → Prop) [DecidableRel p]
    (a : ℝ) (A : CMat n) : cMask p (a • A) = a • cMask p A := by
  ext i j; by_cases hp : p i j <;> simp [cMask, hp]
theorem cMask_conjTranspose {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : CMat n) : (cMask p A)ᴴ = cMask p Aᴴ := by
  ext i j
  by_cases h : p i j
  · simp [cMask, Matrix.conjTranspose_apply, h, (hp i j).mp h]
  · have h' : ¬p j i := fun hh => h ((hp i j).mpr hh)
    simp [cMask, Matrix.conjTranspose_apply, h, h']

def cBlockProjection (block : Fin n → ℕ) (A : CMat n) : CMat n :=
  cMask (fun i j => block i = block j) A

theorem cBlockProjection_mul_left (block : Fin n → ℕ) (A B : CMat n)
    (hA : CSupported block A) :
    cBlockProjection block (A*B) = A * cBlockProjection block B := by
  ext i j
  by_cases hij : block i = block j
  · simp only [cBlockProjection,cMask,hij,if_pos,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hik : block i = block k
    · have hkj : block k = block j := hik.symm.trans hij
      simp [hkj]
    · rw [hA i k hik]; simp
  · simp only [cBlockProjection,cMask,hij,if_neg,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : block i = block k
    · have hkj : block k ≠ block j := fun h => hij (hik.trans h)
      simp [hkj]
    · rw [hA i k hik]; simp

end GS.UnitaryGeometry
