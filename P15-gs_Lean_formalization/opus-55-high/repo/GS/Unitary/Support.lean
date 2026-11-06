module

public import GS.ComplexAlgebra
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing

@[expose] public section


/-! Complex support algebra uses conjugate transpose throughout. -/
noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

/-- A complex matrix with entries only within equal block labels. -/
def CSupported (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

namespace CSupported
variable {block : Fin n → ℕ} {A B : CMat n}
@[simp] theorem zero : CSupported block (0 : CMat n) := fun _ _ _ => rfl
@[simp] theorem one : CSupported block (1 : CMat n) := by
  intro i j hij
  simp [show i ≠ j by grind]
theorem conjTranspose (h : CSupported block A) : CSupported block Aᴴ := by
  intro i j hij
  aesop
theorem add (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A+B) := by
  intro i j hij
  simp [Matrix.add_apply, hA i j hij, hB i j hij]
theorem real_smul (a : ℝ) (hA : CSupported block A) : CSupported block (a • A) := by
  intro i j hij
  aesop
theorem mul (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases hit : block i = block t
  · aesop
  aesop
end CSupported







end GS.UnitaryGeometry
