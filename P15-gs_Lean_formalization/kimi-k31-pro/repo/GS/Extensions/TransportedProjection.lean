module

public import GS.GeometryAlgebra

@[expose] public section

noncomputable section
open Matrix
namespace GS.Extensions
variable {n : ℕ}

def lift (L R X : Mat n) : Mat n := L * X * R
def pull (L R Z : Mat n) : Mat n := Lᵀ * Z * Rᵀ

theorem pull_lift (L R Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    pull L R (lift L R Y) = Y := by
  calc
    pull L R (lift L R Y) = (Lᵀ*L)*Y*(R*Rᵀ) := by
      simp only [pull, lift, Matrix.mul_assoc]
    _ = Y := by rw [hL.1, hR.2]; simp

theorem lift_injective (L R : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    Function.Injective (lift L R) := by
  intro X Y h
  have := congrArg (pull L R) h
  simpa only [pull_lift L R _ hL hR] using this

theorem lift_frobInner (L R X Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobInner (lift L R X) (lift L R Y) = frobInner X Y := by
  unfold lift
  rw [frobInner_right_orthogonal R hR, frobInner_left_orthogonal L hL]

theorem frobInner_mul_right (A B C : Mat n) :
    frobInner (A*B) C = frobInner A (C*Bᵀ) := by
  calc
    frobInner (A*B) C = frobInner (A*B)ᵀ Cᵀ := (frobInner_transpose _ _).symm
    _ = frobInner Aᵀ (B*Cᵀ) := by
      rw [Matrix.transpose_mul, frobInner_mul_left, Matrix.transpose_transpose]
    _ = frobInner A (C*Bᵀ) := by
      have h := frobInner_transpose A (C*Bᵀ)
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h

end GS.Extensions
