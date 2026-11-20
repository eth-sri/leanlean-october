/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Height.ProjectiveBox

/-! Bounded integral shears act on all projective representatives, preserve
primitivity, and preserve distinctness of their projective classes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The shear of a point `x` by `a`, keeping `x 0` and sending `x (j + 1)` to
`x (j + 1) + a j * x 0`; on the affine chart `x 0 = 1` it is the translation by `a`. -/
def homogeneousPointTranslation {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (x : Fin (n + 1) → R) : Fin (n + 1) → R :=
  Fin.cons (x 0) (fun j => x j.succ + a j * x 0)

/-- The shear by `-a` undoes the shear by `a`. -/
lemma homogeneousPointTranslation_inverse {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (x : Fin (n + 1) → R) :
    homogeneousPointTranslation (-a) (homogeneousPointTranslation a x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [homogeneousPointTranslation]

/-- If `z` lies in the box of radius `B ≥ 1` and every coordinate of `a` lies in `[0, d]`, then
the shear of `z` by `-a` lies in the box of radius `(d + 1) * B`. -/
lemma homogeneousPointTranslation_box {n d : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (a : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (z : IntPoint (n + 1)) (hz : InBox z B) (j : Fin (n + 1)) :
    |((homogeneousPointTranslation (-a) z j : ℤ) : ℝ)| ≤ ((d : ℝ) + 1) * B := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change |(z 0 : ℝ)| ≤ _
    nlinarith [hz 0]
  · change |((z k.succ + -a k * z 0 : ℤ) : ℝ)| ≤ _
    rw [Int.cast_add, Int.cast_mul, Int.cast_neg]
    have hak : |(a k : ℝ)| ≤ d := by
      rw [abs_of_nonneg (by aesop)]
      exact_mod_cast (ha k).2
    calc
      _ ≤ |(z k.succ : ℝ)| + |-(a k : ℝ) * (z 0)| := abs_add_le _ _
      _ = |(z k.succ : ℝ)| + |(a k : ℝ)| * |(z 0 : ℝ)| := by rw [abs_mul, abs_neg]
      _ ≤ B + d * B := by bound
      _ = _ := by ring

end
end CCDN
