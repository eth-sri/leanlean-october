module
public import AlbertRecognition.FrameRestriction
public import Mathlib.Algebra.Polynomial.Roots

/-! On any affine line the two diagonal restrictions are ordinary polynomials.
Equality of their squares thus fixes one sign along the entire line. -/
@[expose] public section
namespace AlbertRecognition
open Polynomial
noncomputable section

private def linePoly (B : SymmetricCubic) (x v : V) : ℝ[X] :=
  C (B.form x x x) + C (3 * B.form x x v)*X + C (3 * B.form x v v)*X^2 + C (B.form v v v)*X^3

private theorem eval_line (B : SymmetricCubic) (x v : V) (t : ℝ) :
    (linePoly B x v).eval t = B.form (x+t•v) (x+t•v) (x+t•v) := by
  simp [linePoly,B.swap12,B.swap23]; ring

private theorem polar (B C : SymmetricCubic) (r : ℝ) (h : ∀ x, B.form x x x = r * C.form x x x) (x y z : V) :
    B.form x y z = r * C.form x y z := by
  have hp := h (x+y+z); have xy := h (x+y); have xz := h (x+z); have yz := h (y+z)
  simp only [map_add,LinearMap.add_apply,B.swap12,B.swap23,C.swap12,C.swap23,mul_add] at hp xy xz yz ⊢
  linarith [h x,h y,h z]

theorem cubic_sign (B : SymmetricCubic) (hq : q B = q referenceCubic) :
    (∀ x y z, B.form x y z = CA x y z) ∨ (∀ x y z, B.form x y z = - CA x y z) := by
  by_cases all : ∀ x, B.form x x x = referenceCubic.form x x x
  · left; simpa using polar B referenceCubic 1 (by simpa using all)
  push_neg at all; obtain ⟨x,hx⟩ := all
  suffices opp : ∀ y, B.form y y y = -1 * referenceCubic.form y y y by right; simpa using polar _ _ _ opp
  intro y; let v := y-x
  have e : linePoly B x v ^ 2 = linePoly referenceCubic x v ^ 2 := by
    apply Polynomial.funext; intro t
    simp only [eval_pow,eval_line]; exact sq_eq_sq_iff_eq_or_eq_neg.mpr (point_sign hq _)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with hp | hn
  · exact (hx (by simpa [eval_line] using congrArg (eval 0) hp)).elim
  · simpa [eval_line,v] using congrArg (eval 1) hn
end
end AlbertRecognition
