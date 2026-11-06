/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.Determinant.SingularPlaneChart
import CCDN.Determinant.BlockDeterminant
import CCDN.ForMathlib.Matrix
import CCDN.Height.ProjectiveZeroLocus

/-! Local divisibility for homogeneous evaluation matrices at projective
points. Normalize a unit coordinate modulo the required prime power,
apply the singular affine estimate to the resulting approximate zeros,
then cancel the invertible row factors. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- If `x ≡ y` coordinatewise modulo `q`, then `f(x) ≡ f(y)` modulo `q` for every integer polynomial
`f`. -/
lemma dvd_eval_sub_of_dvd_coordinates {σ : Type*} (q : ℤ)
    (x y : σ → ℤ) (hxy : ∀ j, q ∣ x j - y j) (f : MvPolynomial σ ℤ) :
    q ∣ eval x f - eval y f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    simpa [eval_add, add_sub_add_comm] using dvd_add hf hg
  | mul_X f j hf =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    have he : eval x f * x j - eval y f * y j =
        (eval x f - eval y f) * x j + eval y f * (x j - y j) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right (hxy j) _)

/-- An integer `a` coprime to `q` has an inverse `u` modulo `q`, itself coprime to `q`. -/
lemma exists_integer_inverse_of_isCoprime {q a : ℤ} (h : IsCoprime q a) :
    ∃ u : ℤ, q ∣ u * a - 1 ∧ IsCoprime q u := by
  obtain ⟨v, u, he⟩ := h
  refine ⟨u, ⟨-v, by linear_combination he⟩, v, a, ?_⟩
  simpa [mul_comm a u] using he

/-- Unit normalization in the first homogeneous coordinate preserves the
evaluation of a degree-M form, up to the corresponding unit row factor. -/
lemma projective_chart_eval_congr {n M : ℕ} {q u : ℤ}
    (z : Fin (n + 3) → ℤ) (hu : q ∣ u * z 0 - 1)
    (F : MvPolynomial (Fin (n + 3)) ℤ) (hF : F.IsHomogeneous M) :
    q ∣ eval (fun j : Fin (n + 2) => u * z j.succ) (affineChart (n + 2) F) -
      u ^ M * eval z F := by
  rw [affineChart_eval, ← homogeneous_eval_smul hF]
  apply dvd_eval_sub_of_dvd_coordinates
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa using
      (show q ∣ -(u * z 0 - 1) from dvd_neg.mpr hu)
  · simp

/-- Projective local determinant estimate in a chart whose first coordinate
is a p-adic unit, given the corresponding affine estimate in the chart. -/
theorem projective_chart_det_divisibility {p n s d M N : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (a : Fin (n + 2) → ℤ)
    (hloc : ∀ x : Fin s → Fin (n + 2) → ℤ, (∀ i j, (p : ℤ) ∣ x i j - a j) →
      (∀ i, (p : ℤ) ^ N ∣ eval (x i) (affineChart (n + 2) f)) →
      (p : ℤ) ^ N ∣ (Matrix.of fun i j => eval (x i) (affineChart (n + 2) (F j))).det)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i 0))
    (hres : ∀ i j, (p : ℤ) ∣ z i j.succ - a j * z i 0)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ N ∣ (Matrix.of fun i j => eval (z i) (F j)).det := by
  by_cases hN : N = 0
  · aesop
  have hNpos := Nat.one_le_iff_ne_zero.mpr hN
  let q : ℤ := p ^ N
  have hpq : (p : ℤ) ∣ q := by aesop
  have hex (i : Fin s) := exists_integer_inverse_of_isCoprime
    (show IsCoprime q (z i 0) from (hunit i).pow_left)
  choose u hu huc using hex
  let x : Fin s → Fin (n + 2) → ℤ := fun i j => u i * z i j.succ
  have hx (i : Fin s) (j : Fin (n + 2)) : (p : ℤ) ∣ x i j - a j := by
    have he : x i j - a j =
        u i * (z i j.succ - a j * z i 0) + a j * (u i * z i 0 - 1) := by
      dsimp [x]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (hres i j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s) : q ∣ eval (x i) (affineChart (n + 2) f) := by
    have h := projective_chart_eval_congr (z i) (hu i) f hfhom
    grind
  let A := Matrix.of fun i j : Fin s => eval (x i) (affineChart (n + 2) (F j))
  let D := Matrix.of fun i j : Fin s => u i ^ M * eval (z i) (F j)
  have hA : q ∣ A.det := hloc x hx hxf
  have hAD : q ∣ A.det - D.det := by
    apply Matrix.dvd_det_sub_det_of_dvd_sub
    intro i j
    exact projective_chart_eval_congr (z i) (hu i) (F j) (hF j)
  have hD : q ∣ D.det := by
    simpa using dvd_sub hA hAD
  have hprod : IsCoprime q (∏ i, u i ^ M) :=
    IsCoprime.prod_right fun i _ => (huc i).pow_right
  have he : D.det = (∏ i, u i ^ M) *
      (Matrix.of fun i j => eval (z i) (F j)).det :=
    Matrix.det_mul_column _ _
  rw [he] at hD
  exact hprod.dvd_of_dvd_mul_left hD

section
variable {n : ℕ} (k : Fin (n + 3))

/-- Move coordinate `k` to the first position before taking the affine chart. -/
def projectivePlaneChart (f : MvPolynomial (Fin (n + 3)) ℤ) :
    MvPolynomial (Fin (n + 2)) ℤ :=
  affineChart (n + 2) (rename (Equiv.swap 0 k) f)

lemma eval_swap_plane_coordinates {σ : Type*} [DecidableEq σ] (i k : σ) (z : σ → ℤ)
    (f : MvPolynomial σ ℤ) :
    eval (z ∘ Equiv.swap i k) (rename (Equiv.swap i k) f) = eval z f := by
  rw [eval_rename]
  have he : (z ∘ Equiv.swap i k) ∘ Equiv.swap i k = z := by grind
  rw [he]

end

variable (f : MvPolynomial (Fin 3) ℤ)

