/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Complex.Norm
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.GridInterpolation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-! Control the coefficients by iterating univariate interpolation over the integer box. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {n : ℕ} (f : MvPolynomial (Fin n) ℝ) {d : ℕ} (hd : f.totalDegree ≤ d)

include hd in
/-- Coefficients from values on a grid, one variable at a time. -/
theorem multivariate_coefficient_bound_of_integer_grid
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → ‖eval (fun i => (a i : ℝ)) f‖ ≤ H)
    (m : Fin n →₀ ℕ) :
    ‖f.coeff m‖ ≤ (d+1 : ℝ) ^ (n * (d+1)) * H := by
  induction n generalizing H with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    aesop
  | succ n ih =>
    let g := (finSuccEquiv ℝ n f).coeff (m 0)
    have hg : g.totalDegree ≤ d := by
      by_cases hzero : g = 0
      simp_all
      · have hh := totalDegree_coeff_finSuccEquiv_add_le f (m 0) hzero
        linarith
    have hvalues (a : Fin n → ℕ) (ha : ∀ i, a i ≤ d)  := by
      have hh := polynomial_grid_coefficient_bound
        (Polynomial.map (eval (fun i => (a i))) (finSuccEquiv ℝ n f))
        (Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv f).le.trans
          ((degreeOf_le_totalDegree f 0).trans hd))) hH
        (fun x hx => ?_) (m 0)
      · simpa only [g, Polynomial.coeff_map] using hh
      · rw [← eval_eq_eval_mv_eval']
        have hcons : (Fin.cons (x : ℝ) (fun i => (a i : ℝ))) =
            (fun i => (((Fin.cons x a : Fin (n + 1) → ℕ) i) : ℝ)) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [hcons]
        exact heval (Fin.cons x a) (fun i => Fin.cases hx ha i)
    have hh := ih g hg (by positivity) hvalues m.tail
    rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hh
    convert hh using 1
    ring

end

variable {n : ℕ} (f : IntegerPolynomial n)

/-- If an integer polynomial of total degree at most `d` has values of absolute value at most
`H` on the grid `{0, …, d}ⁿ`, then every coefficient has absolute value at most
`(d + 1) ^ (n * (d + 1)) * H`. -/
theorem integer_multivariate_coefficient_bound_of_grid {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) →
      |(eval (fun i => (a i : ℤ)) f : ℝ)| ≤ H) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  simpa only [coeff_map, eq_intCast, Real.norm_eq_abs] using multivariate_coefficient_bound_of_integer_grid (map (Int.castRingHom ℝ) f)
    ((totalDegree_map_le _ _).trans hd) hH (fun a ha => by
      have he := map_eval (Int.castRingHom ℝ) (fun i => (a i : ℤ)) f
      rw [← show (Int.castRingHom ℝ) (eval (fun i => (a i : ℤ)) f) = eval (fun i => (a i : ℝ)) (map (Int.castRingHom ℝ) f) by simpa [Function.comp_def] using he]
      exact heval a ha) m

/-- Take a grid point where the absolute value is largest. -/
theorem exists_integer_multivariate_grid_height_witness (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧ eval a f ≠ 0 ∧ ∀ m,
      |(f.coeff m : ℝ)| ≤ (d+1 : ℝ) ^ (n*(d+1)) * |(eval a f : ℝ)| := by
  classical
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range (d+1))
  have hS : S.Nonempty := ⟨fun _ => 0, by simp [S]⟩
  obtain ⟨a,ha,hm⟩ := S.exists_max_image (fun a => |(eval (fun i => (a i : ℤ)) f : ℝ)|) hS
  have hb := integer_multivariate_coefficient_bound_of_grid f hd (abs_nonneg _) (fun x hx => hm x (by simpa [S] using hx))
  refine ⟨fun i => a i, fun i => ⟨Int.natCast_nonneg _, ?_⟩, ?_, hb⟩
  · simpa [S] using (Fintype.mem_piFinset.mp ha i)
  · intro hz
    refine hf (MvPolynomial.ext _ _ fun m => ?_)
    have hh := hb m
    simpa [hz] using hh

end
end CCDN
