/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Complex.Norm
import CCDN.ForMathlib.MvPolynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Positivity

/-! Coefficient control on the integer grid in every finite dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Iterated one-variable interpolation controls every coefficient from the
values on the full grid, with a constant depending only on degree and dimension. -/
theorem multivariate_coefficient_bound_of_integer_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → |eval (fun i => (a i : ℝ)) f| ≤ H)
    (m : Fin n →₀ ℕ) :
    |f.coeff m| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  classical
  have hlag (s : Finset ℕ) (i k : ℕ) :
      |(∏ j ∈ s, Lagrange.basisDivisor (i : ℝ) (j : ℝ)).coeff k| ≤
        ∏ j ∈ s, ((j : ℝ) + 1) / |(i : ℝ) - j| := by
    induction s using Finset.induction_on generalizing k with
    | empty => by_cases hk : k = 0 <;> simp [Polynomial.coeff_one, hk]
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj]
      let a : ℝ := ((i : ℝ) - j)⁻¹
      let b : ℝ := -a * j
      have he : Lagrange.basisDivisor (i : ℝ) (j : ℝ) =
          Polynomial.C a * Polynomial.X + Polynomial.C b := by
        simp only [Lagrange.basisDivisor, a, b, neg_mul, map_neg, map_mul, sub_eq_add_neg]; ring
      let p := ∏ l ∈ s, Lagrange.basisDivisor (i : ℝ) (l : ℝ)
      let K := ∏ l ∈ s, ((l : ℝ) + 1) / |(i : ℝ) - l|
      have hK : 0 ≤ K := Finset.prod_nonneg fun _ _ => by positivity
      have hmul : |((Polynomial.C a * Polynomial.X + Polynomial.C b) * p).coeff k| ≤
          (|a| + |b|) * K := by
        rw [add_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
        cases k with
        | zero =>
          simp only [Polynomial.coeff_X_mul_zero, mul_zero, zero_add, abs_mul]
          nlinarith [ih 0, abs_nonneg a, abs_nonneg b]
        | succ k =>
          rw [Polynomial.coeff_X_mul]
          have h := (abs_add_le (a * p.coeff k) (b * p.coeff (k + 1))).trans_eq
            (by rw [abs_mul, abs_mul])
          nlinarith [mul_le_mul_of_nonneg_left (ih k) (abs_nonneg a),
            mul_le_mul_of_nonneg_left (ih (k + 1)) (abs_nonneg b)]
      rw [he]
      refine hmul.trans_eq ?_
      simp only [a, b, K, abs_inv, abs_mul, abs_neg, Nat.abs_cast]
      ring
  induction n generalizing H with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    have hh := heval (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rw [eq_C_of_isEmpty f] at hh
    simpa [hm] using hh
  | succ n ih =>
    let g := (finSuccEquiv ℝ n f).coeff (m 0)
    have hg : g.totalDegree ≤ d := by
      by_cases hzero : g = 0
      · simp [hzero]
      · have hh := totalDegree_coeff_finSuccEquiv_add_le f (m 0) hzero
        dsimp only [g]; omega
    have hvalues (a : Fin n → ℕ) (ha : ∀ i, a i ≤ d) :
        |eval (fun i => (a i : ℝ)) g| ≤ ((d : ℝ) + 1) ^ (d + 1) * H := by
      let P := Polynomial.map (eval (fun i => (a i : ℝ))) (finSuccEquiv ℝ n f)
      have hPdeg : P.natDegree ≤ d :=
        Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv f).le.trans
          ((degreeOf_le_totalDegree f 0).trans hd))
      have hPval (x : ℕ) (hx : x ≤ d) : |P.eval (x : ℝ)| ≤ H := by
        dsimp [P]
        rw [← eval_eq_eval_mv_eval',
          show Fin.cons (x : ℝ) (fun i => (a i : ℝ)) =
            (fun i => (((Fin.cons x a : Fin (n + 1) → ℕ) i) : ℝ)) by
            funext i; exact Fin.cases rfl (fun _ => rfl) i]
        exact heval (Fin.cons x a) (fun i => Fin.cases hx ha i)
      have hinj : Set.InjOn (fun i : ℕ => (i : ℝ)) (range (d + 1)) := Nat.cast_injective.injOn
      have hdeg : P.degree < (range (d + 1)).card := by
        rw [card_range, Polynomial.degree_lt_iff_coeff_zero]
        exact fun r hr => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hb (i : ℕ) (hi : i ∈ range (d + 1)) :
          |(Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℝ)) i).coeff (m 0)| ≤
            ((d : ℝ) + 1) ^ d := calc
        _ ≤ ∏ j ∈ (range (d + 1)).erase i, ((j : ℝ) + 1) / |(i : ℝ) - j| :=
          hlag ((range (d + 1)).erase i) i (m 0)
        _ ≤ ∏ _j ∈ (range (d + 1)).erase i, ((d : ℝ) + 1) := by
          gcongr with j hj
          have hj_ne : j ≠ i := (mem_erase.mp hj).1
          have hj_le : (j : ℝ) ≤ d := mod_cast Nat.lt_succ_iff.mp (mem_range.mp (mem_erase.mp hj).2)
          have hij : (1 : ℝ) ≤ |(i : ℝ) - j| := by
            have hne : (i : ℤ) - j ≠ 0 := sub_ne_zero.mpr (mod_cast hj_ne.symm)
            exact_mod_cast Int.one_le_abs hne
          exact (div_le_self (by positivity) hij).trans (by linarith)
        _ = ((d : ℝ) + 1) ^ d := by
          rw [Finset.prod_const, Finset.card_erase_of_mem hi, Finset.card_range, Nat.add_sub_cancel]
      rw [show eval (fun i => (a i : ℝ)) g = P.coeff (m 0) by simp [g, P]]
      conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
      rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
      calc |∑ i ∈ range (d + 1), (Polynomial.C (P.eval (i : ℝ)) *
            Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℝ)) i).coeff (m 0)|
        _ ≤ ∑ i ∈ range (d + 1), |(Polynomial.C (P.eval (i : ℝ)) *
            Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℝ)) i).coeff (m 0)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ range (d + 1), H * ((d : ℝ) + 1) ^ d := Finset.sum_le_sum fun i hi => by
          rw [Polynomial.coeff_C_mul, abs_mul]
          exact mul_le_mul (hPval i (Nat.lt_succ_iff.mp (mem_range.mp hi))) (hb i hi)
            (abs_nonneg _) hH
        _ = ((d : ℝ) + 1) ^ (d + 1) * H := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
          ring
    have hh := ih g hg (by positivity) hvalues m.tail
    rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hh
    convert hh using 1
    rw [show (n + 1) * (d + 1) = n * (d + 1) + (d + 1) by ring, pow_add]; ring

/-- If an integer polynomial of total degree at most `d` has values of absolute value at most
`H` on the grid `{0, …, d}ⁿ`, then every coefficient has absolute value at most
`(d + 1) ^ (n * (d + 1)) * H`. -/
theorem integer_multivariate_coefficient_bound_of_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) →
      |(eval (fun i => (a i : ℤ)) f : ℝ)| ≤ H) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  have hev (a : Fin n → ℕ) :
      eval (fun i => (a i : ℝ)) (map (Int.castRingHom ℝ) f) =
        (eval (fun i => (a i : ℤ)) f : ℝ) := by
    simpa [Function.comp_def] using (map_eval (Int.castRingHom ℝ) (fun i => (a i : ℤ)) f).symm
  simpa [coeff_map] using multivariate_coefficient_bound_of_integer_grid
    (map (Int.castRingHom ℝ) f) ((totalDegree_map_le _ _).trans hd) hH
    (fun a ha => by rw [hev a]; exact heval a ha) m

/-- A nonzero integer polynomial of total degree at most `d` has a point `a` of the grid
`{0, …, d}ⁿ` with `f(a) ≠ 0` such that every coefficient has absolute value at most
`(d + 1) ^ (n * (d + 1)) * |f(a)|`. -/
theorem exists_integer_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧ eval a f ≠ 0 ∧ ∀ m,
      |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * |(eval a f : ℝ)| := by
  classical
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image
    (fun a : Fin n → ℕ => |(eval (fun i => (a i : ℤ)) f : ℝ)|) ⟨fun _ => 0, by simp [S]⟩
  have hb (m) : |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) *
      |(eval (fun i => (a i : ℤ)) f : ℝ)| :=
    integer_multivariate_coefficient_bound_of_grid f hd (abs_nonneg _)
      (fun b hb => hmax b (by simpa [S, Fintype.mem_piFinset, Nat.lt_succ_iff] using hb)) m
  have ha' : ∀ i, a i ≤ d := by
    simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using ha
  refine ⟨fun i => (a i : ℤ), fun i => ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (ha' i)⟩, ?_, hb⟩
  intro hz
  refine hf (MvPolynomial.ext _ _ fun m => ?_)
  have hh := hb m
  rw [hz, Int.cast_zero, abs_zero, mul_zero] at hh
  exact_mod_cast abs_nonpos_iff.mp hh

end
end CCDN
