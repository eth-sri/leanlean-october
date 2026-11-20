/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Basic.Real.Basic
import CCDN.ForMathlib.MvPolynomial
import Mathlib.LinearAlgebra.Lagrange

/-! Coefficient control on the integer grid by coordinatewise Lagrange interpolation. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Finset

private lemma lagrange_product_coeff_le (d i : ℕ) (a : ℝ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, |(j : ℝ) - a| ≤ d ∧ j ≠ i) (k : ℕ) :
    |(∏ j ∈ S, Lagrange.basisDivisor ((i : ℝ) - a) ((j : ℝ) - a)).coeff k| ≤ ((d : ℝ) + 1) ^ S.card := by
  induction S using Finset.induction_on generalizing k with
  | empty => by_cases h : k = 0 <;> simp [coeff_one, h]
  | @insert j S hj ih =>
    obtain ⟨hjd, hji⟩ := hS j (mem_insert_self _ _)
    let p := ∏ l ∈ S, Lagrange.basisDivisor ((i : ℝ) - a) ((l : ℝ) - a)
    let H := ((d : ℝ) + 1) ^ S.card
    have hp (k : ℕ) : |p.coeff k| ≤ H := ih (fun l hl => hS l (mem_insert_of_mem hl)) k
    have hH : 0 ≤ H := by positivity
    have hunit : |(((i : ℝ) - a) - ((j : ℝ) - a))⁻¹| ≤ 1 := by
      rw [sub_sub_sub_cancel_right]
      have hk : 1 ≤ |(i : ℝ) - j| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hji.symm : (i : ℤ) ≠ j))
      exact (abs_inv _).trans_le ((inv_le_one₀ (by linarith)).mpr hk)
    have hX : |(X * p).coeff k| ≤ H := by
      cases k with
      | zero => simpa using hH
      | succ k => simpa [coeff_X_mul] using hp k
    rw [prod_insert hj, card_insert_of_notMem hj, pow_succ]
    change |(Lagrange.basisDivisor ((i : ℝ) - a) ((j : ℝ) - a) * p).coeff k| ≤ H * _
    rw [Lagrange.basisDivisor, mul_assoc, sub_mul,
      coeff_C_mul, coeff_sub, coeff_C_mul, abs_mul]
    calc
      _ ≤ 1 * (|(X * p).coeff k| + |((j : ℝ) - a) * p.coeff k|) :=
        mul_le_mul hunit (abs_sub ..) (abs_nonneg _) (by norm_num)
      _ ≤ H * ((d : ℝ) + 1) := by
        rw [one_mul, abs_mul]
        nlinarith only [hX, mul_le_mul hjd (hp k) (abs_nonneg _) (Nat.cast_nonneg (α := ℝ) d)]

/-- Coarse Lagrange coefficient bounds suffice for the logarithmic positioning loss. -/
private theorem polynomial_coefficient_bound_of_integer_grid
    (f : ℝ[X]) {d : ℕ} (hd : f.natDegree ≤ d) {H : ℝ} (hH : 0 ≤ H)
    {a : ℝ} (ha : 0 ≤ a ∧ a ≤ d)
    (heval : ∀ i : ℕ, i ≤ d → |f.eval ((i : ℝ) - a)| ≤ H) (k : ℕ) :
    |f.coeff k| ≤ ((d : ℝ) + 1) ^ (d + 1) * H := by
  let S := range (d + 1)
  have hdeg : f.degree < S.card := by
    rw [show S.card = d + 1 by simp [S]]
    exact (degree_le_of_natDegree_le hd).trans_lt (by exact_mod_cast d.lt_succ_self)
  have hinj : Function.Injective (fun i : ℕ => (i : ℝ) - a) :=
    fun i j h => Nat.cast_injective (show (i : ℝ) = j by linarith)
  have h := Lagrange.eq_interpolate hinj.injOn hdeg
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  rw [show ((d : ℝ) + 1) ^ (d + 1) * H = ∑ _ ∈ S, H * ((d : ℝ) + 1) ^ d by
    simp [S, pow_succ]; ring]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [coeff_C_mul, abs_mul]
  refine mul_le_mul (heval i (by simpa [S] using hi)) ?_ (abs_nonneg _) hH
  have hh := lagrange_product_coeff_le d i a (S.erase i) (fun j hj => ⟨?_, (mem_erase.mp hj).1⟩) k
  · simpa [Lagrange.basis, card_erase_of_mem hi, S] using hh
  · have hj' : j ≤ d := by simpa [S] using mem_of_mem_erase hj
    have hjR : (j : ℝ) ≤ d := by exact_mod_cast hj'
    exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) j, ha.2], by linarith [ha.1]⟩

open MvPolynomial

section

variable {n : ℕ}
  (f : MvPolynomial (Fin n) ℝ) {d : ℕ} (hd : f.totalDegree ≤ d)
include n f d hd

/-- Iterate interpolation over the coordinates of a shifted integer grid. -/
theorem multivariate_coefficient_bound_of_shifted_grid
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ v : Fin n → ℕ, (∀ i, v i ≤ d) → |eval (fun i => (v i : ℝ) - a i) f| ≤ H)
    (m : Fin n →₀ ℕ) :
    |f.coeff m| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  induction n generalizing H with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    have h := heval (fun _ => 0) (fun i => Fin.elim0 i)
    have he : (fun i : Fin 0 => ((0 : ℕ) : ℝ) - a i) = 0 := Subsingleton.elim _ _
    simpa only [he, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, hm, Nat.zero_mul, pow_zero, one_mul] using h
  | succ n ih =>
    let g := (finSuccEquiv ℝ n f).coeff (m 0)
    have hg : g.totalDegree ≤ d := by
      by_cases hzero : g = 0
      simp_all
      · have hh := totalDegree_coeff_finSuccEquiv_add_le f (m 0) hzero
        linarith
    have hvalues (v : Fin n → ℕ) (hv : ∀ i, v i ≤ d) :
        |eval (fun i => (v i : ℝ) - a i.succ) g| ≤ ((d : ℝ) + 1) ^ (d + 1) * H := by
      have hh := polynomial_coefficient_bound_of_integer_grid
        (Polynomial.map (eval (fun i => (v i : ℝ) - a i.succ)) (finSuccEquiv ℝ n f))
        (Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv f).le.trans
          ((degreeOf_le_totalDegree f 0).trans hd))) hH (ha 0)
        (fun x hx => ?_) (m 0)
      · simpa [g, Polynomial.coeff_map] using hh
      · rw [← eval_eq_eval_mv_eval']
        convert heval (Fin.cons x v) (Fin.cases hx hv) using 3
        congr 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
    have hh := ih g hg (a ∘ Fin.succ) (fun i => ha _) (show 0 ≤ ((d : ℝ) + 1) ^ (d + 1) * H by positivity) hvalues m.tail
    rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hh
    convert hh using 1
    ring

end

/-- The shifted grid bound for integer coefficients, measured in `ℝ`. -/
theorem integer_multivariate_coefficient_bound_of_shifted_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {d : ℕ} (hd : f.totalDegree ≤ d)
    (a : Fin n → ℤ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ v : Fin n → ℕ, (∀ i, v i ≤ d) →
      |(eval (fun i => (v i : ℤ) - a i) f : ℝ)| ≤ H) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  have h := multivariate_coefficient_bound_of_shifted_grid
    (map (Int.castRingHom ℝ) f) ((totalDegree_map_le _ _).trans hd)
    (fun i => (a i : ℝ)) (fun i => by exact_mod_cast ha i) hH (fun v hv => ?_) m
  · simpa [MvPolynomial.coeff_map] using h
  · rw [show (fun i => (v i : ℝ) - (a i : ℝ)) =
      Int.castRingHom ℝ ∘ (fun i => (v i : ℤ) - a i) by simp [Function.comp_def], ← map_eval]
    exact heval v hv

/-- A nonzero polynomial of degree at most `d` attains a nonzero maximum on the grid. -/
theorem exists_integer_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧ eval a f ≠ 0 ∧
      ∀ v : Fin n → ℕ, (∀ i, v i ≤ d) → |(eval (fun i => (v i : ℤ)) f : ℝ)| ≤ |(eval a f : ℝ)| := by
  classical
  let value (a : Fin n → ℕ) := |(eval (fun i => (a i : ℤ)) f : ℝ)|
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))
  have hS (a) : a ∈ S ↔ ∀ i, a i ≤ d := by simp [S]
  obtain ⟨a, ha, hm⟩ := S.exists_max_image value ⟨fun _ => 0, (hS _).mpr (by simp)⟩
  have hm' : ∀ v : Fin n → ℕ, (∀ i, v i ≤ d) → value v ≤ value a :=
    fun v hv => hm v ((hS v).mpr hv)
  refine ⟨fun i => (a i : ℤ), fun i => ⟨by positivity, by simpa using (hS a).mp ha i⟩, ?_, hm'⟩
  intro hz
  apply hf (MvPolynomial.ext _ _ fun m => ?_)
  have h := integer_multivariate_coefficient_bound_of_shifted_grid f hd 0 (by simp)
    (abs_nonneg (eval (fun i => (a i : ℤ)) f : ℝ)) (by simpa [value] using hm') m
  simp [hz] at h
  exact h

end
end CCDN
