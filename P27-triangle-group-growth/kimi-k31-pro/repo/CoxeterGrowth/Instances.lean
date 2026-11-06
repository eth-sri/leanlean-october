module
public import CoxeterGrowth.Triangle
public import CoxeterGrowth.Plastic

@[expose] public section
/-!
# Instances of the triangle growth series

* closed forms for `(2,3,∞)`, `(2,4,∞)`, `(3,3,∞)`;
* for `(2,3,∞)`: the sphere sizes `1, 3, 5, 7, 9`, the recursion `a(n+5) = a(n+3) + a(n+2)`
  (which fails at `n = 4`), the Padovan identification `a(n) = Pad(n+5)` for `n ≥ 2`, the
  two-sided bound `2ρⁿ ≤ a(n) ≤ 4ρⁿ` (`n ≥ 2`) and `a(n)^{1/n} → ρ`, `ρ` the plastic number.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries Filter Topology

/-- The Coxeter matrix of type `(p, q, ∞)` on `Fin 3` (`∞` encoded as `0`). -/
def triM (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : CoxeterMatrix (Fin 3) where
  M := !![1, 0, p; 0, 1, q; p, q, 1]
  isSymm := Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
  diagonal i := by fin_cases i <;> rfl
  off_diagonal i i' h := by
    fin_cases i <;> fin_cases i' <;> simp_all <;> omega

/-- Non-vacuity: the hypotheses of `growth_series` are satisfiable for all `p, q ≥ 2`. -/
theorem triM_exists (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∃ M : CoxeterMatrix (Fin 3), M 0 1 = 0 ∧ M 0 2 = p ∧ M 1 2 = q :=
  ⟨triM p q hp hq, rfl, rfl, rfl⟩

section Closed

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

/-- Sphere sizes `a(n) = #{w : ℓ(w) = n}`. -/
noncomputable def sphere (n : ℕ) : ℕ := Nat.card {w : W // cs.length w = n}

/-- `(2,3,∞)`: `Σ a(n) tⁿ · (1 − t² − t³) = (1+t)²(1+t+t²)`. -/
theorem growth_series_23 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) * (1 - X ^ 2 - X ^ 3) =
      (1 + X) ^ 2 * (1 + X + X ^ 2) := by
  have h := growth_series cs le_rfl (by norm_num) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h
  linear_combination h

/-- `(2,4,∞)`: `Σ a(n) tⁿ · (1 − t² − t³ − t⁴) = (1+t)²(1+t+t²+t³)`. -/
theorem growth_series_24 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  have h := growth_series cs le_rfl (by norm_num) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h
  linear_combination h

/-- `(3,3,∞)`: `Σ a(n) tⁿ · (1 − t² − 2t³ − t⁴) = (1+t)(1+t+t²)²`. -/
theorem growth_series_33 (h01 : M 0 1 = 0) (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  have h := growth_series cs (by norm_num) (by norm_num) h01 h02 h12
  simp [sum_Ico_eq_sum_range, sum_range_succ] at h
  linear_combination h

/-- Coefficient extraction for `(2,3,∞)`. -/
theorem sphere23_facts (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Nat.card {w : W // cs.length w = 0} = 1 ∧ Nat.card {w : W // cs.length w = 1} = 3 ∧
      Nat.card {w : W // cs.length w = 2} = 5 ∧ Nat.card {w : W // cs.length w = 3} = 7 ∧
      Nat.card {w : W // cs.length w = 4} = 9 ∧
      ∀ n : ℕ, Nat.card {w : W // cs.length w = n + 5} =
        Nat.card {w : W // cs.length w = n + 3} + Nat.card {w : W // cs.length w = n + 2} := by
  have H := growth_series_23 cs h01 h02 h12
  ring_nf at H
  have c (n : ℕ) := congrArg (coeff n) H
  simp [coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X] at c
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  have c4 := c 4
  norm_num at c1 c2 c3 c4
  refine ⟨by simp, by exact_mod_cast c1, by omega, by omega, by omega, fun n => ?_⟩
  have cn := c (n + 5)
  norm_num at cn
  omega

theorem sphere23_rec_fails_at_4 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    Nat.card {w : W // cs.length w = 4} ≠
      Nat.card {w : W // cs.length w = 2} + Nat.card {w : W // cs.length w = 1} := by
  obtain ⟨-, h1, h2, -, h4, -⟩ := sphere23_facts cs h01 h02 h12
  omega

end Closed

/-! ## Padovan -/

/-- **Padovan**: for `(2,3,∞)`, `a(n) = Pad(n+5)` for `n ≥ 2`. -/
theorem sphere23_padovan {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {w : W // cs.length w = n} = pad (n + 5) := by
  obtain ⟨-, -, h2, h3, h4, hrec⟩ := sphere23_facts cs h01 h02 h12
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | _ | _ | m
    · omega
    · omega
    · rw [h2]
      norm_num [hpr, hp0, hp1, hp2]
    · rw [h3]
      norm_num [hpr, hp0, hp1, hp2]
    · rw [h4]
      norm_num [hpr, hp0, hp1, hp2]
    · rw [hrec, hpr (m + 7), ih (m + 3) (by omega) (by omega),
        ih (m + 2) (by omega) (by omega)]

/-! ## Exponential growth rate -/

theorem rho_bounds {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) :
    (1.32 : ℝ) < ρ ∧ ρ < 1.33 := by
  constructor
  · by_contra hle
    rw [not_lt] at hle
    have hq : (0:ℝ) ≤ ρ ^ 2 + 1.32 * ρ + 0.7424 := by nlinarith [sq_nonneg ρ]
    nlinarith [mul_nonneg (sub_nonneg.2 hle) hq]
  · by_contra hle
    rw [not_lt] at hle
    have hq : (0:ℝ) ≤ ρ ^ 2 + 1.33 * ρ + 0.7689 := by nlinarith [sq_nonneg ρ]
    nlinarith [mul_nonneg (sub_nonneg.2 hle) hq]

/-- Two-sided bound for any sequence with the `(2,3,∞)` values and recursion. -/
theorem growth_bounds_of_rec (f : ℕ → ℕ) (h2 : f 2 = 5) (h3' : f 3 = 7) (h4 : f 4 = 9)
    (hrec : ∀ n, f (n + 5) = f (n + 3) + f (n + 2)) {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1)
    (n : ℕ) : 2 * ρ ^ (n + 2) ≤ (f (n + 2) : ℝ) ∧ (f (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  have hb := rho_bounds h1 h3
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · rw [h2]; push_cast
      constructor <;> nlinarith
    · rw [h3']; push_cast
      rw [h3]; constructor <;> nlinarith
    · rw [h4]; push_cast
      have h4' : ρ ^ 4 = ρ ^ 2 + ρ := by
        rw [show ρ ^ 4 = ρ * ρ ^ 3 by ring, h3]; ring
      rw [h4']; constructor <;> nlinarith
    · have ha := ih (m + 1) (by omega)
      have hb := ih m (by omega)
      show 2 * ρ ^ (m + 5) ≤ (f (m + 5) : ℝ) ∧ (f (m + 5) : ℝ) ≤ 4 * ρ ^ (m + 5)
      rw [hrec m]
      push_cast
      have hpow : ρ ^ (m + 5) = ρ ^ (m + 3) + ρ ^ (m + 2) := by
        rw [show ρ ^ (m + 5) = ρ ^ (m + 2) * ρ ^ 3 by ring, h3]; ring
      rw [hpow]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem const_rpow_inv_mul_tendsto {ρ c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹) * ρ) atTop (𝓝 ρ) := by
  have h : Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹)) atTop (𝓝 (c ^ (0 : ℝ))) :=
    tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat (.inl hc.ne')
  simpa using h.mul_const ρ

/-- The root limit from two exponential bounds starting at `n = k`. -/
theorem root_tendsto_of_bounds (f : ℕ → ℕ) {τ c C : ℝ} (hτ : 0 ≤ τ) (hc : 0 < c) (hC : 0 < C)
    (k : ℕ) (hb : ∀ n, c * τ ^ (n + k) ≤ (f (n + k) : ℝ) ∧
      (f (n + k) : ℝ) ≤ C * τ ^ (n + k)) :
    Tendsto (fun n : ℕ => (f n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (const_rpow_inv_mul_tendsto (ρ := τ) hc) (const_rpow_inv_mul_tendsto (ρ := τ) hC) ?_ ?_
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    have hn0 : m + k ≠ 0 := by omega
    calc c ^ (((m + k : ℕ) : ℝ))⁻¹ * τ = (c * τ ^ (m + k)) ^ (((m + k : ℕ) : ℝ))⁻¹ := by
          rw [Real.mul_rpow hc.le (pow_nonneg hτ _), Real.pow_rpow_inv_natCast hτ hn0]
      _ ≤ (f (m + k) : ℝ) ^ (((m + k : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) (hb m).1 (by positivity)
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    have hn0 : m + k ≠ 0 := by omega
    calc (f (m + k) : ℝ) ^ (((m + k : ℕ) : ℝ))⁻¹
        ≤ (C * τ ^ (m + k)) ^ (((m + k : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) (hb m).2 (by positivity)
      _ = C ^ (((m + k : ℕ) : ℝ))⁻¹ * τ := by
          rw [Real.mul_rpow hC.le (pow_nonneg hτ _), Real.pow_rpow_inv_natCast hτ hn0]

section Rate

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

/-- `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for `n ≥ 2`, for every real `ρ > 1` with `ρ³ = ρ + 1`. -/
theorem sphere23_growth (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (Nat.card {w : W // cs.length w = n + 2} : ℝ) ∧
      (Nat.card {w : W // cs.length w = n + 2} : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  obtain ⟨-, -, h2, h3', h4, hrec⟩ := sphere23_facts cs h01 h02 h12
  exact growth_bounds_of_rec (sphere cs) h2 h3' h4 hrec h1 h3 n

/-- `(2,3,∞)`: `a(n)^{1/n} → ρ`. -/
theorem sphere23_root_tendsto (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (ρ : ℝ) (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (Nat.card {w : W // cs.length w = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 ρ) :=
  root_tendsto_of_bounds (sphere cs) (by linarith) (by norm_num) (by norm_num) 2
    (sphere23_growth cs h01 h02 h12 ρ h1 h3)

end Rate

end CoxeterGrowth.Triangle
