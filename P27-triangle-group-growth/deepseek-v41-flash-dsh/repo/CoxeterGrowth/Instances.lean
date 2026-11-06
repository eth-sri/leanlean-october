module
public import CoxeterGrowth.Triangle
public import CoxeterGrowth.Analysis

@[expose] public section
/-!
# Instances of the growth series

Closed forms for `(2,3,∞)`, `(2,4,∞)`, `(3,3,∞)`; for `(2,3,∞)`: the sphere sizes `1, 3, 5, 7, 9`,
the recursion `a(n+5) = a(n+3) + a(n+2)` (which fails at `n = 4`), the Padovan identification
`a(n) = Pad(n+5)` for `n ≥ 2`, the two-sided bound `2ρⁿ ≤ a(n) ≤ 4ρⁿ` (`n ≥ 2`) and
`a(n)^{1/n} → ρ`, `ρ` the plastic number.
-/

namespace CoxeterGrowth.Triangle

open Finset PowerSeries Filter Topology

/-- The Coxeter matrix of type `(p, q, ∞)` on `Fin 3` (`∞` encoded as `0`). -/
def triM (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) : CoxeterMatrix (Fin 3) where
  M := !![1, 0, p; 0, 1, q; p, q, 1]
  isSymm := Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
  diagonal i := by fin_cases i <;> rfl
  off_diagonal i i' h := by fin_cases i <;> fin_cases i' <;> simp_all <;> omega

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
  have h := growth_series cs ⟨le_refl 2, by norm_num, h01, h02, h12⟩
  simpa [show (1 : ℤ⟦X⟧) - X ^ 2 - X ^ 3 = 1 - X * (X + X ^ 2) by ring,
    show (1 + X : ℤ⟦X⟧) * (1 + X) = (1 + X) ^ 2 by ring,
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using h

/-- `(2,4,∞)`.** -/
theorem growth_series_24 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 4) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - X ^ 3 - X ^ 4) = (1 + X) ^ 2 * (1 + X + X ^ 2 + X ^ 3) := by
  have h := growth_series cs ⟨le_refl 2, by norm_num, h01, h02, h12⟩
  simpa [show (1 : ℤ⟦X⟧) - X ^ 2 - X ^ 3 - X ^ 4 = 1 - X * (X + X ^ 2 + X ^ 3) by ring,
    show (1 + X : ℤ⟦X⟧) * (1 + X) = (1 + X) ^ 2 by ring,
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using h

/-- `(3,3,∞)`.** -/
theorem growth_series_33 (h01 : M 0 1 = 0) (h02 : M 0 2 = 3) (h12 : M 1 2 = 3) :
    (PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ)) *
        (1 - X ^ 2 - 2 * X ^ 3 - X ^ 4) = (1 + X) * (1 + X + X ^ 2) ^ 2 := by
  have h := growth_series cs ⟨by norm_num, by norm_num, h01, h02, h12⟩
  simpa [show (1 : ℤ⟦X⟧) - X ^ 2 - 2 * X ^ 3 - X ^ 4 = 1 - (X + X ^ 2) * (X + X ^ 2) by ring,
    show (1 + X : ℤ⟦X⟧) * (1 + X + X ^ 2) * (1 + X + X ^ 2) = (1 + X) * (1 + X + X ^ 2) ^ 2
      by ring,
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ] using h

/-- Coefficient extraction for `(2,3,∞)`. -/
theorem sphere23_facts (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    sphere cs 0 = 1 ∧ sphere cs 1 = 3 ∧ sphere cs 2 = 5 ∧ sphere cs 3 = 7 ∧ sphere cs 4 = 9 ∧
      ∀ n, sphere cs (n + 5) = sphere cs (n + 3) + sphere cs (n + 2) := by
  have H := growth_series_23 cs h01 h02 h12
  rw [show (1 + X : ℤ⟦X⟧) ^ 2 * (1 + X + X ^ 2) = 1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4
    by ring, mul_sub, mul_sub, mul_one] at H
  set A : ℤ⟦X⟧ := PowerSeries.mk fun n => (Nat.card {w : W // cs.length w = n} : ℤ) with hA
  have c : ∀ n, coeff n A - coeff n (A * X ^ 2) - coeff n (A * X ^ 3) =
      coeff n (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 : ℤ⟦X⟧) := by
    intro n; rw [← map_sub, ← map_sub, H]
  have h0 := c 0; have h1 := c 1; have h2 := c 2; have h3 := c 3; have h4 := c 4
  norm_num [hA, coeff_mk, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X] at h0 h1 h2 h3 h4
  unfold sphere
  refine ⟨by simp, by omega, by omega, by omega, by omega, fun n => ?_⟩
  have hn := c (n + 5)
  norm_num [hA, coeff_mk, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X,
    show 2 ≤ n + 5 by omega, show 3 ≤ n + 5 by omega, Nat.reduceSub,
    show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega] at hn
  omega

theorem sphere23_rec_fails_at_4 (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3) :
    sphere cs 4 ≠ sphere cs 2 + sphere cs 1 := by
  obtain ⟨-, h1, h2, -, h4, -⟩ := sphere23_facts cs h01 h02 h12
  omega

end Closed

/-! ## Padovan -/

/-- **Padovan**: for `(2,3,∞)`, `a(n) = Pad(n+5)` for `n ≥ 2`, for any sequence `Pad` with the
Padovan initial values and recursion. -/
theorem sphere23_padovan {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)}
    (cs : CoxeterSystem M W) (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    (pad : ℕ → ℕ) (hp0 : pad 0 = 1) (hp1 : pad 1 = 1) (hp2 : pad 2 = 1)
    (hpr : ∀ n, pad (n + 3) = pad (n + 1) + pad n) (n : ℕ) (hn : 2 ≤ n) :
    sphere cs n = pad (n + 5) := by
  obtain ⟨-, -, h2, h3, h4, hrec⟩ := sphere23_facts cs h01 h02 h12
  have key : ∀ n, 2 ≤ n → sphere cs n = pad (n + 5) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases n with _ | _ | _ | _ | _ | k
      · omega
      · omega
      · rw [h2]; simp [hpr, hp0, hp1, hp2]
      · rw [h3]; simp [hpr, hp0, hp1, hp2]
      · rw [h4]; simp [hpr, hp0, hp1, hp2]
      · rw [hrec k, ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega),
          ← hpr (k + 7)]
  exact key n hn

theorem rho_gt {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) : (1.25 : ℝ) < ρ := by
  by_contra hle
  rw [not_lt] at hle
  have hq : (0 : ℝ) ≤ ρ ^ 2 + 1.25 * ρ + 0.5625 := by nlinarith [sq_nonneg ρ]
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hq]

theorem rho_lt {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) : ρ < (1.4 : ℝ) := by
  by_contra hle
  rw [not_lt] at hle
  have hq : (0 : ℝ) ≤ ρ ^ 2 + 1.4 * ρ + 0.96 := by nlinarith [sq_nonneg ρ]
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hq]

/-- Two-sided bound for any sequence with the `(2,3,∞)` values and recursion. -/
theorem growth_bounds_of_rec (f : ℕ → ℕ) (h2 : f 2 = 5) (h3' : f 3 = 7) (h4 : f 4 = 9)
    (hrec : ∀ n, f (n + 5) = f (n + 3) + f (n + 2)) {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1)
    (n : ℕ) : 2 * ρ ^ (n + 2) ≤ (f (n + 2) : ℝ) ∧ (f (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  have hlo := rho_gt h1 h3
  have hhi := rho_lt h1 h3
  have h4' : ρ ^ 4 = ρ ^ 2 + ρ := by rw [show ρ ^ 4 = ρ * ρ ^ 3 by ring, h3]; ring
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | m
    · rw [h2]; push_cast; constructor <;> nlinarith
    · rw [h3']; push_cast; rw [h3]; constructor <;> nlinarith
    · rw [h4]; push_cast; rw [h4']; constructor <;> nlinarith
    · have ha := ih (m + 1) (by omega)
      have hb := ih m (by omega)
      show 2 * ρ ^ (m + 5) ≤ (f (m + 5) : ℝ) ∧ (f (m + 5) : ℝ) ≤ 4 * ρ ^ (m + 5)
      rw [hrec m]
      push_cast
      rw [show ρ ^ (m + 5) = ρ ^ (m + 3) + ρ ^ (m + 2) by
        rw [show ρ ^ (m + 5) = ρ ^ (m + 2) * ρ ^ 3 by ring, h3]; ring]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

section Rate

variable {W : Type*} [Group W] {M : CoxeterMatrix (Fin 3)} (cs : CoxeterSystem M W)

/-- `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ` for `n ≥ 2`, for every real `ρ > 1` with `ρ³ = ρ + 1`. -/
theorem sphere23_growth (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) (n : ℕ) :
    2 * ρ ^ (n + 2) ≤ (sphere cs (n + 2) : ℝ) ∧ (sphere cs (n + 2) : ℝ) ≤ 4 * ρ ^ (n + 2) := by
  obtain ⟨-, -, h2, h3', h4, hrec⟩ := sphere23_facts cs h01 h02 h12
  exact growth_bounds_of_rec (sphere cs) h2 h3' h4 hrec h1 h3 n

/-- `(2,3,∞)`: `a(n)^{1/n} → ρ`. -/
theorem sphere23_root_tendsto (h01 : M 0 1 = 0) (h02 : M 0 2 = 2) (h12 : M 1 2 = 3)
    {ρ : ℝ} (h1 : 1 < ρ) (h3 : ρ ^ 3 = ρ + 1) :
    Tendsto (fun n : ℕ => (sphere cs n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 ρ) := by
  refine CoxeterGrowth.root_tendsto_of_bounds (f := sphere cs) (τ := ρ) (c := 2) (C := 4)
    (by linarith) (by norm_num) (by norm_num) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact (sphere23_growth cs h01 h02 h12 h1 h3 m).1
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact (sphere23_growth cs h01 h02 h12 h1 h3 m).2

end Rate

end CoxeterGrowth.Triangle

