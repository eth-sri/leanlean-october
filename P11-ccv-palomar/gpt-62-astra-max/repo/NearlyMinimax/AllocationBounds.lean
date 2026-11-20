module

public import Mathlib

@[expose] public section

/-!
# Finite factorial-series bounds for the upper allocation

The coefficients in the variance allocation are bounded directly. The finite
series is not replaced by an assumed variance bound. These scalar lemmas supply
the coarse and fine estimates in `upper_E.tex`, `eq:U13-wj` and `eq:U13-fine`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace NearlyMinimax

/-- The variance factorial series, summing `k! x^k` for `1 ≤ k ≤ D`. -/
def factorialSeries (D : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D, (k + 1).factorial * x ^ (k + 1)

theorem factorialSeries_nonneg (D : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ factorialSeries D x := Finset.sum_nonneg fun k hk => by positivity

section
variable {D : ℕ} {x z β B A C₀ C_D S M : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (hDx : (D : ℝ) * x ≤ Real.exp z)
    (_hC : 0 ≤ C₀) (hCS : 0 < C_D * S) (hD : (D : ℝ) ≤ C_D * S) (hDz : (D : ℝ) * z ≤ β * S ^ 2 / 4)

/-- The successive-term ratio is bounded by `1/2` throughout the finite sum. -/
theorem factorial_term_le_geometric {k : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hD : D * x ≤ 1 / 2) (hk : k < D) :
    (k + 1).factorial * x ^ (k + 1) ≤ x * (1 / 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkp : k < D := by omega
    have hratio : (k + 2 : ℕ) * x ≤ 1 / 2 := by
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hx).trans hD
    have hprev := ih hkp
    calc
      _ =
          ((k + 2 : ℕ) * x) * ((k + 1).factorial * x ^ (k + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        ring
      _ ≤ (1 / 2) * (x * (1 / 2) ^ k) :=
        by bound
      _ = _ := by ring

include hx in
/-- The uniform coarse-level estimate in the paper. -/
theorem factorialSeries_coarse_bound (hD : D * x ≤ 1 / 2) :
    factorialSeries D x ≤ 2 * x := by
  have hg : (∑ k ∈ Finset.range D, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := D)
      (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
    convert h using 1 <;> norm_num
  calc
    _ ≤ ∑ k ∈ Finset.range D, x * (1 / 2) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      grind [factorial_term_le_geometric]
    _ = _ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hx
    _ = _ := mul_comm _ _

/-- Factorials are bounded by the maximal degree to the corresponding power. -/
theorem factorial_cast_le_degree_pow {k : ℕ} (hk : k ≤ D) :
    k.factorial ≤ (D : ℝ) ^ k := by
  exact_mod_cast ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hk k))

include hx hz hDx in
/-- The finite fine-level estimate, prior to replacing `D` by its real upper bound. -/
theorem factorialSeries_fine_bound
    (hDz : D * z ≤ B) (hDA : D ≤ A) :
    factorialSeries D x ≤ A * Real.exp B := by
  calc
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD  := Finset.mem_range.1 hk
      calc
        _ ≤
            _ :=
          mul_le_mul_of_nonneg_right (factorial_cast_le_degree_pow hkD) (by positivity)
        _ = _ := by rw [mul_pow]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hDx (k + 1)
        _ = _ := (Real.exp_nat_mul z (k + 1)).symm
        _ ≤ _ := Real.exp_le_exp.2
          ((mul_le_mul_of_nonneg_right (by exact_mod_cast hkD) hz).trans hDz)
    _ = D * Real.exp B := by simp
    _ ≤ _ := by bound

include hz hCS hD hDz in
/-- Direct substitution of the fine-level allocation's `x = exp z/(C_D S)`. -/
theorem factorialSeries_fine_allocation :
    factorialSeries D (Real.exp z / (C_D * S)) ≤
      C_D * S * Real.exp (β * S ^ 2 / 4) := by
  apply factorialSeries_fine_bound (by positivity) hz _ hDz hD
  have hd := mul_le_mul_of_nonneg_right hD (div_nonneg (Real.exp_pos z).le hCS.le)
  have he : (C_D * S) * (Real.exp z / (C_D * S)) = Real.exp z := by
    grind
  bound

include hz _hC hCS hD hDz in
/-- The fine-level series remains bounded after its sampling weight. -/
theorem factorialSeries_fine_weighted
    (hM : 0 ≤ M) (hMb : M ≤ C₀ * C_D * S) :
    factorialSeries D (Real.exp z / (C_D * S)) * M ≤
      C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  linarith [mul_le_mul (factorialSeries_fine_allocation hz hCS hD hDz) hMb hM (by positivity)]

end

/-- The fixed subtraction in `eq:Udef-S` leaves the quadratic budget reserve. -/
theorem quadratic_allocation_budget {β H t S : ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hdef : S = t - (1 + 2 * H / β)) :
    β * S ^ 2 / 4 + H * S ≤ β * t ^ 2 / 4 := by
  have ht : t = S + (1 + 2 * H / β) := by linarith
  have hid : β * t ^ 2 / 4 - (β * S ^ 2 / 4 + H * S) =
      β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by
    rw [ht]
    field_simp
    ring
  nlinarith

/-- The explicit residual variance upper bound tends to zero. -/
theorem tendsto_allocation_reserve_bound (C₀ C_D : ℝ) :
    Tendsto (fun S => 2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (-2 * S))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 2 (by norm_num)).const_mul
    (2 * C₀ * C_D ^ 2)
  convert h using 1 <;> simp [mul_assoc]

end NearlyMinimax
