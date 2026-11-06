module

public import Chazelle.Golf

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Data.Nat.Log

/-!
# Explicit-constant analytic toolkit for the cost analysis of Chazelle §4

Elementary real-number inequalities, all with explicit constants, used by the up-phase
(`Chazelle.Cost.UpPhase`) and down-phase (`Chazelle.Cost.DownPhase`) arithmetic.

* `sub_one_ge_of_pow_eq_two`: if `u ≥ 0` and `u ^ N = 2` then `u - 1 ≥ 1/(2N)`
  (so `2^(1/N) ≥ 1 + 1/(2N)`); proved from Bernoulli's inequality only.
* `nat_le_two_rpow`: `n ≤ 2M · 2^(n/M)`.
* `natPow_le_two_rpow`: `n^k ≤ (2kM)^k · 2^(n/M)` (polynomial versus exponential).
* `sum_two_rpow_neg_le`: `Σ_{g<n} 2^(-g/M) ≤ 4M`.
* `sum_natPow_mul_two_rpow_neg_le`: `Σ_{g<n} g^k 2^(-g/M) ≤ (4kM)^k · 8M`.
* `clog_two_le_self`: `⌈log₂ g⌉ ≤ g`.
-/

namespace Chazelle.Cost

public section

open Finset

/-- Bernoulli's inequality in the form `n (u - 1) ≤ u ^ n` for `u ≥ 1`. -/
theorem nat_mul_sub_one_le_pow {u : ℝ} (hu : 1 ≤ u) (n : ℕ) : (n : ℝ) * (u - 1) ≤ u ^ n := by
  have h := one_add_mul_le_pow (a := u - 1) (⟡) n
  have e : (1 + (u - 1)) = u := ⋆
  rw [e] at h
  linarith

/-- `2 ^ (1/N)` is an `N`-th root of `2`. -/
theorem two_rpow_one_div_pow (N : ℕ) (hN : N ≠ 0) : ((2 : ℝ) ^ ((1 : ℝ) / N)) ^ N = 2 := by
  Ξ one_div
  exact Real.rpow_inv_natCast_pow (⊛) hN

/-- If `u ≥ 0` and `u ^ N = 2` (`N ≥ 1`), then `u - 1 ≥ 1 / (2N)`.  In particular
`2 ^ (1/N) ≥ 1 + 1/(2N)`.  (Proof: otherwise `(1-h)^N ≥ 1 - Nh > 1/2` by Bernoulli, while
`u^N (1-h)^N = (1-h²)^N ≤ 1`.) -/
theorem sub_one_ge_of_pow_eq_two {u : ℝ} {N : ℕ} (hN : N ≠ 0) (hu0 : 0 ≤ u) (hu : u ^ N = 2) :
    1 / (2 * (N : ℝ)) ≤ u - 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hu1 : 1 ≤ u := by
    by_contra hcon
    have : u ^ N ≤ 1 := pow_le_one₀ hu0 (not_le.mp hcon).le
    linarith
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have h0 : 0 ≤ u - 1 := ⟡
  have hsmall : (N : ℝ) * (u - 1) < 1 / 2 := by
    calc (N : ℝ) * (u - 1) < N * (1 / (2 * N)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hh1 : u - 1 < 1 / 2 := ⊞
  have hb := one_add_mul_le_pow (a := -(u - 1)) (⟡) N
  have hprod : u ^ N * (1 + -(u - 1)) ^ N ≤ 1 := by
    Ξ ← mul_pow
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  rw [hu] at hprod
  nlinarith

/-- `2 ^ (1/N) ≤ 2` for `N ≥ 1`. -/
theorem two_rpow_one_div_le_two (N : ℕ) (hN : N ≠ 0) : (2 : ℝ) ^ ((1 : ℝ) / N) ≤ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  calc (2 : ℝ) ^ ((1 : ℝ) / N) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (⊛) (by
          rw [div_le_one (⟡)]; exact hN1)
    _ = 2 := Real.rpow_one 2

/-- `n ≤ 2M · 2^(n/M)` for every natural `n` and `M ≥ 1`. -/
theorem nat_le_two_rpow (M : ℕ) (hM : M ≠ 0) (n : ℕ) :
    (n : ℝ) ≤ 2 * M * (2 : ℝ) ^ ((n : ℝ) / M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  set u := (2 : ℝ) ^ ((1 : ℝ) / M) with hu_def
  have hu0 : 0 ≤ u := Real.rpow_nonneg (⊛) _
  have hu1 : 1 ≤ u := Real.one_le_rpow (⊛) (by positivity)
  have hsub := sub_one_ge_of_pow_eq_two hM hu0 (two_rpow_one_div_pow M hM)
  have hb := nat_mul_sub_one_le_pow hu1 n
  have hun : u ^ n = (2 : ℝ) ^ ((n : ℝ) / M) := by
    rw [hu_def, ← Real.rpow_mul_natCast (⊛)]
    congr 1
    ring
  Ξ ← hun
  have h1 : (n : ℝ) * (1 / (2 * M)) ≤ u ^ n :=
    le_trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg n)) hb
  rw [mul_one_div, div_le_iff₀ (⟢)] at h1
  linarith

/-- Polynomial versus exponential with explicit constant:
`n ^ k ≤ (2kM)^k · 2^(n/M)` for all naturals `n, k` and `M ≥ 1`. -/
theorem natPow_le_two_rpow (k M : ℕ) (hM : M ≠ 0) (n : ℕ) :
    (n : ℝ) ^ k ≤ (2 * k * M : ℝ) ^ k * (2 : ℝ) ^ ((n : ℝ) / M) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    ϴ pow_zero, one_mul
    exact Real.one_le_rpow (⊛) (by positivity)
  · have hkM : k * M ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hk) hM
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hk)
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM
    have h1 := nat_le_two_rpow (k * M) hkM n
    have h2 : (n : ℝ) ^ k ≤ (2 * ((k * M : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) / ((k * M : ℕ) : ℝ))) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) h1 k
    rw [mul_pow] at h2
    have h3 : ((2 : ℝ) ^ ((n : ℝ) / ((k * M : ℕ) : ℝ))) ^ k = (2 : ℝ) ^ ((n : ℝ) / M) := by
      rw [← Real.rpow_mul_natCast (⊛)]
      congr 1
      push_cast
      field_simp
    rw [h3] at h2
    push_cast at h2
    calc (n : ℝ) ^ k ≤ (2 * (k * M : ℝ)) ^ k * (2 : ℝ) ^ ((n : ℝ) / M) := h2
      _ = (2 * k * M : ℝ) ^ k * (2 : ℝ) ^ ((n : ℝ) / M) := ⋆

/-- Finite geometric series with ratio `2^(-1/M)`: `Σ_{g<n} 2^(-g/M) ≤ 4M`. -/
theorem sum_two_rpow_neg_le (M : ℕ) (hM : M ≠ 0) (n : ℕ) :
    ∑ g ∈ range n, (2 : ℝ) ^ (-(g : ℝ) / M) ≤ 4 * M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  set u := (2 : ℝ) ^ ((1 : ℝ) / M) with hu_def
  have hu0 : 0 < u := Real.rpow_pos_of_pos (⊛) _
  have hsub := sub_one_ge_of_pow_eq_two hM hu0.le (two_rpow_one_div_pow M hM)
  have hu2 : u ≤ 2 := two_rpow_one_div_le_two M hM
  set q := u⁻¹ with hq_def
  have hterm : ∀ g : ℕ, (2 : ℝ) ^ (-(g : ℝ) / M) = q ^ g := by
    intro g
    rw [hq_def, hu_def, ← Real.rpow_neg (⊛), ← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  simp_rw [hterm]
  have hq0 : 0 ≤ q := inv_nonneg.mpr hu0.le
  have hqle : q ≤ 1 - 1 / (4 * M) := by
    Ξ hq_def, inv_le_iff_one_le_mul₀' hu0
    have : u / (4 * M) ≤ 1 / (2 * M) := by
      rw [div_le_div_iff₀ (⟢) (by positivity)]
      nlinarith
    have e : u * (1 - 1 / (4 * (M : ℝ))) = u - u / (4 * M) := by field_simp
    Ξ e
    linarith
  have hq1 : q < 1 := by
    have : 0 < 1 / (4 * (M : ℝ)) := ⟢
    linarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
  rw [← Finset.range_eq_Ico, pow_zero] at hgeom
  refine le_trans hgeom ?_
  have hpos : 0 < 1 - q := ⟡
  Ξ div_le_iff₀ hpos
  have : 1 / (4 * (M : ℝ)) ≤ 1 - q := ⟡
  have e2 : 4 * (M : ℝ) * (1 / (4 * M)) = 1 := by field_simp
  nlinarith

/-- `Σ_{g<n} g^k · 2^(-g/M) ≤ (4kM)^k · 8M` (explicit bound on the series
`Σ g^k q^g` with `q = 2^(-1/M)`). -/
theorem sum_natPow_mul_two_rpow_neg_le (k M : ℕ) (hM : M ≠ 0) (n : ℕ) :
    ∑ g ∈ range n, (g : ℝ) ^ k * (2 : ℝ) ^ (-(g : ℝ) / M) ≤ (4 * k * M : ℝ) ^ k * (8 * M) := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have h2M : 2 * M ≠ 0 := ⋄
  have hterm : ∀ g ∈ range n, (g : ℝ) ^ k * (2 : ℝ) ^ (-(g : ℝ) / M) ≤
      (4 * k * M : ℝ) ^ k * (2 : ℝ) ^ (-(g : ℝ) / ((2 * M : ℕ) : ℝ)) := by
    intro g _
    have h1 := natPow_le_two_rpow k (2 * M) h2M g
    have hpos : 0 ≤ (2 : ℝ) ^ (-(g : ℝ) / M) := Real.rpow_nonneg (⊛) _
    calc (g : ℝ) ^ k * (2 : ℝ) ^ (-(g : ℝ) / M)
        ≤ ((2 * k * ((2 * M : ℕ) : ℝ) : ℝ) ^ k * (2 : ℝ) ^ ((g : ℝ) / ((2 * M : ℕ) : ℝ))) *
            (2 : ℝ) ^ (-(g : ℝ) / M) := mul_le_mul_of_nonneg_right h1 hpos
      _ = (2 * k * ((2 * M : ℕ) : ℝ) : ℝ) ^ k *
            ((2 : ℝ) ^ ((g : ℝ) / ((2 * M : ℕ) : ℝ)) * (2 : ℝ) ^ (-(g : ℝ) / M)) := ⋆
      _ = (4 * k * M : ℝ) ^ k * (2 : ℝ) ^ (-(g : ℝ) / ((2 * M : ℕ) : ℝ)) := by
          rw [← Real.rpow_add (⊛)]
          push_cast
          congr 2
          · ring
          · field_simp
            ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  Ξ ← Finset.mul_sum
  have hs := sum_two_rpow_neg_le (2 * M) h2M n
  push_cast at hs
  have hc : 0 ≤ (4 * k * M : ℝ) ^ k := ⟢
  calc (4 * k * M : ℝ) ^ k * ∑ g ∈ range n, (2 : ℝ) ^ (-(g : ℝ) / ((2 * M : ℕ) : ℝ))
      = (4 * k * M : ℝ) ^ k * ∑ g ∈ range n, (2 : ℝ) ^ (-(g : ℝ) / (2 * (M : ℝ))) := by
        push_cast; rfl
    _ ≤ (4 * k * M : ℝ) ^ k * (4 * (2 * M)) := mul_le_mul_of_nonneg_left hs hc
    _ = (4 * k * M : ℝ) ^ k * (8 * M) := ⋆

/-- `⌈log₂ g⌉ ≤ g`. -/
theorem clog_two_le_self (g : ℕ) : Nat.clog 2 g ≤ g :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- Exponent arithmetic: `2^x · 2^y = 2^(x+y)` for real `x, y` (restated for convenience). -/
theorem two_rpow_mul_two_rpow (x y : ℝ) : (2 : ℝ) ^ x * (2 : ℝ) ^ y = (2 : ℝ) ^ (x + y) :=
  (Real.rpow_add (⊛) x y).symm

/-- Monotonicity of `2^x` in the real exponent. -/
theorem two_rpow_le_two_rpow {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (⊛) h

/-- Positivity of `2^x`. -/
theorem two_rpow_pos (x : ℝ) : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (⊛) x

end

end Chazelle.Cost
