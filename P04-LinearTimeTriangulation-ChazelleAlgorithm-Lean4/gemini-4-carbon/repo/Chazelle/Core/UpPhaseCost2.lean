module

public import Chazelle.Core.UpPhaseCost

/-!
# WP-J up phase: the cost of all grades is linear

`upT_le`: `Σ_{g ≤ p} gT g ≤ K n`.  Grade `g` has `(n - 2)/2^g + 1` chains of cost
`≤ K₁ 2^g 2^(-g/76)` each (`stepB_le`), so it costs `≤ K₁ (n 2^(-g/76) + 2 · 2^g) + O(g)`; the
geometric series give `O(n)` (`2^p ≤ 2 n`).
-/

namespace Chazelle.Core.Up

open Chazelle.Cost

@[expose] public section

section proofs

theorem sum_pow_two (m : ℕ) : ∑ g ∈ Finset.range m, 2 ^ g + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem K1_nonneg (κB κL : ℕ) (κG : ℕ → ℕ) (κO : ℕ) : 0 ≤ K1 κB κL κG κO := by
  unfold K1; positivity

/-- **The cost of grade `g`.** -/
theorem gT_le (κB κL : ℕ) (κG : ℕ → ℕ) (κO n g : ℕ) :
    (gT κB κL κG κO n g : ℝ) ≤
      K1 κB κL κG κO * ((n : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 76) + 2 * (2 : ℝ) ^ g) +
        (17 * g + 100) := by
  set S := stepB κB κL κG κO g with hS
  set cnt := gradeCount n g with hcnt
  have h1 : gT κB κL κG κO n g ≤ (cnt + 1) * (S + 19) + 17 * g + 100 := by
    have e : (cnt + 1) * (S + 19) = cnt * (S + 19) + S + 19 := by ring
    have e2 : stepB κB κL κG κO g = S := hS.symm
    have e3 : gradeCount n g = cnt := hcnt.symm
    unfold gT gradeC; rw [e2, e3]; omega
  have h1' : (gT κB κL κG κO n g : ℝ) ≤ ((cnt : ℝ) + 1) * ((S : ℝ) + 19) + 17 * g + 100 := by
    exact_mod_cast h1
  have hSt := stepB_le κB κL κG κO g
  rw [← hS] at hSt; push_cast at hSt
  have h2g : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have hc : (cnt : ℝ) + 1 ≤ (n : ℝ) / (2 : ℝ) ^ g + 2 := by
    rw [hcnt]; unfold gradeCount
    have : (((n - 2) / 2 ^ g : ℕ) : ℝ) ≤ ((n - 2 : ℕ) : ℝ) / ((2 ^ g : ℕ) : ℝ) := Nat.cast_div_le
    have hn2 : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    push_cast at this ⊢
    have : ((n - 2 : ℕ) : ℝ) / (2 : ℝ) ^ g ≤ (n : ℝ) / (2 : ℝ) ^ g :=
      div_le_div_of_nonneg_right hn2 h2g.le
    linarith
  have hK := K1_nonneg κB κL κG κO
  have hY := Yg_le g
  have hY0 := Yg_pos g
  have hS0 : (0 : ℝ) ≤ (S : ℝ) + 19 := by positivity
  have hc0 : (0 : ℝ) ≤ (cnt : ℝ) + 1 := by positivity
  have e : ((n : ℝ) / (2 : ℝ) ^ g + 2) * Yg g =
      (n : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 76) + 2 * Yg g := by
    unfold Yg; field_simp
  have i1 : ((cnt : ℝ) + 1) * ((S : ℝ) + 19) ≤ ((n : ℝ) / (2 : ℝ) ^ g + 2) * (K1 κB κL κG κO * Yg g) :=
    mul_le_mul hc hSt hS0 (by positivity)
  have i2 : ((n : ℝ) / (2 : ℝ) ^ g + 2) * (K1 κB κL κG κO * Yg g) =
      K1 κB κL κG κO * ((n : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 76) + 2 * Yg g) := by
    rw [← e]; ring
  have i3 : K1 κB κL κG κO * ((n : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 76) + 2 * Yg g) ≤
      K1 κB κL κG κO * ((n : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 76) + 2 * (2 : ℝ) ^ g) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  linarith

/-- **All grades cost `O(n)`.** -/
theorem upT_le_real (κB κL : ℕ) (κG : ℕ → ℕ) (κO n : ℕ) (hn : 2 ≤ n) :
    (upT κB κL κG κO n : ℝ) ≤ (312 * K1 κB κL κG κO + 3200) * n := by
  set p := topGrade n with hp
  set K := K1 κB κL κG κO with hK
  have hK0 : 0 ≤ K := K1_nonneg κB κL κG κO
  unfold upT
  rw [← hp]
  push_cast
  have hsum : ∑ g ∈ Finset.range (p + 1), (gT κB κL κG κO n g : ℝ) ≤
      K * n * ∑ g ∈ Finset.range (p + 1), (2 : ℝ) ^ (-(g : ℝ) / 76) +
        K * 2 * ∑ g ∈ Finset.range (p + 1), (2 : ℝ) ^ g +
        ∑ g ∈ Finset.range (p + 1), (17 * (g : ℝ) + 100) := by
    calc ∑ g ∈ Finset.range (p + 1), (gT κB κL κG κO n g : ℝ)
        ≤ ∑ g ∈ Finset.range (p + 1), (K * n * (2 : ℝ) ^ (-(g : ℝ) / 76) +
            K * 2 * (2 : ℝ) ^ g + (17 * (g : ℝ) + 100)) :=
          Finset.sum_le_sum fun g _ => by
            have := gT_le κB κL κG κO n g
            have e : K * ((n : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 76) + 2 * (2 : ℝ) ^ g) =
              K * n * (2 : ℝ) ^ (-(g : ℝ) / 76) + K * 2 * (2 : ℝ) ^ g := by ring
            linarith
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.mul_sum]
  have hA : ∑ g ∈ Finset.range (p + 1), (2 : ℝ) ^ (-(g : ℝ) / 76) ≤ 304 := by
    have := sum_two_rpow_neg_le 76 (by norm_num) (p + 1); push_cast at this; linarith
  have hB : ∑ g ∈ Finset.range (p + 1), (2 : ℝ) ^ g ≤ 4 * n := by
    have h1 := sum_pow_two (p + 1)
    have h2 := two_pow_le_of_le_top hn (le_refl (topGrade n))
    rw [← hp] at h2
    have h3 : ∑ g ∈ Finset.range (p + 1), 2 ^ g ≤ 4 * n := by rw [pow_succ] at h1; omega
    exact_mod_cast h3
  have hC : ∑ g ∈ Finset.range (p + 1), (17 * (g : ℝ) + 100) ≤ 3200 * n := by
    have h1 : ∀ g ∈ Finset.range (p + 1), (17 * (g : ℝ) + 100) ≤ 17 * p + 100 := fun g hg => by
      have : g ≤ p := by simp at hg; omega
      have : (g : ℝ) ≤ p := by exact_mod_cast this
      linarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h3 : (p + 1) * (17 * p + 100) ≤ 100 * (p + 3) ^ 2 := by ring_nf; omega
    have h4 := sq_le_two_pow p
    have h5 := two_pow_le_of_le_top hn (le_refl (topGrade n))
    rw [← hp] at h5
    have h6 : (p + 1) * (17 * p + 100) ≤ 3200 * n := by omega
    have h7 : ((p + 1 : ℕ) : ℝ) * (17 * (p : ℝ) + 100) ≤ 3200 * n := by exact_mod_cast h6
    push_cast at h7 h2
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have i1 := mul_le_mul_of_nonneg_left hA (show 0 ≤ K * (n : ℝ) by positivity)
  have i2 : K * 2 * ∑ g ∈ Finset.range (p + 1), (2 : ℝ) ^ g ≤ 8 * (K * n) := by
    have := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * 2 by positivity)
    have e : K * 2 * (4 * (n : ℝ)) = 8 * (K * n) := by ring
    linarith
  have e3 : (312 * K + 3200) * (n : ℝ) = 312 * (K * n) + 3200 * n := by ring
  linarith

/-- **All grades cost `O(n)`** (natural-number form). -/
theorem upT_le (κB κL : ℕ) (κG : ℕ → ℕ) (κO : ℕ) :
    ∃ K : ℕ, ∀ n, 2 ≤ n → upT κB κL κG κO n ≤ K * n := by
  refine ⟨⌈312 * K1 κB κL κG κO + 3200⌉₊, fun n hn => ?_⟩
  have h := upT_le_real κB κL κG κO n hn
  have h2 : (312 * K1 κB κL κG κO + 3200) * (n : ℝ) ≤ (⌈312 * K1 κB κL κG κO + 3200⌉₊ : ℝ) * n :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg n)
  exact_mod_cast h.trans h2

end proofs

end

end Chazelle.Core.Up
