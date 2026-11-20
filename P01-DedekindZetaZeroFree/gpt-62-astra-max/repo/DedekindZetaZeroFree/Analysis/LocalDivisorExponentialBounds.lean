module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem exists_local_exponential_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ,
      ((k : ℝ) + 1) ≤ B * (2 : ℝ) ^ (ε * (k : ℝ)) := by
  set r : ℝ := (2 : ℝ) ^ (-ε) with hrdef
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hrlt : r < 1 := by
    rw [hrdef, Real.rpow_neg h2.le]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hε)
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by
      rw [hrdef]; exact Real.rpow_pos_of_pos h2 _)]; exact hrlt
  have hbase := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm
  have hsum : HasSum (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) (1 / (1 - r) ^ 2) := by
    simpa [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using hbase
  refine ⟨max 1 (1 / (1 - r) ^ 2), le_max_left _ _, fun k => ?_⟩
  have hle : ((k : ℝ) + 1) * r ^ k ≤ 1 / (1 - r) ^ 2 := by
    simpa [hsum.tsum_eq] using (hsum.summable.sum_le_tsum {k} (fun i _ => by positivity))
  have hrpow : r ^ k = (2 : ℝ) ^ (-(ε * (k : ℝ))) := by
    rw [hrdef, ← Real.rpow_natCast ((2 : ℝ) ^ (-ε)) k, ← Real.rpow_mul h2.le]
    ring_nf
  have hone : r ^ k * (2 : ℝ) ^ (ε * (k : ℝ)) = 1 := by
    rw [hrpow, ← Real.rpow_add h2]
    rw [neg_add_cancel, Real.rpow_zero]
  calc ((k : ℝ) + 1) = ((k : ℝ) + 1) * (r ^ k * (2 : ℝ) ^ (ε * (k : ℝ))) := by
        rw [hone, mul_one]
    _ = ((k : ℝ) + 1) * r ^ k * (2 : ℝ) ^ (ε * (k : ℝ)) := by ring
    _ ≤ max 1 (1 / (1 - r) ^ 2) * (2 : ℝ) ^ (ε * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (hle.trans (le_max_right _ _)) (Real.rpow_pos_of_pos h2 _).le

theorem local_exponential_bound_of_two_le_rpow (ε : ℝ) (q : ℝ)
    (hq : 1 ≤ q) (hpow : 2 ≤ q ^ ε) (k : ℕ) :
    ((k : ℝ) + 1) ≤ q ^ (ε * (k : ℝ)) := by
  calc _ ≤ (2 : ℝ) ^ k := (by
    have := Nat.succ_le_of_lt k.lt_two_pow_self
    exact_mod_cast this)
    _ = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm
    _ ≤ (q ^ ε) ^ (k : ℝ) := Real.rpow_le_rpow (by norm_num) hpow (Nat.cast_nonneg k)
    _ = q ^ (ε * (k : ℝ)) := (Real.rpow_mul (le_trans zero_le_one hq) ε (k : ℝ)).symm

end DedekindZetaZeroFree.LargeSieve.Vendor
