module
public import RationalShortRange
public import RationalMomentCover

@[expose] public section

noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem rational_energy_trivial (A : Finset ℚ) (W : Finset ℝ) :
    rationalEnergy A W ≤ (A.card : ℝ)*(W.card : ℝ)^2 := by
  have hphase (r : ℚ) (t : ℝ) : ‖phase r t‖ = 1 := by
    rw [← exponentialPhase_log, exponentialPhase_norm]
  unfold rationalEnergy
  calc
    _ ≤ ∑ _r ∈ A, (W.card : ℝ)^2 := by
      apply sum_le_sum
      intro r _
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sum_le _ _).trans_eq (by simp only [hphase, sum_const, nsmul_eq_mul, mul_one])
    _ = _ := by simp

theorem rational_card_le_height (A : Finset ℚ) (H : ℕ)
    (hA : ∀ r ∈ A, 0 < r ∧ r.den ≤ H ∧ |Real.log (r : ℝ)| ≤ 1) :
    A.card ≤ 3*H*H := by
  have hmaps : Set.MapsTo positiveRatPair (↑A : Set ℚ)
      (↑(Icc 1 (3*H) ×ˢ Icc 1 H) : Set (ℕ × ℕ)) := by
    intro r hr
    have hn : (r.num.natAbs : ℝ) ≤ 3*(H : ℝ) := by
      have hd : (r.den : ℝ) ≤ H := by exact_mod_cast (hA r hr).2.1
      exact (numerator_bound_of_log (hA r hr).1 (hA r hr).2.2).trans
        ((mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Nat.cast_nonneg _)))
    exact mem_product.mpr ⟨mem_Icc.mpr
      ⟨Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (hA r hr).1.ne'), by exact_mod_cast hn⟩,
      mem_Icc.mpr ⟨r.pos, (hA r hr).2.1⟩⟩
  have hinj : Set.InjOn positiveRatPair (↑A : Set ℚ) := by
    intro r hr s hs h
    rw [← positiveRatPair_ratio (hA r hr).1, ← positiveRatPair_ratio (hA s hs).1, h]
  simpa using card_le_card_of_injOn positiveRatPair hmaps hinj

end Montgomery.RationalMoment
