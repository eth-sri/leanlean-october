module

public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters
public import proofs.RAFCriticalWindowQuantitative.FiniteEscapeAdapters

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

theorem real_truncation_error (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (L : ℕ) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a)
    (e S : ENNReal) (hS : S ≠ ∞)
    (h : e ≤ S + (precisionIndex ε : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ (recordIndex q hq hq1 L ε hε)) :
    e.toReal ≤ S.toReal + (ε : ℝ) / 2 := by
  let m := precisionIndex ε
  let r := recordIndex q hq hq1 L ε hε
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hp : (toNNReal a : ENNReal) ^ (L + 1) ≤ 1 := pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  have ht : ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r ≠ ∞ := by finiteness
  have hi : (m : ENNReal)⁻¹ ≠ ∞ := by simp [hm0]
  have hsum : S + (m : ENNReal)⁻¹ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hS, hi⟩
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsum, ht⟩) h
  rw [ENNReal.toReal_add hsum ht, ENNReal.toReal_add hS hi, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hp (by simp), ENNReal.toReal_inv] at hreal
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_toNNReal] at hreal
  have hpm : (m : ℝ)⁻¹ ≤ (ε : ℝ) / 4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast; simpa [one_div] using hcast
  have hrec := (Rat.cast_le (K := ℝ)).mpr (recordIndex_error q hq hq1 L ε hε).2
  push_cast at hrec
  have hcR : ((actualBinaryWords L).card : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (actualBinaryWords_card L ▸ Nat.sub_le (2 ^ (L + 1)) 2)
  have hqa : (q : ℝ) ≤ a := ha
  have hpow := pow_le_pow_left₀ (by exact_mod_cast hq.le) hqa (L + 1)
  have hnonneg : (0 : ℝ) ≤ 1 - (a : ℝ) ^ (L + 1) := sub_nonneg.mpr (pow_le_one₀ a.property.1 a.property.2)
  have hrb : ((actualBinaryWords L).card : ℝ) * (1 - (a : ℝ) ^ (L + 1)) ^ r ≤ (ε : ℝ) / 4 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg (sub_le_sub_left hpow 1) _) (Nat.cast_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right hcR (pow_nonneg (by exact_mod_cast (repair_ratio q hq hq1 L).1) _)).trans hrec)
  linarith

end RAFCriticalWindowQuantitative
