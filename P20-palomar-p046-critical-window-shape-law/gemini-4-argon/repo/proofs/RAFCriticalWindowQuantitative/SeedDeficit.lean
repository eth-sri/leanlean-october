module

public import proofs.RAFCriticalWindowQuantitative.EffectiveSeed

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval
open scoped ENNReal

def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩

theorem selected_contour_deficit (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    contourBudget a k / (1-contourBudget a k) ≤
      1 / ((m : ENNReal)*(m+1)) := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let k := seedIndex b hb hb1 m
  let h := (molecularContourConstant : ℚ) * (1 - b^2)^k
  have hmR : (0 : ℚ) < m := by exact_mod_cast hm
  have hd : (0 : ℚ) < (m : ℚ) * (m + 1) := by positivity
  have hb0 : 0 ≤ b := hb.le
  have hh0 : (0 : ℚ) ≤ h := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by nlinarith) _)
  have ht2 := (seedIndex_spec b hb hb1 m).2
  change h * ((m : ℚ) * (m + 1) + 1) ≤ 1 at ht2
  have hh1 : h < 1 := by nlinarith
  have hdiv : h / (1 - h) ≤ 1 / ((m : ℚ) * (m + 1)) :=
    (div_le_div_iff₀ (sub_pos.mpr hh1) hd).mpr (by nlinarith)
  have hfin : contourBudget a k ≠ ∞ := by unfold contourBudget; finiteness
  have ha : (toNNReal a : ENNReal)^2 ≤ 1 := pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  have hreal : (contourBudget a k).toReal = (molecularContourConstant : ℝ) * (1 - (b : ℝ)^2)^k := by
    rw [contourBudget, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le ha (by simp)]
    simp [a, rationalParameter]
  have he : contourBudget a k < 1 := (ENNReal.toReal_lt_toReal hfin (by simp)).mp <| by
    rw [hreal, ENNReal.toReal_one]; exact_mod_cast hh1
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hfin (ne_of_gt (tsub_pos_iff_lt.mpr he))) (by finiteness)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le he.le (by simp), hreal]
  simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hcast := (Rat.cast_le (K := ℝ)).mpr hdiv
  push_cast [h] at hcast; exact hcast

end RAFCriticalWindowQuantitative
