
import proofs.RAFCriticalWindowQuantitative.ApproximationParameters
import proofs.RAFCriticalWindowQuantitative.FiniteEscapeAdapters


namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval
open scoped ENNReal

variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) (ε : ℚ) (hε : 0 < ε)



variable (a : I) (ha : rationalParameter q hq.le hq1 ≤ a)



include ha in
theorem uniform_error_of_bound  
    (e S : ENNReal) (hS : S ≠ ∞)
    (h : e ≤ S+(precisionIndex ε : ENNReal)⁻¹+
      (actualBinaryWords L).card*(1-toNNReal a^(L+1))^
        (recordIndex q hq hq1 L ε hε)) :
    e.toReal ≤ S.toReal+ε/2 := by
  have hm : 0 < precisionIndex ε := by have := precisionIndex_ge_two ε; omega
  have hp0 : (toNNReal a : ENNReal)^(L+1) ≤ 1 :=
    pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  have ht := (ENNReal.toReal_mono (by finiteness) h).trans
    (ENNReal.toReal_add_le.trans (add_le_add ENNReal.toReal_add_le le_rfl))
  simp_all
  have hp := Rat.cast_le (K := ℝ).mpr (show 1 / _ ≤ ε / 4 from by
    apply (div_le_iff₀ (by exact_mod_cast hm : (0 : ℚ) < precisionIndex ε)).mpr
    have hc := (div_le_iff₀ hε).mp (Nat.le_ceil (4/ε))
    dsimp [precisionIndex]
    push_cast
    nlinarith)

  push_cast at hp
  have hr := (show ((actualBinaryWords L).card : ℝ)*(1-(a:ℝ)^(L+1))^(recordIndex q hq hq1 L ε hε) ≤ (ε:ℝ)/4 from by
    have h := Rat.cast_le (K := ℝ).mpr (recordIndex_error q hq hq1 L ε hε).2
    push_cast at h
    refine le_trans ?_ h
    have hb : 0 ≤ 1-(a:ℝ)^(L+1) := sub_nonneg.mpr (pow_le_one₀ a.property.1 a.property.2)
    gcongr
    · exact_mod_cast (actualBinaryWords_card L).le.trans (Nat.sub_le _ _)
    · exact ha)


  simp_all
  linarith

theorem certified_interval_of_error (e ε : ℚ) (hε : 0 < ε) (S : ℝ)
    (hl : S ≤ e) (hu : e ≤ S+ε/2) :
    (e-ε/2 : ℚ) ≤ S ∧ S ≤ e ∧ e-(e-ε/2) < ε := by
  simp_all

end RAFCriticalWindowQuantitative
