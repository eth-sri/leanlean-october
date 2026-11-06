module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
public import proofs.RAFCriticalWindowQuantitative.QuotientCertifiedEvaluator

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval

def splitTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

def quotientTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem splitTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := splitTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε := by
  by_cases h : q = 0
  · subst q
    have he : rationalParameter 0 hq hq1 = 0 := Subtype.ext Rat.cast_zero
    have hz : (staticSurvival 0).toReal = 0 :=
      le_antisymm (by simpa only [Set.Icc.coe_zero, pow_one, mul_zero] using split_sparse_real 0 1) ENNReal.toReal_nonneg
    simp [splitTotalInterval, he, hz, hε]
  · have hq' := lt_of_le_of_ne hq (Ne.symm h)
    rw [splitTotalInterval, dite_eq_right h]
    exact certifiedInterval_of_bounds q hq' hq1 ε hε _ _ _ _ (measure_ne_top _ _) (measure_ne_top _ _)
      (explicit_split_truncation q hq' hq1 _ (precisionIndex_ge_two ε) _ le_rfl _)
      ((splitEscapeEval_correct q hq hq1 _).trans
        (congrArg ENNReal.toReal (split_escape_finite _ _ (recordCap_ge_two _ _)).symm))
      (split_survival_le_escape _ _)

theorem quotientTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := quotientTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε := by
  by_cases h : q = 0
  · subst q
    have he : rationalParameter 0 hq hq1 = 0 := Subtype.ext Rat.cast_zero
    have hz : (quotientSurvival 0).toReal = 0 :=
      le_antisymm (by simpa only [Set.Icc.coe_zero, pow_one, mul_zero] using quotient_sparse_real 0 1) ENNReal.toReal_nonneg
    simp [quotientTotalInterval, he, hz, hε]
  · have hq' := lt_of_le_of_ne hq (Ne.symm h)
    rw [quotientTotalInterval, dite_eq_right h]
    exact certifiedInterval_of_bounds q hq' hq1 ε hε _ _ _ _ (measure_ne_top _ _) (measure_ne_top _ _)
      (explicit_quotient_truncation q hq' hq1 _ (precisionIndex_ge_two ε) _ le_rfl _)
      ((quotientEscapeEval_correct q hq hq1 _).trans
        (congrArg ENNReal.toReal (quotient_escape_finite _ _ (recordCap_ge_two _ _)).symm))
      (quotient_survival_le_escape _ _)

end RAFCriticalWindowQuantitative
