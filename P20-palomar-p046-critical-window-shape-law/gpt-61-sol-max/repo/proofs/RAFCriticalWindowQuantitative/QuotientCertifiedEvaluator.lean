
import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
import proofs.RAFCriticalWindowQuantitative.RealErrorBudget


namespace RAFCriticalWindowQuantitative
open RAFReactionQuotient MeasureTheory unitInterval HordijkSteelThreshold Filter RAF.Polymer

variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def quotientEvaluationCap   :=
  let hhalf  := rationalHalf_pos q hq
  let hhalf1  := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

theorem quotient_uniform_approximation  (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (quotientEscapeProbability a (quotientEvaluationCap q hq hq1 ε hε)).toReal ≤
      (quotientSurvival a).toReal + ε/2 := by
  let m := precisionIndex ε
  let L := 10*seedIndex (q/2) (by positivity) (by linarith) m
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  apply uniform_error_of_bound q hq hq1 L ε hε a ha _ _ (measure_ne_top _ _)
  apply (finite_seed_truncation quotientPrefixIndex a L _).trans
  apply add_le_add _ le_rfl
  have h := seed_survival_bound (quotientInfiniteMeasure a) L m hm (by
    intro N hN
    have h := effective_quotient_bulk q hq hq1 m a ha N hN
    rw [← infinite_quotient_restriction_map N a,
      Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply _)
        (Set.toFinite _).measurableSet] at h
    simp only [Set.preimage, Set.mem_ofPred_eq, quotientClosure_restriction] at h
    rw [quotientInfiniteMeasure, Measure.map_apply quotientField_measurable]
    · exact h
    · apply Measurable.setOf
      exact (measurable_of_finite (fun ω : Reaction N → Prop =>
        MassDeficit m (temporaryReactionClosure L (staticOpenReactions ω)))).comp (by fun_prop))
  rw [← quotientSurvival_eq] at h
  rw [quotientInfiniteMeasure,
    Measure.map_apply quotientField_measurable (measurableSet_infinite_seed 2 _)] at h
  exact h



def quotientCertifiedInterval   :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

/-- An executable terminating rational enclosure for the actual quotient survival profile. -/
abbrev quotientCertifiedInterval_correct   := by
  let K := quotientEvaluationCap q hq hq1 ε hε
  let a := rationalParameter q hq.le hq1
  let e := quotientEscapeEval q (K-2)
  have he  :=
    (quotientEscapeEval_correct q hq.le hq1 (K-2)).trans
      (congrArg ENNReal.toReal (quotient_escape_finite a K (recordCap_ge_two _ _)).symm)
  apply certified_interval_of_error e ε hε (quotientSurvival a).toReal
  · rw [he]
    exact ENNReal.toReal_mono (measure_ne_top _ _) ((by
                                                      solve_by_elim [MeasureTheory.measure_mono]))
  · rw [he]
    exact quotient_uniform_approximation q hq hq1 ε hε a le_rfl

end RAFCriticalWindowQuantitative
