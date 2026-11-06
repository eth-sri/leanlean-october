
import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
import proofs.RAFCriticalWindowQuantitative.RealErrorBudget


namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold MeasureTheory unitInterval Filter RAF.Polymer

variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitEvaluationCap   :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

theorem split_uniform_approximation  (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (splitEscapeProbability a (splitEvaluationCap q hq hq1 ε hε)).toReal ≤
      (staticSurvival a).toReal + ε/2 := by
  let m := precisionIndex ε
  let L := 10*seedIndex q hq hq1 m
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  apply uniform_error_of_bound q hq hq1 L ε hε a ha _ _ (measure_ne_top _ _)
  apply (finite_seed_truncation splitPrefixIndex a L _).trans
  apply add_le_add _ le_rfl
  have hbad (N : ℕ) (hN : _)  := by
    apply (static_decreasing_event_mono N ha
      (fun S => MassDeficit m (temporaryReactionClosure L S)) ?_).trans
      (effective_static_bulk q hq hq1 m N hN)
    intro S T hST hT
    exact (Nat.mul_le_mul_left m (Finset.card_le_card (temporaryReactionClosure_mono hST))).trans_lt hT
  have h := seed_survival_bound (infiniteStaticMeasure a) L m hm (by
    intro N hN
    have h := hbad N hN
    change staticReactionMeasure N a _ ≤ _ at h
    rw [← infiniteStatic_restriction_map N a,
      Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet] at h
    exact h)
  rw [infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_infinite_seed 2 _)] at h
  exact h



def splitCertifiedInterval   :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

/-- An executable terminating rational enclosure for the actual split survival profile. -/
abbrev splitCertifiedInterval_correct   := by
  let K := splitEvaluationCap q hq hq1 ε hε
  let a := rationalParameter q hq.le hq1
  let e := splitEscapeEval q (K-2)
  have he  :=
    (splitEscapeEval_correct q hq.le hq1 (K-2)).trans
      (congrArg ENNReal.toReal (split_escape_finite a K (recordCap_ge_two _ _)).symm)
  apply certified_interval_of_error e ε hε (staticSurvival a).toReal
  · rw [he]
    exact ENNReal.toReal_mono (measure_ne_top _ _) ((by
                                                      rw [staticSurvival, infiniteStaticMeasure,
                                                        Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2)]
                                                      apply measure_mono
                                                      intro ω hω
                                                      exact hω K))
  · rw [he]
    exact split_uniform_approximation q hq hq1 ε hε a le_rfl

end RAFCriticalWindowQuantitative
