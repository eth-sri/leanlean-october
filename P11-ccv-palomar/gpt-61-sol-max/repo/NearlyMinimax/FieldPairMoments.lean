module

public import NearlyMinimax.TwoStagePairRisk

@[expose] public section

/-! Actual joint second moments and means of the two-stage pair statistic. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {P Ω E : Type*} [MeasurableSpace P] [MeasurableSpace Ω] [MeasurableSpace E]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem fieldWeightedSymmetrization_memLp weight {G : P → E × E → ℝ}
    (hG : MemLp (fun z  => G z.1 z.2) 2 (π.prod (μ.prod μ))) :
    MemLp (fun z  => weightedSymmetrization weight (G z.1) z.2)
      2 (π.prod (μ.prod μ)) := by
  have hs : MeasurePreserving (fun z : P × (E × E) => (z.1, z.2.swap))
      (π.prod (μ.prod μ)) (π.prod (μ.prod μ)) :=
    (MeasurePreserving.id π).prod Measure.measurePreserving_swap
  exact (hG.add (hG.comp_measurePreserving hs)).const_mul (weight / 4)

theorem fieldPairAverage_memLp {n } weight {G }
    (hG : MemLp (fun z  => G z.1 z.2) 2 (π.prod (μ.prod μ)))
    X (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ) :
    MemLp (fieldPairAverage n weight G X) 2 (π.prod ν) := by
  unfold fieldPairAverage
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  have hij := (Finset.mem_filter.mp hp).2
  have hm  :=
    (MeasurePreserving.id π).prod (pair_measurePreserving X hind hX hij)
  exact (fieldWeightedSymmetrization_memLp weight hG).comp_measurePreserving hm

end NearlyMinimax.PairUStatistic
