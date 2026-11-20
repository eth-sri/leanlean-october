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

variable {n : ℕ} (weight : ℝ) {G : P → E × E → ℝ}
    (hG : MemLp (fun z : P × (E × E) => G z.1 z.2) 2 (π.prod (μ.prod μ)))
include hG

theorem fieldWeightedSymmetrization_memLp :
    MemLp (fun z => weightedSymmetrization weight (G z.1) z.2)
      2 (π.prod (μ.prod μ)) := (hG.add (hG.comp_measurePreserving ((MeasurePreserving.id π).prod Measure.measurePreserving_swap))).const_mul (weight / 4)

theorem fieldPairAverage_memLp
    {X : Fin n → Ω → E} (hind : iIndepFun X ν)
    (hX : ∀ i, MeasurePreserving (X i) ν μ) :
    MemLp (fieldPairAverage weight G X) 2 (π.prod ν) := by
  unfold fieldPairAverage
  simp [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact (fieldWeightedSymmetrization_memLp weight hG).comp_measurePreserving ((MeasurePreserving.id π).prod (pair_measurePreserving X hind hX ((Finset.mem_filter.mp hp).2)))

end NearlyMinimax.PairUStatistic
