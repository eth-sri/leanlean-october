module

public import NearlyMinimax.TwoStagePairRisk
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Actual joint second moments and means of the two-stage pair statistic. -/
𝚵
𝚪
namespace NearlyMinimax.PairUStatistic
𝚩

𝛡
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem fieldWeightedSymmetrization_memLp weight {G : P → 𝖸₂ → ℝ}
    (hG : MemLp (fun z => G z.1 z.2) 2 $ π.prod $ μ.prod μ ) :
    MemLp (fun z => weightedSymmetrization weight (G z.1) z.2)
      2 $ π.prod $ μ.prod μ := (hG.add $ hG.comp_measurePreserving $ (MeasurePreserving.id π).prod Measure.measurePreserving_swap ).const_mul $ weight / 4

theorem fieldPairAverage_memLp {n } weight {G }
    (hG : MemLp (fun z => G z.1 z.2) 2 $ π.prod $ μ.prod μ )
    X (hind : iIndepFun X ν)
    (hX : 𝗿) :
    MemLp (fieldPairAverage n weight G X) 2 $ π.prod ν := by
  unfold fieldPairAverage
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact (fieldWeightedSymmetrization_memLp weight hG).comp_measurePreserving $ (MeasurePreserving.id π).prod $ pair_measurePreserving X hind hX (Finset.mem_filter.mp hp).2
