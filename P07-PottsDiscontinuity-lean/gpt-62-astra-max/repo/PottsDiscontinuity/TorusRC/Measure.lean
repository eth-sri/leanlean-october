module

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.FK.Probability

/-!
# The critical random-cluster probability on the indexed diamond torus

Normalize the actual indexed-edge weight `torusRCWeight` of `Torus/DiamondGraph.lean`,
retaining loops and parallel edges
for small periods. No identification with a simple-graph configuration space
is required to define this law.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

section
variable (q : Set.Ici (1 : ℝ))

theorem criticalParameter_pos :
    0 < (rcCriticalParameter q).val := by
  have hq := lt_of_lt_of_le zero_lt_one q.property
  exact div_pos (Real.sqrt_pos.2 hq) (by positivity)

theorem criticalParameter_lt_one :
    (rcCriticalParameter q).val < 1 := by
  exact (div_lt_one (by positivity)).2 (by linarith)

end

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (A : RCConfig N M)
include hN hM q

theorem torusRCWeight_pos :
    0 < torusRCWeight hN hM q A := by
  exact mul_pos (mul_pos (pow_pos (criticalParameter_pos q) _)
    (pow_pos (sub_pos.2 (criticalParameter_lt_one q)) _))
    (pow_pos (lt_of_lt_of_le zero_lt_one q.property) _)

/-- Sum over all indexed configurations, including isolated vertices in the weight. -/
noncomputable def torusRCPartition : ℝ :=
  FK.FiniteProbability.partition (torusRCWeight hN hM q)

theorem torusRCPartition_pos : 0 < torusRCPartition hN hM q :=
  FK.FiniteProbability.partition_pos (torusRCWeight_pos hN hM q)

include A in
/-- The normalized mass of an indexed configuration. -/
noncomputable def torusRCMass : ℝ :=
  torusRCWeight hN hM q A / torusRCPartition hN hM q

theorem torusRCMass_pos :
    0 < torusRCMass hN hM q A :=
  div_pos (torusRCWeight_pos hN hM q A) (torusRCPartition_pos hN hM q)

theorem sum_torusRCMass : ∑ A, torusRCMass hN hM q A = 1 :=
  FK.FiniteProbability.sum_probability (torusRCWeight_pos hN hM q)

/-- The probability mass function of the critical indexed diamond-torus law. -/
noncomputable def torusRCPMF : PMF (RCConfig N M) :=
  FK.FiniteProbability.pmf (torusRCWeight_pos hN hM q)

theorem torusRCPMF_apply :
    torusRCPMF hN hM q A = ENNReal.ofReal (torusRCMass hN hM q A) := rfl

/-- The critical torus RC probability measure, with the product discrete sigma-field. -/
noncomputable def torusRCMeasure : Measure (RCConfig N M) :=
  (torusRCPMF hN hM q).toMeasure

instance torusRCMeasure_isProbabilityMeasure : IsProbabilityMeasure (torusRCMeasure hN hM q) := by
  unfold torusRCMeasure
  infer_instance

/-- Real-valued event probability under the critical torus RC measure. -/
noncomputable def torusRCProbability (E : Set (RCConfig N M)) : ℝ :=
  (torusRCMeasure hN hM q).real E

theorem torusRCMeasure_singleton :
    torusRCMeasure hN hM q {A} = ENNReal.ofReal (torusRCMass hN hM q A) := (PMF.toMeasure_apply_singleton _ A (measurableSet_singleton A)).trans
    (torusRCPMF_apply hN hM q A)

theorem torusRCProbability_singleton :
    torusRCProbability hN hM q {A} = torusRCMass hN hM q A := by
  unfold torusRCProbability Measure.real
  rw [torusRCMeasure_singleton, ENNReal.toReal_ofReal (torusRCMass_pos hN hM q A).le]

end PottsDiscontinuity.TorusRC
