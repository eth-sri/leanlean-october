module

public import QPBT.Combining.EvalDeficit
public import QPBT.Combining.UniformLinePoint

/-! # Averaged overlaps on paired sublines

Sample an extended line and a point on it, and retain its two projected
line-point pairs. The joint law need not be a mixture of product laws. For
a single Pauli component, however, regrouping by the evaluated line answers
shows that the integrand depends only on the two lines and the selected
point. The marginal mixture property then suffices to transfer the deficit.
-/
@[expose] public section
namespace MIPStarRE.QPBT

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

abbrev LinePointPairSample.coords (w : LinePointPairSample P) := (w.1.2, w.2.2)

def SubLinePointSample.pairs (s : SubLinePointSample P) : LinePointPairSample P :=
  let u := directPointToPauli s.2
  ((s.1.2.1, projX u), (s.1.2.2, projZ u))

namespace SubLineWitness
variable (sublines : SubLineWitness P)

/-- The joint law of the projected line-point pairs. -/
def evalLaw := (subLinePointDist sublines.D).map SubLinePointSample.pairs

theorem evalLaw_isProbability : sublines.evalLaw.IsProbability :=
  ((Distribution.prod_isProbability sublines.isProbability (uniformDistribution_isProbability _)).map _).map _

theorem avg_coords (f : PauliPoint P × PauliPoint P → ℝ) :
    avgOver sublines.evalLaw (fun w => f w.coords) = avgOver (uniformDistribution _) f := by
  simp only [evalLaw, subLinePointDist, Distribution.avgOver_map, avgOver_prod]
  exact sublines.avgOver_projX_projZ P f

private theorem component_mixture (W : PauliKind)
    (f : (LineDesc P.toLdParams × LineDesc P.toLdParams) × PauliPoint P → ℝ) :
    ∃ μ : Distribution (SubLineComponent P), μ.IsProbability ∧
      avgOver sublines.evalLaw (fun (w : LinePointPairSample P) => f ((w.1.1, w.2.1), W.component w.coords)) =
        avgOver μ (fun c => avgOver (Distribution.prod (restrictedLinePointDist c.1 c.2.1)
          (restrictedLinePointDist c.1 c.2.2)) (fun (w : LinePointPairSample P) => f ((w.1.1, w.2.1), W.component w.coords))) := by
  obtain ⟨μ, hμ, hx, hz⟩ := sublines.source_mixture
  refine ⟨μ, hμ, ?_⟩
  cases W
  · simpa [PauliKind.component, SubLinePointSample.pairs, subLineXProjection, evalLaw, subLineXComponentDist, Distribution.avgOver_map, avgOver_bind, avgOver_prod]
      using congrArg (fun D => avgOver D f) hx
  · simpa [PauliKind.component, SubLinePointSample.pairs, subLineZProjection, evalLaw, subLineZComponentDist, Distribution.avgOver_map, avgOver_bind, avgOver_prod]
      using congrArg (fun D => avgOver D f) hz

end SubLineWitness

/-- Postprocessing the left measurement regroups the same weighted effects. -/
theorem placed_overlap_postprocess {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : ProjectiveSetting P ε) (first second : Placement)
    (M : Measurement α (S.ExpandedLocalSpace first.side)) (f : α → β)
    (R : β → Op (S.ExpandedLocalSpace second.side)) :
    (∑ b, stateQForm S.psiHat (S.place first ((M.postprocess f).effect b) * S.place second (R b))) =
      ∑ a, stateQForm S.psiHat (S.place first (M.effect a) * S.place second (R (f a))) := by
  classical
  simp only [Quantum.Measurement.postprocess_effect, S.place_finset_sum, Finset.sum_mul, stateQForm_finset_sum]
  exact Finset.sum_readout f _

variable (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP) (first second : Placement)

abbrev EvaluatedPair (P : AdmissibleParams) := Option (PauliScalar P) × Option (PauliScalar P)

/-- The line-pair overlap against an operator indexed by the two evaluations. -/
def lineOverlap (w : LinePointPairSample P) (R : EvaluatedPair P → Op (S.ExpandedLocalSpace second.side)) :=
  ∑ o, stateQForm S.psiHat (S.place first ((lines.evaluated first.side w).effect o) * S.place second (R o))

def SubLineWitness.meanOverlap
    (R : PauliPoint P × PauliPoint P → EvaluatedPair P → Op (S.ExpandedLocalSpace second.side)) :=
  avgOver sublines.evalLaw fun w => lineOverlap lines first second w (R w.coords)

private def singleOverlap (W : PauliKind) (v : (LineDesc P.toLdParams × LineDesc P.toLdParams) × PauliPoint P) :=
  ∑ fs, stateQForm S.psiHat (S.place first ((lines.T first.side v.1.1 v.1.2).effect fs) *
    S.place second ((S.pointMeasExpOption second.side W v.2).effect
      (evalOpt (W.component v.1) v.2 (W.component fs))))

private theorem lineOverlap_component (W : PauliKind) (w : LinePointPairSample P) :
    lineOverlap lines first second w (S.componentEffect second.side W w.coords) =
      singleOverlap lines first second W ((w.1.1, w.2.1), W.component w.coords) := by
  unfold lineOverlap CombinedLinesWitness.evaluated
  rw [placed_overlap_postprocess]
  cases W <;> rfl

/-- Either one-point overlap inherits the deficit of the restricted product laws. -/
theorem SubLineWitness.component_deficit (hopposite : first.IsOpposite second) (W : PauliKind) :
    1 - sublines.meanOverlap lines first second (S.componentEffect second.side W) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨μ, hμ, hm⟩ := sublines.component_mixture W (singleOverlap lines first second W)
  simp only [meanOverlap, lineOverlap_component, hm]
  apply sub_le_comm.mp
  refine (avgOver_const_of_isProbability μ hμ _).symm.le.trans (avgOver_mono _ _ _ fun c => ?_)
  simp_rw [← lineOverlap_component]
  exact sub_le_comm.mp (lines.one_sub_overlap_restricted_le first second hopposite W c.1 c.1 c.2.1 c.2.2)

end
end MIPStarRE.QPBT
