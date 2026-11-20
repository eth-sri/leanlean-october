module

public import QPBT.Combining.ZEvalDeficit
public import QPBT.Combining.Lines.SubLineMixture

/-!
# Sub-line averages of the Z-point overlap

The Z-point overlap of the paired-line measurement depends on the two source
lines and the Z block of the sampled extended point. The separate projected-point
mixture properties of the directly indexed sub-line law identify each one-point
marginal as a mixture of restricted product laws. Both marginal averaging
identities are recorded here. Regrouping line answers by their evaluations
then transfers the Z-overlap deficit from
`MIPStarRE.QPBT.Combining.ZEvalDeficit` to this law.

The Z-overlap estimates hold for arbitrary opposite placements, with separate
first-player specializations. The concrete X-overlap deficit instead uses the
exact X marginal of the X-Z-X sandwich and is proved in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z estimates support blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`.
The separate marginal identities encode the analogue of Property 2 of
`lem:qld-sublines` for the directly indexed law; source-distribution transport
remains separate.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

set_option maxHeartbeats 500000

/-- Summing a paired-line answer against a family of point effects that
depends on the answer only through its two evaluations is summing the
evaluation classes of the paired-line measurement against that family.  This
is the fiber regrouping of the proofs of `lem:claim-17-1`, `lem:claim-17-2`,
and `lem:claim-17-3`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:2651-2830`. -/
theorem regroup_line_answer_sum_at {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (lineX lineZ : LineDesc P.toLdParams) (x z : PauliPoint P)
    (G : Option (PauliScalar P) → Option (PauliScalar P) →
      Op (S.ExpandedLocalSpace second.side)) :
    (∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          ((S.placedMeasurement first
            ((lines.T first.side lineX lineZ).postprocess (fun fs =>
              (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)))).effect o *
            S.place second (G o.1 o.2))) =
      ∑ fX, ∑ fZ, S.placedCorrelation first second
        ((lines.T first.side lineX lineZ).effect (fX, fZ)) (G (evalOpt lineX x fX) (evalOpt lineZ z fZ)) := by
  classical
  simp only [ProjectiveSetting.placedMeasurement_effect]
  simpa only [Fintype.sum_prod_type] using
    S.placed_overlap_postprocess first second (lines.T first.side lineX lineZ)
      (fun fs => (evalOpt lineX x fs.1, evalOpt lineZ z fs.2)) (fun o => G o.1 o.2)

/-- The projected source point, conditioned on its restricted line laws. -/
theorem SubLineWitness.exists_avgOver_source_eq_mixture (P : AdmissibleParams)
    (sublines : SubLineWitness P) (W : PauliKind)
    (F : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (PauliPoint P) → ℝ) :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => F (sample.2, W.projectPoint (directPointToPauli P
              (sample.1.base + t • sample.1.direction))))) =
        avgOver components (fun c =>
          avgOver (Distribution.prod (restrictedLinePointDist P c.1 c.2.1)
              (restrictedLinePointDist P c.1 c.2.2))
            (fun w => F ((w.1.1, w.2.1), W.component (w.1.2, w.2.2)))) := by
  obtain ⟨components, hcomp, h⟩ := sublines.exists_avgOver_joint P
  exact ⟨components, hcomp, h (fun w =>
    F ((w.1.1, w.2.1), W.component (w.1.2, w.2.2)))⟩

section Overlaps

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-- A sub-line triple sampled together with its affine parameter. -/
abbrev SubLineDraw (P : AdmissibleParams) := SubLineTriple P × DirectScalarQ P.extendedDirectLd

abbrev SubLineWitness.drawLaw (sublines : SubLineWitness P) : Distribution (SubLineDraw P) :=
  Distribution.prod sublines.D (uniformDistribution _)

theorem SubLineWitness.drawLaw_isProbability (sublines : SubLineWitness P) :
    sublines.drawLaw.IsProbability :=
  Distribution.prod_isProbability _ _ sublines.isProbability (uniformDistribution_isProbability _)

/-- The point on each source line obtained by projecting the drawn extended point. -/
abbrev SubLineDraw.linePoints (s : SubLineDraw P) : SourceLinePointPair P :=
  let u := directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)
  ((s.1.2.1, projX u), (s.1.2.2, projZ u))

abbrev SubLineDraw.basePoints (s : SubLineDraw P) : PointPair P := (s.linePoints.1.2, s.linePoints.2.2)

abbrev CombinedLinesWitness.placedSublineEval (lines : CombinedLinesWitness S points δP)
    (p : Placement) (s : SubLineDraw P) := S.placedMeasurement p (lines.evalPair p.side s.linePoints)

/-- Overlap on one triple, summing the original paired-line answers. -/
def sublineOverlap (lines : CombinedLinesWitness S points δP) (first second : Placement)
    (G : PointPair P → (Option (PauliScalar P) × Option (PauliScalar P)) →
      Op (S.ExpandedLocalSpace second.side)) (sample : SubLineTriple P) : ℝ :=
  avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
    let s : SubLineDraw P := (sample, t)
    ∑ fs, S.placedCorrelation first second
      ((lines.T first.side sample.2.1 sample.2.2).effect fs) (G (SubLineDraw.basePoints s)
          (evalOpt sample.2.1 (SubLineDraw.basePoints s).1 fs.1, evalOpt sample.2.2 (SubLineDraw.basePoints s).2 fs.2)))

/-- Regrouping under the full law of a triple and its parameter. -/
theorem SubLineWitness.avgOver_sublineOverlap_eq (sublines : SubLineWitness P)
    (lines : CombinedLinesWitness S points δP) (first second : Placement)
    (G : PointPair P → (Option (PauliScalar P) × Option (PauliScalar P)) →
      Op (S.ExpandedLocalSpace second.side)) :
    avgOver sublines.D (sublineOverlap lines first second G) =
      avgOver sublines.drawLaw (fun s => ∑ o, stateQForm S.psiHat
        ((lines.placedSublineEval first s).effect o * S.place second (G (SubLineDraw.basePoints s) o))) := by
  rw [SubLineWitness.drawLaw, SandwichProduct.avgOver_distribution_prod]
  apply avgOver_congr
  intro sample
  apply avgOver_congr
  intro t
  exact (S.placed_overlap_postprocess first second _ _ _).symm

section

variable (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (W : PauliKind)
include lines first second W

/-- Overlap of paired-line answers with the point readout in basis `W`. -/
def pointOverlapAt
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (PauliPoint P)) : ℝ :=
  ∑ fX, ∑ fZ, S.placedCorrelation first second
    ((lines.T first.side w.1.1 w.1.2).effect (fX, fZ)) ((S.pointMeasExpOption second.side W w.2).effect
        (evalOpt (W.component w.1) w.2 (W.component (fX, fZ))))

/-- At a pair of line-point pairs, the marginal overlap can be grouped by the
pair of evaluations. -/
theorem pointOverlap_eq_at (w : SourceLinePointPair P) :
    pointOverlapAt lines first second W ((w.1.1, w.2.1), W.component (w.1.2, w.2.2)) =
      ∑ o, S.placedCorrelation first second
        ((lines.evalPair first.side w).effect o) (S.completedPointPairEffect second.side W (w.1.2, w.2.2) o) := by
  have h := (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun a b => S.completedPointPairEffect second.side W (w.1.2, w.2.2) (a,b))).symm
  cases W <;> exact h

end

section

variable (sublines : SubLineWitness P)
    (lines : CombinedLinesWitness S points δP) (first second : Placement)
include sublines lines first second

/-- The marginal overlap on the full sub-line draw. -/
def SubLineWitness.pointOverlapAvg (W : PauliKind) : ℝ :=
  avgOver sublines.drawLaw (fun s => ∑ o, stateQForm S.psiHat
    ((lines.placedSublineEval first s).effect o *
      S.place second (S.completedPointPairEffect second.side W (SubLineDraw.basePoints s) o)))

/-- The marginal deficit of a sub-line average in either basis is bounded by
averaging the common estimate for each restricted component. -/
theorem SubLineWitness.one_sub_avgOver_pointOverlap_le_at (hopposite : first.IsOpposite second) (W : PauliKind) :
    1 - sublines.pointOverlapAvg lines first second W ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  have hread : sublines.pointOverlapAvg lines first second W =
      avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t => pointOverlapAt lines first second W (sample.2, W.projectPoint (directPointToPauli P
            (sample.1.base + t • sample.1.direction))))) := by
    rw [pointOverlapAvg, SubLineWitness.drawLaw, SandwichProduct.avgOver_distribution_prod]
    apply avgOver_congr
    intro sample
    apply avgOver_congr
    intro t
    exact (pointOverlap_eq_at lines first second W (SubLineDraw.linePoints (P := P) (sample, t))).symm
  obtain ⟨components, hcomp, hmix⟩ :=
    sublines.exists_avgOver_source_eq_mixture P W (pointOverlapAt lines first second W)
  rw [hread, hmix, ← avgOver_const_of_isProbability components hcomp 1, ← avgOver_sub]
  apply le_of_le_of_eq (avgOver_mono _ _ _ fun c => ?_)
    (avgOver_const_of_isProbability components hcomp _)
  rw [avgOver_congr _ _ _ fun w => pointOverlap_eq_at lines first second W w]
  exact lines.one_sub_overlap_restricted_le first second hopposite W c.1 c.1 c.2.1 c.2.2

end

end Overlaps

end

end MIPStarRE.QPBT
