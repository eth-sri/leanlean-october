module

public import QPBT.Combining.SubLineZDeficit

/-!
# X-point subline averages

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

variable {P : AdmissibleParams} {ε δQ δP : ℝ} {S : ProjectiveSetting P ε}
  {points : CombinedPointsWitness S δQ}

/-! ## The mixture form of a one-point sub-line average -/

/-- The overlap of the paired-line measurement at two source lines with the
expanded `X`-point effect at a point, summed over the line answers.  This is
the deficit integrand in the proof of `lem:claim-17-2`, as a function of the
two source lines and the `X`-point alone. -/
def xPointOverlapAt (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : (LineDesc P.toLdParams × LineDesc P.toLdParams) ×
      (Fin P.m → PauliScalar P)) : ℝ :=
  ∑ fX, ∑ fZ, stateQForm S.psiHat
    (S.place first ((lines.T first.side w.1.1 w.1.2).effect (fX, fZ)) *
      S.place second ((S.pointMeasExpOption second.side .X w.2).effect (evalOpt w.1.1 w.2 fX)))

/-- At a pair of line-point pairs, the `X`-point overlap is the overlap of the
evaluated pair-line measurement with the completed `X`-point measurement; the
`Z`-point of the second pair only labels the evaluation classes. -/
theorem xPointOverlap_eq_at (lines : CombinedLinesWitness S points δP)
    (first second : Placement)
    (w : LinePointPairSample P) :
    xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2) =
      ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
        stateQForm S.psiHat
          (S.place first
            (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
              (evalOpt w.1.1 w.1.2 fs.1, evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X w.1.2).effect o.1)) :=
  (regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun o1 _ => (S.pointMeasExpOption second.side .X w.1.2).effect o1)).symm

/-- The deficit of the sub-line average of the `X`-point overlap is bounded by
the inflated line and point consistency errors.  This is the bound on the
deficit in the proof of `lem:claim-17-2`, blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1168-1201`. -/
theorem SubLineWitness.one_sub_avgOver_xPointOverlap_le_at
    (sublines : SubLineWitness P) (lines : CombinedLinesWitness S points δP)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    1 - avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
        (fun t => xPointOverlapAt lines first second (sample.2, projX (directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨components, hcomp, hmix⟩ :=
    SubLineWitness.exists_avgOver_X_eq_mixture P sublines (xPointOverlapAt lines first second)
  rw [hmix, ← avgOver_const_of_isProbability components hcomp 1, ← avgOver_sub]
  refine hcomp.avgOver_le_of_forall_le_on_support _ _ fun c _ => ?_
  rw [avgOver_congr _ _ _ fun w => xPointOverlap_eq_at lines first second w]
  refine lines.one_sub_overlap_restricted_le_at first second hopposite c.1 c.1 c.2.1 c.2.2
    (fun xz o => (S.pointMeasExpOption second.side .X xz.1).effect o.1)
    (fun xz o => (S.pointMeasExpOption second.side .Z xz.2).effect o.2)
    (fun _ _ => S.pointMeasExpOption_isProj _ _ _ _) (fun _ _ => S.pointMeasExpOption_isProj _ _ _ _) ?_
  exact le_of_eq_of_le (avgOver_congr _ _ _ fun xz => S.sum_norm_place_completedPair_sub_sq second _ _ _
    (fun _ => by rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some])
    (fun _ => by rw [S.pointMeasExpOption_effect_none, zero_mul])
    fun _ => by rw [S.pointMeasExpOption_effect_none, mul_zero])
    (points.orderedXZ_dist_le second)


end

end MIPStarRE.QPBT
