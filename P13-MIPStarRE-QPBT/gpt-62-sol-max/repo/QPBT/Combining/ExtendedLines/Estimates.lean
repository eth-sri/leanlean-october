module

public import QPBT.Combining.ExtendedLines.Overlap
public import QPBT.Combining.ErrorBounds

/-!
# Estimates for the extended-line construction

This construction uses the directly indexed extended-line space, the answer
alphabet obtained from the field by adjoining an undefined-evaluation outcome,
and the corrected sum-form convention for polynomial errors.

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

/-- Remove the two point factors in succession, using their marginal deficits. -/
private theorem subline_ordered_overlap_near_one
    {P : AdmissibleParams} {ε δQ δP : ℝ}
    {S : ProjectiveSetting P ε} {points : CombinedPointsWitness S δQ}
    (lines : CombinedLinesWitness S points δP) (sublines : SubLineWitness P)
    (first second : Placement) (hop : first.IsOpposite second) :
    |avgOver sublines.D (orderedSublineOverlap S points lines first second) - 1| ≤
      4 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
  have hδP := (S.placedDefect_nonneg _ _ _ (lines.evalPair first.side)
    (fun s => points.completedPair second.side s.1.2 s.2.2) hop).trans (lines.consistent first second hop)
  have hδQ := (opFamilyDistSq_nonneg _ _ _ _).trans (points.self_consistent first second hop)
  have hroot (W : PauliKind) :=
    (Real.sqrt_le_sqrt (sublines.one_sub_avgOver_pointOverlap_le_at lines first second hop W)).trans
      (sqrt_deficit_bound_le _ _ _ (by exact_mod_cast P.one_le_m) hδP hδQ)
  let μ := sublines.drawLaw
  let A := lines.placedSublineEval first
  let B (W : PauliKind) (s : SubLineDraw P) (o : Option (PauliScalar P) × Option (PauliScalar P)) :=
    S.place second (S.completedPointPairEffect second.side W (SubLineDraw.basePoints s) o)
  have hB (W : PauliKind) (s) (o) : IsProj (B W s o) :=
    S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _)
  have hAB (W : PauliKind) (s) (o) : Commute ((A s).effect o) (B W s o) :=
    S.place_comm first second hop _ _
  have hX := abs_overlap_gap_le_sqrt_one_sub_of_isProj μ A (B .X) (B .Z) S.psiHat
    sublines.drawLaw_isProbability S.psiHat_norm (hB .X) (hB .Z) (hAB .X) (hAB .Z)
  have hZ := abs_overlap_gap_le_sqrt_one_sub_of_isProj μ A (B .Z) (fun _ _ => 1) S.psiHat
    sublines.drawLaw_isProbability S.psiHat_norm (hB .Z) (fun _ _ => IsStarProjection.one _)
    (hAB .Z) (fun _ _ => Commute.one_right _)
  simp only [one_mul, mul_one, sum_stateQForm_effect_eq_one _ _ S.psiHat_norm] at hZ
  rw [avgOver_const_of_isProbability _ sublines.drawLaw_isProbability] at hZ
  unfold orderedSublineOverlap
  rw [sublines.avgOver_sublineOverlap_eq]
  simp_rw [S.place_mul]
  have h := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add (hX.trans (hroot .X)) (hZ.trans (hroot .Z)))
  exact h.trans_eq (by simp only [Real.rpow_eq_pow]; ring)

/-- The first-route paired overlap estimate with its exact coefficient `6`.
This Lean-only quantitative specialization supports paper `lem:qld-4-13`,
lines 1020--1034, and exposes the current proof's witness for issue
Dengnifer/MIPStarRE-QPBT-bak#729. -/
theorem subline_joint_overlap_near_one_at_explicit
    (params : AdmissibleParams) (error pointError lineError : ℝ)
    (setting : ProjectiveSetting params error)
    (points : CombinedPointsWitness setting pointError)
    (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    |avgOver sublines.D (pairedSublineOverlap setting points lines first second) - 1| ≤
      6 * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
        (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
          error ^ (1 / 4 : ℝ))) := by
  have hfirst := sublines.paired_ordered_overlap_gap_le lines first second
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hfirst
  norm_num [Real.sqrt_eq_rpow] at hfirst
  have h := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add hfirst (subline_ordered_overlap_near_one lines sublines first second hopposite))
  refine h.trans ?_
  have hr : 0 ≤ pointError ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; positivity
  have hP := rpow_quarter_nonneg lineError
  have hQ := rpow_quarter_nonneg pointError
  have hE := rpow_quarter_nonneg error
  simp only [Real.rpow_eq_pow] at hP hQ hE
  nlinarith [mul_nonneg (Real.sqrt_nonneg (params.m : ℝ)) hP,
    mul_nonneg (Real.sqrt_nonneg (params.m : ℝ)) hQ,
    mul_nonneg (Real.sqrt_nonneg (params.m : ℝ)) hE]

/-- A universal constant bounds the deviation of the paired subline overlap from
one in terms of the point, line, and strategy errors. -/
theorem subline_joint_overlap_near_one_at :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (params : AdmissibleParams) (error pointError lineError : ℝ)
        (setting : ProjectiveSetting params error)
        (points : CombinedPointsWitness setting pointError)
        (lines : CombinedLinesWitness setting points lineError) (sublines : SubLineWitness params)
        (first second : Placement), first.IsOpposite second →
        |avgOver sublines.D (pairedSublineOverlap setting points lines first second) - 1| ≤
          constant * (pointError ^ (1 / 2 : ℝ) + Real.sqrt (params.m : ℝ) *
            (lineError ^ (1 / 4 : ℝ) + pointError ^ (1 / 4 : ℝ) +
              error ^ (1 / 4 : ℝ))) := ⟨6, by norm_num, subline_joint_overlap_near_one_at_explicit⟩

end

end MIPStarRE.QPBT
