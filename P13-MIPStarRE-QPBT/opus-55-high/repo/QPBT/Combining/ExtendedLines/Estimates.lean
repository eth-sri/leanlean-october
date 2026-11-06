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
              error ^ (1 / 4 : ℝ))) := by
  refine ⟨6, by norm_num, fun P ε δQ δP S points lines sublines first second hopposite => ?_⟩
  have hprob : (Distribution.prod sublines.D
      (uniformDistribution (DirectScalarQ P.extendedDirectLd))).IsProbability :=
    Distribution.prod_isProbability _ _ sublines.isProbability
      (uniformDistribution_isProbability _)
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent first second hopposite)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  set zOverlap := avgOver sublines.D (fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
      zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
        (sample.1.base + t • sample.1.direction))))) with hz
  have hfirst : |avgOver sublines.D
      (pairedSublineOverlap S points lines first second) - avgOver sublines.D
        (orderedSublineOverlap S points lines first second)| ≤
      2 * δQ ^ (1 / 2 : ℝ) := by
    have heq : Real.sqrt (4 * δQ) = 2 * δQ ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num [Real.sqrt_eq_rpow]
    exact (sublines.paired_ordered_overlap_gap_le lines first second).trans_eq heq
  let u (s : SubLineTriple P × DirectScalarQ P.extendedDirectLd) :=
    directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)
  have hsecond : |avgOver sublines.D
      (orderedSublineOverlap S points lines first second) - zOverlap| ≤
      2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
    refine le_of_eq_of_le ?_ ((abs_overlap_gap_le_sqrt_one_sub_of_isProj _
      (fun s => S.placedMeasurement first ((lines.T first.side s.1.2.1 s.1.2.2).postprocess
        fun fs => (evalOpt s.1.2.1 (projX (u s)) fs.1, evalOpt s.1.2.2 (projZ (u s)) fs.2)))
      (fun s (o : Option (PauliScalar P) × Option (PauliScalar P)) =>
        S.place second ((S.pointMeasExpOption second.side .X (projX (u s))).effect o.1))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .Z (projZ (u s))).effect o.2))
      S.psiHat hprob S.psiHat_norm
      (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun s o => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun s o => S.place_comm first second hopposite _ _)
      (fun s o => S.place_comm first second hopposite _ _)).trans
      ((Real.sqrt_le_sqrt (le_of_eq_of_le ?_
        (sublines.one_sub_avgOver_xPointOverlap_le_at lines first second hopposite))).trans
      (sqrt_deficit_bound_le _ _ _ hm hδP hδQ)))
    · simp only [SandwichProduct.avgOver_distribution_prod, hz, ← ProjectiveSetting.place_mul]
      congr 2 <;> refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
      · exact ((regroup_line_answer_sum_at lines first second _ _ _ _ fun o1 o2 =>
          (S.pointMeasExpOption second.side .Z (projZ (u (sample, t)))).effect o2 *
            (S.pointMeasExpOption second.side .X (projX (u (sample, t)))).effect o1).trans
          (by simp only [Fintype.sum_prod_type]; rfl)).symm
      · exact (regroup_line_answer_sum_at lines first second _ _ _ _
          (fun _ o2 => (S.pointMeasExpOption second.side .Z _).effect o2)).symm
    · rw [SandwichProduct.avgOver_distribution_prod]
      congr 1
      exact avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t =>
        regroup_line_answer_sum_at lines first second sample.2.1 sample.2.2 _ _
          (fun o1 _ => (S.pointMeasExpOption second.side .X (projX (directPointToPauli P
            (sample.1.base + t • sample.1.direction)))).effect o1)
  have hle := sublines.avgOver_zPointOverlap_le_one_at lines first second hopposite
  have hthird : 1 - zOverlap ≤
      2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
    have hdef := sublines.one_sub_avgOver_zPointOverlap_le_at lines first second hopposite
    have h0 : 0 ≤ zOverlap := avgOver_nonneg _ _ fun sample => avgOver_nonneg _ _ fun t =>
      zPointOverlap_nonneg_at lines first second hopposite _
    refine le_trans ?_ ((Real.sqrt_le_sqrt hdef).trans (sqrt_deficit_bound_le _ _ _ hm hδP hδQ))
    rw [Real.le_sqrt (by linarith) (by linarith)]
    nlinarith
  have hhalf : 0 ≤ δQ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsum : 0 ≤ δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ) :=
    add_nonneg (rpow_quarter_nonneg _) (rpow_quarter_nonneg _)
  have hquarter : 0 ≤ ε ^ (1 / 4 : ℝ) := rpow_quarter_nonneg ε
  have hdimension := Real.sqrt_nonneg (P.m : ℝ)
  rw [abs_le] at *
  constructor <;> nlinarith [mul_nonneg hdimension hsum, mul_nonneg hdimension hquarter]

end

end MIPStarRE.QPBT
