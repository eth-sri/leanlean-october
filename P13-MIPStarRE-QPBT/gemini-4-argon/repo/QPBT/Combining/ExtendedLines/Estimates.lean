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
  classical
  let zOverlap := avgOver sublines.D (fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
      zPointOverlapAt lines first second (sample.2, projZ (directPointToPauli P
        (sample.1.base + t • sample.1.direction)))))
  have hδP : 0 ≤ δP := by
    refine le_trans ?_ (lines.consistent first second hopposite)
    unfold consistencyDefect
    exact avgOver_nonneg _ _ fun s =>
      consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
          (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2))
        ((points.Q second.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2))
  have hδQ : 0 ≤ δQ :=
    le_trans (opFamilyDistSq_nonneg _ _ _ _) (points.self_consistent first second hopposite)
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.one_le_m
  have hfirst : |avgOver sublines.D
      (pairedSublineOverlap S points lines first second) -
      avgOver (Distribution.prod sublines.D
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
        (orderedSublineOverlap S points lines first second)| ≤
      2 * δQ ^ (1 / 2 : ℝ) := by
    have heq : Real.sqrt (4 * δQ) = 2 * δQ ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num [Real.sqrt_eq_rpow]
    exact (sublines.paired_ordered_overlap_gap_le lines first second).trans_eq heq
  have hsecond : |avgOver (Distribution.prod sublines.D
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
        (orderedSublineOverlap S points lines first second) - zOverlap| ≤
      2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
    have hz : zOverlap = avgOver (Distribution.prod sublines.D
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
        (fun s => ∑ o : Option (PauliScalar P) × Option (PauliScalar P),
          stateQForm S.psiHat
            ((S.placedMeasurement first
              ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
                (evalOpt s.1.2.1 (projX (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
                  evalOpt s.1.2.2 (projZ (directPointToPauli P
                    (s.1.1.base + s.2 • s.1.1.direction))) fs.2)))).effect o *
              S.place second ((S.pointMeasExpOption second.side .Z
                (projZ (directPointToPauli P
                  (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2))) := by
      rw [SandwichProduct.avgOver_distribution_prod]
      refine avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_
      exact zPointOverlap_eq_at lines first second
        ((sample.2.1, projX (directPointToPauli P (sample.1.base + t • sample.1.direction))),
          (sample.2.2, projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))
    rw [hz]
    dsimp only [orderedSublineOverlap]
    refine (abs_overlap_gap_le_sqrt_one_sub_of_isProj'
      (Distribution.prod sublines.D
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun s => S.placedMeasurement first
        ((lines.T first.side s.1.2.1 s.1.2.2).postprocess (fun fs =>
          (evalOpt s.1.2.1 (projX (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction))) fs.1,
            evalOpt s.1.2.2 (projZ (directPointToPauli P
              (s.1.1.base + s.2 • s.1.1.direction))) fs.2))))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .X
        (projX (directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
      (fun s o => S.place second ((S.pointMeasExpOption second.side .Z
        (projZ (directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2))
      (fun s o => S.place second
        ((S.pointMeasExpOption second.side .Z
            (projZ (directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)))).effect o.2 *
          (S.pointMeasExpOption second.side .X
            (projX (directPointToPauli P (s.1.1.base + s.2 • s.1.1.direction)))).effect o.1))
      S.psiHat
      (Distribution.prod_isProbability _ _ sublines.isProbability
        (uniformDistribution_isProbability _))
      S.psiHat_norm
      (fun _ _ => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun _ _ => S.place_isProj _ (S.pointMeasExpOption_isProj _ _ _ _))
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => S.place_comm first second hopposite _ _)
      (fun _ _ => ProjectiveSetting.place_mul S second _ _)).trans
      ((Real.sqrt_le_sqrt ?_).trans (sqrt_deficit_bound_le _ _ _ hm hδP hδQ))
    refine (sub_le_sub_left ?_ 1).trans
      (sublines.one_sub_avgOver_xPointOverlap_le_at lines first second hopposite)
    rw [SandwichProduct.avgOver_distribution_prod]
    refine le_of_eq (avgOver_congr _ _ _ fun sample => avgOver_congr _ _ _ fun t => ?_)
    exact xPointOverlap_eq_at lines first second
      ((sample.2.1, projX (directPointToPauli P (sample.1.base + t • sample.1.direction))),
        (sample.2.2, projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))
  have hthird : |zOverlap - 1| ≤
      2 * Real.sqrt (P.m : ℝ) * (δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ)) := by
    have hdef := sublines.one_sub_avgOver_zPointOverlap_le_at lines first second hopposite
    have hle := sublines.avgOver_zPointOverlap_le_one_at lines first second hopposite
    have hnonneg : 0 ≤ zOverlap :=
      avgOver_nonneg _ _ fun _ => avgOver_nonneg _ _ fun _ =>
        zPointOverlap_nonneg_at lines first second hopposite _
    have h0 : 0 ≤ 1 - zOverlap := by linarith
    calc
      |zOverlap - 1| = Real.sqrt ((1 - zOverlap) ^ 2) := by
        rw [abs_sub_comm, abs_of_nonneg h0, Real.sqrt_sq h0]
      _ ≤ Real.sqrt (2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) :=
        Real.sqrt_le_sqrt (by nlinarith)
      _ ≤ _ := sqrt_deficit_bound_le _ _ _ hm hδP hδQ
  have hchain := (abs_sub_le _ _ (1 : ℝ)).trans
    (add_le_add hfirst ((abs_sub_le _ zOverlap (1 : ℝ)).trans (add_le_add hsecond hthird)))
  have hhalf : 0 ≤ δQ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_nonneg _
  have hsum : 0 ≤ δP ^ (1 / 4 : ℝ) + δQ ^ (1 / 4 : ℝ) :=
    add_nonneg (rpow_quarter_nonneg _) (rpow_quarter_nonneg _)
  have hquarter := rpow_quarter_nonneg ε
  simp only [Real.rpow_eq_pow] at hquarter
  have hdimension := Real.sqrt_nonneg (P.m : ℝ)
  refine hchain.trans ?_
  nlinarith [mul_nonneg hdimension hsum, mul_nonneg hdimension hquarter]

end

end MIPStarRE.QPBT
