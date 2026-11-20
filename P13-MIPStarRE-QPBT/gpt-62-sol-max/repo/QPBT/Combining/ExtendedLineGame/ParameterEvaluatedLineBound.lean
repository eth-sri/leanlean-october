module

public import QPBT.Combining.DirectLowDegree.Transport.LineResampling
public import QPBT.Combining.ExtendedLineGame.LineNoneMass
public import QPBT.Combining.ExtendedLineGame.ParameterCompletion

/-!
# Bounds for independently parameter-evaluated line answers

This module specializes the parameter/completed-read comparison to the axis
and diagonal measurements supplied by an `ExtendedLinesWitness`. The affine
parameter is sampled independently of the line. Affine resampling then
recovers the original joint line-point law, including zero directions.
The numerical estimates are formalization-only consequences of the supplied
point and line witnesses supporting the classical-game construction in the
proof of `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#341.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

local notation "D" => P.extendedDirectLd
local notation "Sample" => DirectLdSpace D
local notation "Scalar" => DirectScalarQ D
local notation "LinePoint" => DirectLineDesc D × (Fin P.extendedDirectLd.m → Scalar)

/-- The degree bound for the coefficient vector returned by a line question. -/
abbrev lineDegree (P : AdmissibleParams) : LineKind → ℕ
  | .axis => P.d
  | .diagonal => P.extendedDirectLd.m * P.extendedDirectLd.d

section

variable (kind : LineKind)

/-- Read the unique component of a valid line answer. Wrong formats have zero weight. -/
abbrev lineCoefficients (a : DirectLdAnswer D) :
    DirectDegPoly D (lineDegree P kind) :=
  match kind, a with
  | .axis, .alinePolys c => c onlyCoordinate
  | .diagonal, .dlinePolys c => c onlyCoordinate
  | _, _ => 0

/-- The canonical direct-game question represented by the sampled line. -/
abbrev lineQuestion (l : DirectLineDesc D) : DirectLdQuestion D :=
  (lineTag kind, ⟨l.base, l.index, match kind with | .axis => 0 | .diagonal => l.direction⟩)

/-- The evaluation defect under the line marginal and an independent affine parameter. -/
def parameterEvaluationDefect (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LineKind) : ℝ :=
  avgOver (linePointLaw P kind) fun s =>
    avgOver (uniformDistribution Scalar) fun t =>
      parameterEvalDefect (strategy lines) (lineQuestion kind s.1) (lineQuestion kind s.1)
        (lineCoefficients kind) (lineCoefficients kind) t

private theorem sample_line_question (s : Sample) :
    lineQuestion kind (sampleLine kind s) = sampleQuestion (lineTag kind) s := by
  cases kind <;> rfl

private theorem lineGameRead_eq (s : Sample) (a : DirectLdAnswer D)
    (h : validDirectLdAnswer (lineTag kind) a = true) :
    lineGameRead kind s a =
      (directEvalOpt (sampleLine kind s) s.point (lineCoefficients kind a)).map
        (extendedDirectScalarEquiv P) := by
  cases kind <;> cases a <;> simp [lineTag, validDirectLdAnswer] at h <;> rfl

private theorem avgOver_line_resample (F : LinePoint → ℝ) :
    avgOver ((linePointLaw P kind).map Prod.fst) (fun l =>
      avgOver (uniformDistribution Scalar) (fun t => F (l, l.base + t • l.direction))) =
    avgOver (linePointLaw P kind) F := by
  cases kind
  · exact avgOver_directALinePointDist_resample D F
  · exact avgOver_directDLinePointDist_resample D F

end

private theorem parameterEvaluationDefect_le_completed
    (lines : ExtendedLinesWitness setting points deltaL) (kind : LineKind) :
    parameterEvaluationDefect lines kind ≤ sameLineEvaluationDefect lines kind +
      lineNoneMass lines kind .alice + lineNoneMass lines kind .bob := by
  let S := strategy lines
  let q := lineQuestion (P := P) kind
  let e (s : LinePoint) a := directEvalOpt s.1 s.2 (lineCoefficients kind a)
  let F (s : LinePoint) := outcomeEventWeight S (q s.1) (q s.1) (fun a b => e s a ≠ e s b) +
    aliceEventWeight S (q s.1) (fun a => e s a = none) +
    bobEventWeight S (q s.1) (fun b => e s b = none)
  calc
    _ ≤ avgOver (linePointLaw P kind) F := by
      rw [← avgOver_line_resample kind F, Distribution.avgOver_map]
      exact avgOver_mono _ _ _ fun s => avgOver_mono _ _ _ fun t =>
        parameterEvalDefect_le_completed_add_none S (q s.1) (q s.1)
          (lineCoefficients kind) (lineCoefficients kind) s.1 t
    _ = _ := by
      rw [show sameLineEvaluationDefect lines kind = _ from
        WinImplications.consistencyDefect_postprocess_eq_mismatch
          (uniformDistribution Sample) S (sampleQuestion (lineTag kind))
          (sampleQuestion (lineTag kind)) (lineGameRead kind) (lineGameRead kind)]
      simp only [linePointLaw, Distribution.avgOver_map, lineNoneMass, ← avgOver_add]
      refine avgOver_congr _ _ _ fun s => ?_
      dsimp only [F, q, e, sideEventWeight, S]
      rw [sample_line_question]
      simp_rw [← outcome_event_weight_left_eq (strategy lines) _ (sampleQuestion (lineTag kind) s),
        ← outcome_event_weight_right_eq (strategy lines) (sampleQuestion (lineTag kind) s)]
      congr 1 <;> (first | apply outcomeEventWeight_congr_valid | congr 1 <;>
        apply outcomeEventWeight_congr_valid)
      all_goals
        intro a b ha hb
        simp [lineGameRead_eq kind s a ha, lineGameRead_eq kind s b hb,
          (Option.map_injective (extendedDirectScalarEquiv P).injective).eq_iff]

/-- Independent evaluations disagree only at the rate of completed disagreements and failures. -/
theorem parameterEvaluationDefect_le
    (lines : ExtendedLinesWitness setting points deltaL) (kind : LineKind) :
    parameterEvaluationDefect lines kind ≤ 6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have h := parameterEvaluationDefect_le_completed lines kind
  have hsame := sameLineEvaluationDefect_le lines kind
  have ha := (alice_line_none_mass_le_rejection lines kind).trans (line_point_rejection_le lines kind)
  have hb := (bob_line_none_mass_le_rejection lines kind).trans (point_line_rejection_le lines kind)
  linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
