module

public import QPBT.Combining.ExtendedLineGame.LineNoneMass
public import QPBT.Combining.DirectLowDegree.CoefficientConsistency

/-! # From line evaluation to full coefficient consistency

Both line branches compare singleton tuples of coefficients. Random parameter
sampling tests those coefficients up to the univariate collision loss. We
charge disagreement at the sampled parameter to disagreement of the two
completed reads or failure of the first read. Resampling along the line turns
these into the same-line and line/point bounds on the actual game questions.
-/

@[expose] public section

namespace MIPStarRE.QPBT.ExtendedLineGame

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
  {setting : ProjectiveSetting P epsilon} {points : CombinedPointsWitness setting deltaQ}

private abbrev Sample (P : AdmissibleParams) := DirectLdSpace P.extendedDirectLd
private abbrev Line (P : AdmissibleParams) := DirectLineDesc P.extendedDirectLd

def lineDegree (P : AdmissibleParams) : LineKind → ℕ
  | .axis => P.d
  | .diagonal => P.extendedDirectLd.m * P.extendedDirectLd.d

private def desc : LineKind → Sample P → Line P
  | .axis => directALineDescOf _
  | .diagonal => directDLineDescOf _

private def query : LineKind → Line P → DirectLdQuestion P.extendedDirectLd
  | .axis, l => (.aline, ⟨l.base, l.index, 0⟩)
  | .diagonal, l => (.dline, ⟨l.base, l.index, l.direction⟩)

private theorem query_desc (k : LineKind) (s : Sample P) :
    query k (desc k s) = branchQ (lineTag k) s := by cases k <;> rfl

private def coefficients? (k : LineKind) : DirectLdAnswer P.extendedDirectLd →
    Option (DirectDegPoly P.extendedDirectLd (lineDegree P k)) :=
  match k with
  | .axis => fun | .alinePolys f => some (f onlyCoordinate) | _ => none
  | .diagonal => fun | .dlinePolys f => some (f onlyCoordinate) | _ => none

variable (k : LineKind)
private abbrev coeff (a : DirectLdAnswer P.extendedDirectLd) := (coefficients? k a).getD 0

/-- The geometric completed read, expressed on a line and a point instead of
on the sampled seed. A missing tag or ambiguous evaluation gives `none`. -/
private def completed (l : Line P) (u : DirectPoint P.extendedDirectLd) : Readout P :=
  fun a => (coefficients? k a).bind fun c => (directEvalOpt l u c).map (extendedDirectScalarEquiv P)

private theorem completed_desc (s : Sample P) (a) :
    completed k (desc k s) s.point a = lineRead k s a := by cases k <;> cases a <;> rfl

private theorem completed_sound {l : Line P} {t : DirectScalarQ P.extendedDirectLd} {a v}
    (h : completed k l (l.base + t • l.direction) a = some v) :
    extendedDirectScalarEquiv P (evalCoefficient (coeff k a) t) = v := by
  obtain ⟨c, hc, hw⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨w, heval, rfl⟩ := Option.map_eq_some_iff.mp hw
  simp only [coeff, hc, Option.getD_some]
  exact congrArg _ (((directEvalOpt_eq_some_iff _ _ c w).1 heval).2 t rfl)

private theorem parameter_event_le (lines : ExtendedLinesWitness setting points deltaL)
    (l : Line P) (t : DirectScalarQ P.extendedDirectLd) :
    let q := query k l
    let r := completed k l (l.base + t • l.direction)
    outcomeEventWeight (strategy lines) q q (fun a b =>
        evalCoefficient (coeff k a) t ≠ evalCoefficient (coeff k b) t) ≤
      outcomeEventWeight (strategy lines) q q (fun a b => r a ≠ r b) +
        aliceEventWeight (strategy lines) q (fun a => r a = none) := by
  intro q r
  rw [← outcome_event_weight_left_eq (strategy lines) q q]
  simp only [outcomeEventWeight, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hsame (hab : r a = r b) (hn : r a ≠ none) :
      evalCoefficient (coeff k a) t = evalCoefficient (coeff k b) t := by
    cases h : r a with
    | none => contradiction
    | some v =>
        exact (extendedDirectScalarEquiv P).injective ((completed_sound k h).trans (completed_sound k (hab.symm.trans h)).symm)
  have hw := outcomeWeight_nonneg (strategy lines) q q a b
  split_ifs <;> grind

private theorem resample (F : Line P × DirectPoint P.extendedDirectLd → ℝ) :
    avgOver (uniformDistribution (Sample P)) (fun s =>
      let l := desc k s
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t => F (l, l.base + t • l.direction))) =
        avgOver (uniformDistribution _) (fun s => F (desc k s, s.point)) := by
  cases k with
  | axis => simpa only [directALinePointDist, Distribution.avgOver_map, desc, Sample] using
      avgOver_directALinePointDist_resample P.extendedDirectLd F
  | diagonal => simpa only [directDLinePointDist, Distribution.avgOver_map, desc, Sample] using
      avgOver_directDLinePointDist_resample P.extendedDirectLd F

variable (lines : ExtendedLinesWitness setting points deltaL)

private def parameterLoss :=
  avgOver (uniformDistribution (Sample P)) fun s =>
    let q := branchQ (lineTag k) s
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun t =>
      outcomeEventWeight (strategy lines) q q fun a b =>
        evalCoefficient (coeff k a) t ≠ evalCoefficient (coeff k b) t

private theorem parameterLoss_le :
    parameterLoss k lines ≤ 4 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  let F (p : Line P × DirectPoint P.extendedDirectLd) :=
    let r := completed k p.1 p.2
    let q := query k p.1
    outcomeEventWeight (strategy lines) q q (fun a b => r a ≠ r b) +
      aliceEventWeight (strategy lines) q (fun a => r a = none)
  calc
    _ ≤ avgOver (uniformDistribution (Sample P)) (fun s => avgOver
        (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun t =>
          F (desc k s, (desc k s).base + t • (desc k s).direction)) := by
      unfold parameterLoss
      refine avgOver_mono _ _ _ fun s => avgOver_mono _ _ _ fun t => ?_
      dsimp only [F]
      simpa only [query_desc] using parameter_event_le k lines (desc k s) t
    _ = _ := resample k F
    _ = _ := by
      simp only [F, query_desc, completed_desc, avgOver_add]
      rw [← WinImplications.consistencyDefect_postprocess_eq_mismatch]
      rfl
    _ ≤ _ := add_le_add (same_line_evaluation_le lines k) (line_none_le_rejection lines k)
    _ ≤ _ := by linarith [(mixed_bounds lines k).1]

private theorem sameLine_iff (s : Sample P) (a b : DirectLdAnswer P.extendedDirectLd)
    (ha : validDirectLdAnswer (lineTag k) a = true) (hb : validDirectLdAnswer (lineTag k) b = true) :
    directLdWinPredicate _ (branchQ (lineTag k) s) (branchQ (lineTag k) s) a b = true ↔
        coeff k a = coeff k b := by
  have singleton {β : Type} (f g : Fin P.extendedDirectLd.k → β) :
      f = g ↔ f onlyCoordinate = g onlyCoordinate := by
    refine ⟨fun h => congrFun h _, fun h => funext fun i => ?_⟩
    have hi : i = onlyCoordinate := Fin.ext (Nat.eq_zero_of_le_zero (show i.val ≤ 0 from Nat.le_of_lt_succ i.isLt))
    rwa [hi]
  cases k <;> cases a <;> cases b <;>
    simp_all [lineTag, branchQ, directLdWinPredicate, validDirectLdAnswer, coeff, coefficients?, singleton] <;> rfl

/-- Full coefficient answers disagree with at most the completed-read error
plus the probability of collision at a fresh uniform parameter. -/
theorem sameLine_rejection_le :
    rejection lines (lineTag k) (lineTag k) ≤
      4 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) + lineDegree P k / P.extendedDirectLd.q := by
  let q := branchQ (P := P) (lineTag k)
  let S := strategy lines
  let μ := uniformDistribution (Sample P)
  have h := consistencyDefect_directCoefficients_le_evaluated_add P.extendedDirectLd μ (fun s => (S.A (q s)).postprocess (coeff k))
    (fun s => (S.B (q s)).postprocess (coeff k)) S.ψ (uniformDistribution_isProbability _) S.ψ_norm
  simp only [MIPStarRE.Quantum.Measurement.postprocess_comp] at h
  rw [WinImplications.consistencyDefect_postprocess_eq_mismatch,
    WinImplications.consistencyDefect_postprocess_eq_mismatch, avgOver_prod] at h
  refine le_trans ?_ (h.trans (add_le_add (parameterLoss_le k lines) le_rfl))
  apply le_of_eq
  exact avgOver_congr _ _ _ fun s => rejectedMass_of_readout lines _ _ _ _ (sameLine_iff k s)

end
end MIPStarRE.QPBT.ExtendedLineGame
