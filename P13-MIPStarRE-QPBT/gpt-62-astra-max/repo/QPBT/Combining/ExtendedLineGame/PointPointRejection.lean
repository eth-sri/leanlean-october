module

public import QPBT.Combining.ExtendedLineGame.MixedLinePointRejection

/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

@[simp] private theorem piCongrLeft_const_apply
    {I J K : Type*} (e : I ≃ J) (f : I → K) (j : J) :
    (e.piCongrLeft fun _ => K) f j = f (e.symm j) := by
  simp [Equiv.piCongrLeft_apply]

/-- Split a direct extended point into its two Pauli points and two scalar
coordinates.  This is a single bijection, so uniformity is joint rather than
an inference from four separate marginals. -/
noncomputable def directPointExtendedQuestionEquiv (P : AdmissibleParams) :
    (DirectPoint P.extendedDirectLd) ≃
      ExtendedPointQuestion P :=
  (Equiv.piCongrRight fun _ => (extendedDirectScalarEquiv P).toEquiv).trans <|
    ((finCombineEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans <|
      (Equiv.sumPiEquivProdPi fun _ : (Fin P.m ⊕ Fin P.m) ⊕ Fin 2 =>
        PauliScalar P).trans <|
        (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m =>
          PauliScalar P).prodCongr
            (piFinTwoEquiv fun _ => PauliScalar P)

/-- The joint coordinate equivalence reads exactly as `projX`, `projZ`,
`alphaVar`, and `betaVar`. -/
theorem directPointExtendedQuestionEquiv_apply
    (P : AdmissibleParams)
    (u : DirectPoint P.extendedDirectLd) :
    directPointExtendedQuestionEquiv P u =
      ((projX (directPointToPauli u), projZ (directPointToPauli u)),
        (directPointToPauli u (alphaVar P.m),
          directPointToPauli u (betaVar P.m))) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
        _ (.inl (.inl i)) = _
      simp
      rfl
    · funext i
      change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
        _ (.inl (.inr i)) = _
      simp
      rfl
  · apply Prod.ext
    · apply piCongrLeft_const_apply
    · apply piCongrLeft_const_apply

/-- A jointly uniform auxiliary coordinate can be discarded when both
operator families depend only on the first coordinate. -/
private theorem consistencyDefect_uniform_fst
    {X Y Alpha IA IB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Alpha] [DecidableEq Alpha]
    [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (A : X → Alpha → Op IA) (B : X → Alpha → Op IB)
    (psi : EuclideanSpace ℂ (IA × IB)) :
    consistencyDefect (uniformDistribution (X × Y))
        (fun xy a => heteroKron (A xy.1 a) 1)
        (fun xy a => heteroKron 1 (B xy.1 a)) psi =
      consistencyDefect (uniformDistribution X)
        (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (B x a)) psi := by
  simp [consistencyDefect]
  let f : X → ℝ := fun x =>
    ∑ a : Alpha, ∑ b : Alpha,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv (IA × IB) ℂ).symm
          ((heteroKron (A x a) 1 * heteroKron 1 (B x b)).mulVec psi))).re
  exact avgOver_uniform_fst f

variable (lines : ExtendedLinesWitness setting points deltaL)
  (sample : DirectLdSpace P.extendedDirectLd)

private theorem point_point_win_iff_read_eq
    (valuesA valuesB : Fin P.extendedDirectLd.k →
      DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap .point sample)
        (.point, directLdMap .point sample)
        (.pointVals valuesA) (.pointVals valuesB) = true ↔
      pointGameRead (.pointVals valuesA) = pointGameRead (.pointVals valuesB) := by
  simp [directLdWinPredicate, validDirectLdAnswer, if_true, decide_eq_true_eq, pointGameRead, Option.some.injEq]
  constructor
  · intro h
    rw [h]
  · intro h
    funext i
    have hval : i.val = 0 := by
      have hlt : i.val < 1 := i.isLt
      omega
    have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext hval
    subst i
    exact (extendedDirectScalarEquiv P).injective h

theorem pointPointReadLaw : BranchReadLaw (P := P) .point .point
    (fun _ => pointGameRead) (fun _ => pointGameRead) := by
  intro s a b ha hb
  cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
  apply point_point_win_iff_read_eq

private theorem point_rejectedMass_eq_read_mismatch :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap .point sample)
        (.point, directLdMap .point sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap .point sample)
        (.point, directLdMap .point sample)
        (fun answerA answerB => pointGameRead answerA ≠ pointGameRead answerB) := rejectedMass_of_readout lines _ _ _ _ (pointPointReadLaw sample)

/-- The point/point branch rejection is exactly the consistency defect of the
two completed scalar point readouts under the common uniform point question. -/
theorem point_branch_rejection_eq_consistencyDefect :
    directLdBranchRejectionProbability (strategy lines)
        (.point, .point) =
      bipartiteDefect (uniformDistribution
        (DirectPoint P.extendedDirectLd))
        (fun u => (points.Q .alice
        (projX (directPointToPauli u))
        (projZ (directPointToPauli u))).postprocess fun values =>
          some (directPointToPauli u (alphaVar P.m) * values.1 +
            directPointToPauli u (betaVar P.m) * values.2))
        (fun u => (points.Q .bob
        (projX (directPointToPauli u))
        (projZ (directPointToPauli u))).postprocess fun values =>
          some (directPointToPauli u (alphaVar P.m) * values.1 +
            directPointToPauli u (betaVar P.m) * values.2))
        (pairState setting) := by
  rw [directLdBranchRejectionProbability_point_point_eq]
  calc
    _ = avgOver (uniformDistribution
          (DirectPoint P.extendedDirectLd))
        (fun u => outcomeEventWeight (strategy lines)
          (directLdPointQuestionOf P.extendedDirectLd u)
          (directLdPointQuestionOf P.extendedDirectLd u)
          (fun answerA answerB => pointGameRead answerA ≠ pointGameRead answerB)) := by
      apply avgOver_congr
      intro u
      simpa [directLdPointQuestionOf, directLdMap] using
        point_rejectedMass_eq_read_mismatch lines
          ⟨u, P.extendedDirectLd.firstIndex, 0⟩
    _ = bipartiteDefect (uniformDistribution
          (DirectPoint P.extendedDirectLd))
        (fun u => (answerMeasurement lines .alice
        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
         pointGameRead)
        (fun u => (answerMeasurement lines .bob
        (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
         pointGameRead)
        (pairState setting) :=
      (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution
          (DirectPoint P.extendedDirectLd))
        (strategy lines)
        (directLdPointQuestionOf P.extendedDirectLd)
        (directLdPointQuestionOf P.extendedDirectLd)
        (fun _ => pointGameRead) (fun _ => pointGameRead)).symm
    _ = _ := by
      apply consistencyDefect_congr <;> intro u answer <;> dsimp only
      · rw [show directLdPointQuestionOf P.extendedDirectLd u =
            (.point, directLdMap .point
              ⟨u, P.extendedDirectLd.firstIndex, 0⟩) by rfl,
          point_read_effect]
      · rw [show directLdPointQuestionOf P.extendedDirectLd u =
            (.point, directLdMap .point
              ⟨u, P.extendedDirectLd.firstIndex, 0⟩) by rfl,
          point_read_effect]

/-- The point/point rejection probability of the supplied extended strategy is
bounded by the self-consistency error of its joint point measurements. -/
theorem point_point_rejection_le :
    directLdBranchRejectionProbability (strategy lines)
        (.point, .point) ≤ deltaQ := by
  rw [point_branch_rejection_eq_consistencyDefect]
  let dist :=
    uniformDistribution
    ((PauliPoint P) × (PauliPoint P))
  calc
    _ = bipartiteDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q => (points.Q .alice q.1.1 q.1.2).postprocess fun values =>
        some (q.2.1 * values.1 + q.2.2 * values.2))
        (fun q => (points.Q .bob q.1.1 q.1.2).postprocess fun values =>
        some (q.2.1 * values.1 + q.2.2 * values.2))
        (pairState setting) := by
      simp only [bipartiteDefect]
      rw [← consistencyDefect_uniform_question_equiv
        (directPointExtendedQuestionEquiv P)]
      apply consistencyDefect_congr <;> intro u answer <;> rw [directPointExtendedQuestionEquiv_apply]
    _ ≤ bipartiteDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q => points.Q .alice q.1.1 q.1.2)
        (fun q => points.Q .bob q.1.1 q.1.2)
        (pairState setting) := consistencyDefect_postprocess_question_le
        _
        _
        _
        _
        _
    _ = bipartiteDefect dist
        (fun xz => points.Q .alice xz.1 xz.2)
        (fun xz => points.Q .bob xz.1 xz.2)
        (pairState setting) := consistencyDefect_uniform_fst
        (X := (PauliPoint P) × (PauliPoint P))
        (fun xz => (points.Q .alice xz.1 xz.2).effect)
        (fun xz => (points.Q .bob xz.1 xz.2).effect)
        _
    _ = consistencyDefect dist
        (fun xz => (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect)
        (fun xz => (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect)
        setting.psiHat := by
      simp only [bipartiteDefect, consistencyDefect]
      apply avgOver_congr
      intro xz
      congr 1 with a
      congr 1 with b
      by_cases hab : a = b
      · simp [hab]
      · simp only [hab, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
        simp [placedMeasurement_effect, DistanceCalculus.placed_product_stateQForm_eq]
        apply stateQForm_pairState_eq_AA'_BA''
        · exact measurement_effect_hermitian (points.Q PlayerSide.alice xz.1 xz.2) a
        · exact measurement_effect_hermitian (points.Q PlayerSide.bob xz.1 xz.2) b
    _ ≤ opFamilyDistSq dist
        (fun xz values =>
          (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect values)
        (fun xz values =>
          (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect values)
        setting.psiHat := by
      apply consistencyDefect_le_opFamilyDistSq_of_projective
      · intro xz
        exact setting.placedMeasurement_isProjective .AA'
          _ (points.projective .alice xz.1 xz.2)
      · intro xz
        exact setting.placedMeasurement_isProjective .BA''
          _ (points.projective .bob xz.1 xz.2)
    _ = opFamilyDistSq dist
        (fun xz values =>
          setting.place .AA' ((points.Q .alice xz.1 xz.2).effect values))
        (fun xz values =>
          setting.place .BA'' ((points.Q .bob xz.1 xz.2).effect values))
        setting.psiHat := by
      apply opFamilyDistSq.eq_1
    _ ≤ deltaQ := points.self_consistent Placement.AA' Placement.BA'' trivial

end ExtendedLineGame

end

end MIPStarRE.QPBT
