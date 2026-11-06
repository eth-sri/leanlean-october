module

public import QPBT.Combining.ExtendedLineGame.LinePointRejection
public import QPBT.Combining.Points.Placement

/-!
# Point/point rejection for the extended direct game
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
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]

/-- Split a direct extended point into its two Pauli points and two scalar
coordinates. -/
noncomputable def directPointExtendedQuestionEquiv (P : AdmissibleParams) :
    (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) ≃
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
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointExtendedQuestionEquiv P u =
      ((projX (directPointToPauli P u), projZ (directPointToPauli P u)),
        (directPointToPauli P u (alphaVar P.m),
          directPointToPauli P u (betaVar P.m))) := by
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) (Prod.ext ?_ ?_)
  · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
      (fun j => extendedDirectScalarEquiv P (u j)) (.inl (.inl i)) = _
    rw [piCongrLeft_const_apply]; rfl
  · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
      (fun j => extendedDirectScalarEquiv P (u j)) (.inl (.inr i)) = _
    rw [piCongrLeft_const_apply]; rfl
  · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
      (fun j => extendedDirectScalarEquiv P (u j)) (.inr 0) = _
    rw [piCongrLeft_const_apply]; rfl
  · change (finCombineEquiv P.m).piCongrLeft (fun _ => PauliScalar P)
      (fun j => extendedDirectScalarEquiv P (u j)) (.inr 1) = _
    rw [piCongrLeft_const_apply]; rfl

private theorem consistencyDefect_dependent_postprocess_le
    {X Alpha Beta IA IB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Alpha] [DecidableEq Alpha]
    [Fintype Beta] [DecidableEq Beta]
    [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (mu : Distribution X) (A : X → Measurement Alpha IA)
    (B : X → Measurement Alpha IB) (psi : EuclideanSpace ℂ (IA × IB))
    (f : X → Alpha → Beta) :
    consistencyDefect mu
        (fun x b => heteroKron (((A x).postprocess (f x)).effect b) 1)
        (fun x b => heteroKron 1 (((B x).postprocess (f x)).effect b)) psi ≤
      consistencyDefect mu
        (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) psi := by
  unfold consistencyDefect
  refine avgOver_mono _ _ _ fun x => ?_
  have h := consistencyDefect_postprocess_le (uniformDistribution Unit)
    (fun _ => A x) (fun _ => B x) psi (f x)
  unfold consistencyDefect at h
  simpa only [avgOver_uniform_const] using h

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
  unfold consistencyDefect
  let f : X → ℝ := fun x =>
    ∑ a : Alpha, ∑ b : Alpha,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv (IA × IB) ℂ).symm
          ((heteroKron (A x a) 1 * heteroKron 1 (B x b)).mulVec psi))).re
  change avgOver (uniformDistribution (X × Y)) (fun xy => f xy.1) =
    avgOver (uniformDistribution X) f
  exact avgOver_uniform_fst f

private theorem point_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => pointGameRead answerA ≠ pointGameRead answerB) :=
  rejectedMass_eq_read_mismatch_of_win_iff lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> try contradiction
    rename_i valuesA valuesB
    simp only [directLdWinPredicate, validDirectLdAnswer,
      Bool.and_self, ite_true, decide_eq_true_eq, pointGameRead, Option.some.injEq,
      (extendedDirectScalarEquiv P).injective.eq_iff]
    refine ⟨fun h => h ▸ rfl, fun h => funext fun i => ?_⟩
    have hi : i = onlyCoordinate := by
      ext; have := i.isLt; change i.val < 1 at this; change i.val = 0; omega
    exact hi ▸ h

/-- The point/point branch rejection is exactly the consistency defect of the
two completed scalar point readouts under the common uniform point question. -/
theorem point_branch_rejection_eq_consistencyDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) =
      consistencyDefect (uniformDistribution
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (fun u answer => heteroKron
          (((points.Q .alice
            (projX (directPointToPauli P u))
            (projZ (directPointToPauli P u))).postprocess fun values =>
              some (directPointToPauli P u (alphaVar P.m) * values.1 +
                directPointToPauli P u (betaVar P.m) * values.2)).effect answer) 1)
        (fun u answer => heteroKron 1
          (((points.Q .bob
            (projX (directPointToPauli P u))
            (projZ (directPointToPauli P u))).postprocess fun values =>
              some (directPointToPauli P u (alphaVar P.m) * values.1 +
                directPointToPauli P u (betaVar P.m) * values.2)).effect answer))
        (pairState setting) := by
  rw [directLdBranchRejectionProbability_point_point_eq]
  calc
    _ = avgOver (uniformDistribution
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (fun u => outcomeEventWeight (strategy lines)
          (directLdPointQuestionOf P.extendedDirectLd u)
          (directLdPointQuestionOf P.extendedDirectLd u)
          (fun answerA answerB => pointGameRead answerA ≠ pointGameRead answerB)) := by
      apply avgOver_congr
      intro u
      simpa [directLdPointQuestionOf, directLdMap] using
        point_rejectedMass_eq_read_mismatch lines
          ⟨u, P.extendedDirectLd.firstIndex, 0⟩
    _ = consistencyDefect (uniformDistribution
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (fun u answer => heteroKron
          ((((answerMeasurement lines .alice
            (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
              pointGameRead).effect answer)) 1)
        (fun u answer => heteroKron 1
          ((((answerMeasurement lines .bob
            (directLdPointQuestionOf P.extendedDirectLd u)).postprocess
              pointGameRead).effect answer)))
        (pairState setting) :=
      (WinImplications.consistencyDefect_postprocess_eq_mismatch
        (uniformDistribution
          (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd))
        (strategy lines)
        (fun u => directLdPointQuestionOf P.extendedDirectLd u)
        (fun u => directLdPointQuestionOf P.extendedDirectLd u)
        (fun _ => pointGameRead) (fun _ => pointGameRead)).symm
    _ = _ := by
      apply consistencyDefect_congr <;> intro u answer
      · rw [show directLdPointQuestionOf P.extendedDirectLd u =
            (.point, directLdMap P.extendedDirectLd .point
              ⟨u, P.extendedDirectLd.firstIndex, 0⟩) by rfl,
          point_read_effect lines .alice]
      · rw [show directLdPointQuestionOf P.extendedDirectLd u =
            (.point, directLdMap P.extendedDirectLd .point
              ⟨u, P.extendedDirectLd.firstIndex, 0⟩) by rfl,
          point_read_effect lines .bob]

/-- The point/point rejection probability of the supplied extended strategy is
bounded by the self-consistency error of its joint point measurements. -/
theorem point_point_rejection_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) ≤ deltaQ := by
  rw [point_branch_rejection_eq_consistencyDefect lines]
  calc
    _ = consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q answer => heteroKron
          (((points.Q .alice q.1.1 q.1.2).postprocess fun values =>
            some (q.2.1 * values.1 + q.2.2 * values.2)).effect answer) 1)
        (fun q answer => heteroKron 1
          (((points.Q .bob q.1.1 q.1.2).postprocess fun values =>
            some (q.2.1 * values.1 + q.2.2 * values.2)).effect answer))
        (pairState setting) := by
      rw [← consistencyDefect_uniform_question_equiv
        (directPointExtendedQuestionEquiv P)]
      apply consistencyDefect_congr <;> intro u answer
      · rw [directPointExtendedQuestionEquiv_apply]
      · rw [directPointExtendedQuestionEquiv_apply]
    _ ≤ consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q values => heteroKron
          ((points.Q .alice q.1.1 q.1.2).effect values) 1)
        (fun q values => heteroKron 1
          ((points.Q .bob q.1.1 q.1.2).effect values))
        (pairState setting) := by
      exact consistencyDefect_dependent_postprocess_le
        (uniformDistribution (ExtendedPointQuestion P))
        (fun q => points.Q .alice q.1.1 q.1.2)
        (fun q => points.Q .bob q.1.1 q.1.2)
        (pairState setting)
        (fun q values => some (q.2.1 * values.1 + q.2.2 * values.2))
    _ = consistencyDefect (uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz values => heteroKron
          ((points.Q .alice xz.1 xz.2).effect values) 1)
        (fun xz values => heteroKron 1
          ((points.Q .bob xz.1 xz.2).effect values))
        (pairState setting) := by
      exact consistencyDefect_uniform_fst
        (X := (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))
        (Y := PauliScalar P × PauliScalar P)
        (Alpha := PauliScalar P × PauliScalar P)
        (IA := setting.ExpandedLocalSpace .alice)
        (IB := setting.ExpandedLocalSpace .bob)
        (fun xz values => (points.Q .alice xz.1 xz.2).effect values)
        (fun xz values => (points.Q .bob xz.1 xz.2).effect values)
        (pairState setting)
    _ = consistencyDefect (uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz values =>
          (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect values)
        (fun xz values =>
          (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect values)
        setting.psiHat := by
      unfold consistencyDefect
      apply avgOver_congr
      intro xz
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · simp [hab]
      · simp only [hab, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
        rw [placedMeasurement_effect, placedMeasurement_effect,
          DistanceCalculus.placed_product_stateQForm_eq]
        apply stateQForm_pairState_eq_AA'_BA''
        · exact (Matrix.nonneg_iff_posSemidef.mp
            ((points.Q .alice xz.1 xz.2).pos a)).isHermitian
        · exact (Matrix.nonneg_iff_posSemidef.mp
            ((points.Q .bob xz.1 xz.2).pos b)).isHermitian
    _ ≤ opFamilyDistSq (uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz values =>
          (setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2)).effect values)
        (fun xz values =>
          (setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)).effect values)
        setting.psiHat := by
      apply consistencyDefect_le_opFamilyDistSq_of_projective
      · intro xz
        exact setting.placedMeasurement_isProjective .AA'
          (points.Q .alice xz.1 xz.2) (points.projective .alice xz.1 xz.2)
      · intro xz
        exact setting.placedMeasurement_isProjective .BA''
          (points.Q .bob xz.1 xz.2) (points.projective .bob xz.1 xz.2)
    _ = opFamilyDistSq (uniformDistribution
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
        (fun xz values =>
          setting.place .AA' ((points.Q .alice xz.1 xz.2).effect values))
        (fun xz values =>
          setting.place .BA'' ((points.Q .bob xz.1 xz.2).effect values))
        setting.psiHat := by
      apply DistanceCalculus.opFamilyDistSq_congr <;> intro xz values
      · exact setting.placedMeasurement_effect .AA'
          (points.Q .alice xz.1 xz.2) values
      · exact setting.placedMeasurement_effect .BA''
          (points.Q .bob xz.1 xz.2) values
    _ ≤ deltaQ := by
      simpa only [Placement.side] using
        points.self_consistent .AA' .BA'' trivial

end ExtendedLineGame

end

end MIPStarRE.QPBT
