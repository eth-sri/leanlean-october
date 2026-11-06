module

public import QPBT.Combining.ExtendedLineGame.MixedLinePointRejection
public import QPBT.Combining.Points.Placement

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


namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

@[simp] theorem piCongrLeft_const_apply
    {I J K : Type*} (e : I ≃ J) (f : I → K) (j : J) :
    (e.piCongrLeft fun _ => K) f j = f (e.symm j) := by
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]

/-- Split a direct extended point into its two Pauli points and two scalar
coordinates.  This is a single bijection, so uniformity is joint rather than
an inference from four separate marginals. -/
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
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) (Prod.ext ?_ ?_) <;>
    exact (piCongrLeft_const_apply _ _ _).trans rfl

/-- Question-dependent coarse-graining on opposite tensor factors cannot
increase their consistency defect. -/
theorem consistencyDefect_dependent_postprocess_le
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
  apply avgOver_mono
  intro x
  have h := consistencyDefect_postprocess_le (uniformDistribution Unit)
    (fun _ => A x) (fun _ => B x) psi (f x)
  unfold consistencyDefect at h
  simpa only [avgOver_uniform_const] using h

/-- A jointly uniform auxiliary coordinate can be discarded when both
operator families depend only on the first coordinate. -/
theorem consistencyDefect_uniform_fst
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
  let f := fun x =>
    ∑ a : Alpha, ∑ b : Alpha,
      if a = b then 0 else
        (inner ℂ psi ((EuclideanSpace.equiv (IA × IB) ℂ).symm
          ((heteroKron (A x a) 1 * heteroKron 1 (B x b)).mulVec psi))).re
  exact avgOver_uniform_fst f

theorem point_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (valuesA valuesB : Fin P.extendedDirectLd.k →
      DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.pointVals valuesA) (.pointVals valuesB) = true ↔
      pointGameRead (.pointVals valuesA) = pointGameRead (.pointVals valuesB) := by
  simp only [directLdWinPredicate, validDirectLdAnswer,
    Bool.and_self, ite_true, decide_eq_true_eq, pointGameRead, Option.some.injEq,
    (extendedDirectScalarEquiv P).injective.eq_iff, funext_iff]
  exact ⟨fun h => h _, fun h i => (Fin.fin_one_eq_zero i).symm ▸ h⟩

variable (lines : ExtendedLinesWitness setting points deltaL)

theorem point_rejectedMass_eq_read_mismatch
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => pointGameRead answerA ≠ pointGameRead answerB) :=
  rejectedMass_eq_mismatch_of lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
    exact point_point_win_iff_read_eq sample _ _

/-- The point/point branch rejection is exactly the consistency defect of the
two completed scalar point readouts under the common uniform point question. -/
theorem point_branch_rejection_eq_consistencyDefect
    :
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
  refine ((avgOver_congr _ _ _ fun u => point_rejectedMass_eq_read_mismatch lines
    ⟨u, P.extendedDirectLd.firstIndex, 0⟩).trans
    (WinImplications.consistencyDefect_postprocess_eq_mismatch _ (strategy lines)
      (directLdPointQuestionOf P.extendedDirectLd) (directLdPointQuestionOf P.extendedDirectLd)
      (fun _ => pointGameRead) (fun _ => pointGameRead)).symm).trans ?_
  exact consistencyDefect_congr _ _ _ _ _ _
    (fun u a => congrArg (heteroKron · 1) (point_read_effect lines .alice ⟨u, P.extendedDirectLd.firstIndex, 0⟩ a))
    (fun u a => congrArg (heteroKron 1) (point_read_effect lines .bob ⟨u, P.extendedDirectLd.firstIndex, 0⟩ a))

/-- The point/point rejection probability of the supplied extended strategy is
bounded by the self-consistency error of its joint point measurements. -/
theorem point_point_rejection_le
    :
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
      rw [← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
      apply consistencyDefect_congr <;> intro u answer <;> rw [directPointExtendedQuestionEquiv_apply]
    _ ≤ consistencyDefect (uniformDistribution (ExtendedPointQuestion P))
        (fun q values => heteroKron ((points.Q .alice q.1.1 q.1.2).effect values) 1)
        (fun q values => heteroKron 1 ((points.Q .bob q.1.1 q.1.2).effect values))
        (pairState setting) :=
      consistencyDefect_dependent_postprocess_le (uniformDistribution (ExtendedPointQuestion P))
        (fun q => points.Q .alice q.1.1 q.1.2) (fun q => points.Q .bob q.1.1 q.1.2)
        (pairState setting) fun q values => some (q.2.1 * values.1 + q.2.2 * values.2)
    _ = _ := consistencyDefect_uniform_fst
      (X := (Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))
      (Y := PauliScalar P × PauliScalar P)
      (fun xz values => (points.Q .alice xz.1 xz.2).effect values)
      (fun xz values => (points.Q .bob xz.1 xz.2).effect values) (pairState setting)
    _ = _ := (placed_consistency_pairState setting
      (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) (fun xz => points.Q .alice xz.1 xz.2)
      (fun xz => points.Q .bob xz.1 xz.2)).1.symm
    _ ≤ _ := consistencyDefect_le_opFamilyDistSq_of_projective
      (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz => setting.placedMeasurement .AA' (points.Q .alice xz.1 xz.2))
      (fun xz => setting.placedMeasurement .BA'' (points.Q .bob xz.1 xz.2)) setting.psiHat
      (fun xz => setting.placedMeasurement_isProjective .AA' _ (points.projective .alice xz.1 xz.2))
      (fun xz => setting.placedMeasurement_isProjective .BA'' _ (points.projective .bob xz.1 xz.2))
    _ ≤ deltaQ := points.self_consistent .AA' .BA'' trivial

end ExtendedLineGame

end

end MIPStarRE.QPBT
