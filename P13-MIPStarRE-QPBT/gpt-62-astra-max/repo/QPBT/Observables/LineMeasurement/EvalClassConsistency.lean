module

public import QPBT.Observables.LineMeasurement.BipartiteTransport

/-!
# Consistency of expanded evaluation classes with expanded points

This module proves item 3 of the expanded-line consistency lemma on the four
directed opposite-placement pairs. On each bipartition the distance between
the evaluation classes of the expanded line measurement and the completed
expanded point measurement is at most twice their inconsistency, which by the
overlap identity equals the inconsistency of the strategy's evaluation classes
with its completed point measurement. The trivial bound `4` on the same
distance supplies the large-`ε` case of the common square-root error.

## References

Item 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:540-545`,
blueprint `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Overlaps of the evaluation classes -/

variable (S : ProjectiveSetting P ε) (W : PauliKind) (line : LineDesc P.toLdParams)
  (u : PauliPoint P)

/-- Summed over outcomes, the overlap of Alice's expanded evaluation classes
with Bob's completed expanded point measurement on the expanded state equals
the corresponding overlap of the strategy's own evaluation classes with its
completed point measurement on the strategy state. The ancillary Pauli
projectors cancel because they agree exactly on the EPR pairs. This is the
identity behind `eq:qld-comm-line-pt-cons2`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem sum_stateQForm_evalClass_AA'_BA''_eq :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.lineEvalMeasExp .alice W line u).effect o) *
            S.place .BA'' ((S.pointMeasExpOption .bob W u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  rw [← overlap_AA'_BA''_eq]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : PauliLinePoly P => evalOpt line u f = o),
          DistanceCalculus.stateQForm S.psiHat
            (S.place .AA' (S.expLineOp .alice W line f) *
              S.place .BA'' ((S.pointMeasExpOption .bob W u).effect
                (evalOpt line u f))) := by
      congr 1 with o
      rw [lineEvalMeasExp_effect, place_AA'_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      simp_all
    _ = ∑ f : PauliLinePoly P,
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' (S.expLineOp .alice W line f) *
            S.place .BA'' ((S.pointMeasExpOption .bob W u).effect
              (evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ _ _
    _ = _ := by
      simp_rw [pointMeasExpOption_effect_evalOpt]

/-- The identity of `sum_stateQForm_evalClass_AA'_BA''_eq` with the two
placements exchanged, so that the evaluation classes are carried by the `BA''`
registers and the completed point measurement by `AA'`. This is the symmetric equivalent
of `eq:qld-comm-line-pt-cons2` on the reversed directed pair, paper
`14_analysis_of_the_pauli_basis_test.tex:540-548`. -/
theorem sum_stateQForm_evalClass_BA''_AA'_eq :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.pointMeasExpOption .alice W u).effect o) *
            S.place .BA'' ((S.lineEvalMeasExp .bob W line u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  rw [← overlap_BA''_AA'_eq]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : PauliLinePoly P => evalOpt line u f = o),
          DistanceCalculus.stateQForm S.psiHat
            (S.place .BA'' (S.expLineOp .bob W line f) *
              S.place .AA' ((S.pointMeasExpOption .alice W u).effect
                (evalOpt line u f))) := by
      congr 1 with o
      rw [place_AA'_mul_place_BA''_comm, lineEvalMeasExp_effect,
        place_BA''_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      simp_all
    _ = ∑ f : PauliLinePoly P,
        DistanceCalculus.stateQForm S.psiHat
          (S.place .BA'' (S.expLineOp .bob W line f) *
            S.place .AA' ((S.pointMeasExpOption .alice W u).effect
              (evalOpt line u f))) :=
      Finset.sum_fiberwise Finset.univ _ _
    _ = _ := by
      simp_rw [pointMeasExpOption_effect_evalOpt]

/-! ## Item 3: evaluation classes versus completed expanded points -/

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AA'`--`BA''`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_aaBa_eq :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P))))
        (fun sample a => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.pointMeasExpOption .bob W sample.2)).effect a))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  apply avgOver_congr
  intro sample
  congr 1 with a
  rw [norm_place_AA'_sub_place_BA'']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `AA'`--`BA''`
pair is bounded by twice the strategy's line-point inconsistency. This is
`eq:qld-comm-line-pt-cons2`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. The source reaches it from
`eq:qld-comm-line-pt-cons` through an elementary sub-measurement inequality,
at the cost of a square root, paper
`14_analysis_of_the_pauli_basis_test.tex:598-677`; here it comes directly from
the exact overlap identity together with `fact:agreement`, so the bound is
linear in the error of the strategy. -/
theorem evalClassDist_aaBa_le :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤
      2 * bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.lineEvalMeas .alice W sample.1 sample.2)
        (fun sample => S.pointMeasOption .bob W sample.2)
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (PauliPoint P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  have hμ := linePointDist_isProbability P.toLdParams
  rw [evalClassDist_aaBa_eq]
  refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap hμ
    (fun sample => S.lineEvalMeasExp .alice W sample.1 sample.2) (fun sample =>
      DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointMeasExpOption .bob W sample.2)) (norm_reindexState_psiHat S (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB))).trans (le_of_eq ?_)
  change _ = 2 * consistencyDefect μ
    (fun sample => (DistanceCalculus.leftPlacedMeasurement
     (S.lineEvalMeas .alice W sample.1 sample.2)).effect)
    (fun sample => (DistanceCalculus.rightPlacedMeasurement
     (S.pointMeasOption .bob W sample.2)).effect) S.toStrategy.ψ
  rw [(DistanceCalculus.consistencyDefect_eq_one_sub_overlap
    (fun sample => DistanceCalculus.leftPlacedMeasurement
    (S.lineEvalMeas .alice W sample.1 sample.2))
    (fun sample => DistanceCalculus.rightPlacedMeasurement
    (S.pointMeasOption .bob W sample.2)) hμ S.toStrategy.ψ_norm)]
  congr 2
  apply avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a) *
            S.place .BA'' ((S.pointMeasExpOption .bob W sample.2).effect a)) := by
      congr 1 with a
      apply stateQForm_aaBa_mul_eq
    _ = _ :=
      sum_stateQForm_evalClass_AA'_BA''_eq S W sample.1 sample.2
    _ = _ := by
      congr 1 with a
      exact (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AA'`--`BA''`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_aaBa_le_four :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [evalClassDist_aaBa_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four
    (linePointDist_isProbability P.toLdParams) _ _
    (norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BA''`--`AA'`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_eq :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat =
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => heteroKron ((S.pointMeasExpOption .alice W sample.2).effect a)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P))))
        (fun sample a => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          ((DistanceCalculus.leftPlacedMeasurement
            (ιB := PauliRegister P × PauliRegister P)
            (S.lineEvalMeasExp .bob W sample.1 sample.2)).effect a))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  rw [DistanceCalculus.opFamilyDistSq_symm]
  apply avgOver_congr
  intro sample
  congr 1 with a
  rw [norm_place_AA'_sub_place_BA'']
  rfl

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `BA''`--`AA'`
pair, bounded by twice the interchanged strategy line-point inconsistency.
Paper `14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_le :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤
      2 * bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.pointMeasOption .alice W sample.2)
        (fun sample => S.lineEvalMeas .bob W sample.1 sample.2)
        S.toStrategy.ψ := by
  let X := LineDesc P.toLdParams × (PauliPoint P)
  let R := PauliRegister P
  let μ := linePointDist P.toLdParams
  let B : X → Measurement (Option (PauliScalar P))
      ((S.toStrategy.ιB × R) × (R × R)) := fun sample =>
    DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeasExp .bob W sample.1 sample.2)
  have hμ := linePointDist_isProbability P.toLdParams
  rw [evalClassDist_baAa_eq]
  refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap hμ
    (fun sample => S.pointMeasExpOption .alice W sample.2) B (norm_reindexState_psiHat S (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB))).trans (le_of_eq ?_)
  change _ = 2 * consistencyDefect μ
    (fun sample => (DistanceCalculus.leftPlacedMeasurement
     (S.pointMeasOption .alice W sample.2)).effect)
    (fun sample => (DistanceCalculus.rightPlacedMeasurement
     (S.lineEvalMeas .bob W sample.1 sample.2)).effect) S.toStrategy.ψ
  rw [(DistanceCalculus.consistencyDefect_eq_one_sub_overlap
    (fun sample => DistanceCalculus.leftPlacedMeasurement
    (S.pointMeasOption .alice W sample.2))
    (fun sample => DistanceCalculus.rightPlacedMeasurement
    (S.lineEvalMeas .bob W sample.1 sample.2)) hμ S.toStrategy.ψ_norm)]
  congr 2
  apply avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.pointMeasExpOption .alice W sample.2).effect a) *
            S.place .BA'' ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a)) := by
      congr 1 with a
      apply stateQForm_aaBa_mul_eq
    _ = _ :=
      sum_stateQForm_evalClass_BA''_AA'_eq S W sample.1 sample.2
    _ = _ := by
      congr 1 with a
      exact (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BA''`--`AA'`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_le_four :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [evalClassDist_baAa_eq]
  exact DistanceCalculus.opFamilyDistSq_placed_le_four
    (linePointDist_isProbability P.toLdParams) _ _
    (norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `AB''`--`BB'`
pair. Paper `14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_le :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤
      2 * bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.lineEvalMeas .alice W sample.1 sample.2)
        (fun sample => S.pointMeasOption .bob W sample.2)
        S.toStrategy.ψ := by
  have h := evalClassDist_aaBa_le S W
  simpa only [opFamilyDistSq, opposite_place_norm_sub_eq] using h

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AB''`--`BB'`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_le_four :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤ 4 := by
  have h := evalClassDist_aaBa_le_four S W
  simpa only [opFamilyDistSq, opposite_place_norm_sub_eq] using h

set_option synthInstance.maxSize 400 in
/-- Expanded evaluation-class consistency on the directed `BB'`--`AB''`
pair. Paper `14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_le :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤
      2 * bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.pointMeasOption .alice W sample.2)
        (fun sample => S.lineEvalMeas .bob W sample.1 sample.2)
        S.toStrategy.ψ := by
  have h := evalClassDist_baAa_le S W
  rw [DistanceCalculus.opFamilyDistSq_symm] at h ⊢
  simpa only [opFamilyDistSq, opposite_place_norm_sub_eq] using h

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BB'`--`AB''`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_le_four :
    opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤ 4 := by
  have h := evalClassDist_baAa_le_four S W
  rw [DistanceCalculus.opFamilyDistSq_symm] at h ⊢
  simpa only [opFamilyDistSq, opposite_place_norm_sub_eq] using h

end ProjectiveSetting

end

end MIPStarRE.QPBT
