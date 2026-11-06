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

namespace DistanceCalculus

/-- Two oppositely placed complete measurement families whose diagonal overlap
agrees with that of another such pair are at distance at most twice the
inconsistency of the other pair, and at most `4`. This is `fact:agreement`
combined with the overlap form of the consistency defect. -/
theorem opFamilyDistSq_placed_le_min {X α ιA ιB κA κB : Type*} [Fintype X] [DecidableEq X]
    [Fintype α] [DecidableEq α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A : X → MIPStarRE.Quantum.Measurement α ιA) (B : X → MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (A₀ : X → MIPStarRE.Quantum.Measurement α κA) (B₀ : X → MIPStarRE.Quantum.Measurement α κB)
    (φ : EuclideanSpace ℂ (κA × κB)) (hφ : ‖φ‖ = 1)
    (h : ∀ x, ∑ a, stateQForm ψ (heteroKron ((A x).effect a) 1 * heteroKron 1 ((B x).effect a)) =
      ∑ a, stateQForm φ (heteroKron ((A₀ x).effect a) ((B₀ x).effect a))) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤
      min (2 * consistencyDefect μ (fun x a => heteroKron ((A₀ x).effect a) 1)
        (fun x a => heteroKron 1 ((B₀ x).effect a)) φ) 4 := by
  refine le_min ((opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ).trans_eq
    (congrArg (2 * ·) ((consistencyDefect_eq_one_sub_overlap μ (fun x => leftPlacedMeasurement
      (A x)) (fun x => rightPlacedMeasurement (B x)) ψ hμ hψ).trans (.trans ?_
      (consistencyDefect_eq_one_sub_overlap μ (fun x => leftPlacedMeasurement (A₀ x))
        (fun x => rightPlacedMeasurement (B₀ x)) φ hμ hφ).symm))))
    (opFamilyDistSq_placed_le_four μ hμ A B ψ hψ)
  exact congrArg (1 - ·) (avgOver_congr _ _ _ fun x => (h x).trans
    (Finset.sum_congr rfl fun a _ => (placed_product_stateQForm_eq _ _ _).symm))

end DistanceCalculus

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Overlaps of the evaluation classes -/

variable (S : ProjectiveSetting P ε) (W : PauliKind)

/-- Summed over outcomes, the overlap of Alice's expanded evaluation classes
with Bob's completed expanded point measurement on the expanded state equals
the corresponding overlap of the strategy's own evaluation classes with its
completed point measurement on the strategy state. The ancillary Pauli
projectors cancel because they agree exactly on the EPR pairs. This is the
identity behind `eq:qld-comm-line-pt-cons2`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem sum_stateQForm_evalClass_AA'_BA''_eq (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.lineEvalMeasExp .alice W line u).effect o) *
            S.place .BA'' ((S.pointMeasExpOption .bob W u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) :=
  overlap_identity P W (S.lineMeas .alice W line) (S.pointMeas .bob W u)
    (fun A B => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B)) line u S.psiHat
    (S.place .AA') (S.place .BA'') (S.place_finset_sum .AA') (S.place_finset_sum .BA'')
    (S.expLineOp .alice W line) (fun _ => rfl) _ (S.pointMeasExpOption_effect_eq_elim .bob W u)
    (fun hu f' f'' b' b'' => (stateQForm_place_AA'_mul_BA''_two S _ _ _ _
      (IsSelfAdjoint.of_nonneg ((S.lineMeas .alice W line).pos f')) (IsSelfAdjoint.of_nonneg ((S.pointMeas .bob W u).pos b'))
      (IsSelfAdjoint.of_nonneg (tauLineProj_nonneg P W line f'')) (IsSelfAdjoint.of_nonneg (tauPointProj_nonneg W u b''))).trans
      (by rw [stateQForm_eprState_tauLineProj_tauPointProj P W line u hu f'' b'']))
    (fun s A B => by simp [DistanceCalculus.heteroKron_finset_sum_left,
      DistanceCalculus.stateQForm_finset_sum]) (fun A => by simp [heteroKron_zero_right, DistanceCalculus.stateQForm_zero])

/-- The identity of `sum_stateQForm_evalClass_AA'_BA''_eq` with the two
placements exchanged, so that the evaluation classes are carried by the `BA''`
registers and the completed point measurement by `AA'`. This is the symmetric equivalent
of `eq:qld-comm-line-pt-cons2` on the reversed directed pair, paper
`14_analysis_of_the_pauli_basis_test.tex:540-548`. -/
theorem sum_stateQForm_evalClass_BA''_AA'_eq (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.pointMeasExpOption .alice W u).effect o) *
            S.place .BA'' ((S.lineEvalMeasExp .bob W line u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  simp only [place_AA'_mul_place_BA''_comm S]
  exact overlap_identity P W (S.lineMeas .bob W line) (S.pointMeas .alice W u)
    (fun A B => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron B A)) line u S.psiHat
    (S.place .BA'') (S.place .AA') (S.place_finset_sum .BA'') (S.place_finset_sum .AA')
    (S.expLineOp .bob W line) (fun _ => rfl) _ (S.pointMeasExpOption_effect_eq_elim .alice W u)
    (fun hu f' f'' b' b'' => (congrArg _ (place_AA'_mul_place_BA''_comm S _ _).symm).trans
      ((stateQForm_place_AA'_mul_BA''_two S _ _ _ _
      (IsSelfAdjoint.of_nonneg ((S.pointMeas .alice W u).pos b')) (IsSelfAdjoint.of_nonneg ((S.lineMeas .bob W line).pos f'))
      (IsSelfAdjoint.of_nonneg (tauPointProj_nonneg W u b'')) (IsSelfAdjoint.of_nonneg (tauLineProj_nonneg P W line f''))).trans
      (by rw [stateQForm_eprState_tauPointProj_tauLineProj P W line u hu f'' b''])))
    (fun s A B => by simp [DistanceCalculus.heteroKron_finset_sum_right,
      DistanceCalculus.stateQForm_finset_sum]) (fun A => by simp [heteroKron_zero_left, DistanceCalculus.stateQForm_zero])

/-- The identity of `sum_stateQForm_evalClass_AA'_BA''_eq` on the second
bipartition: summed over outcomes, the overlap of Alice's expanded evaluation
classes on `AB''` with Bob's completed expanded point measurement on `BB'`
equals the corresponding strategy overlap. -/
theorem sum_stateQForm_evalClass_AB''_BB'_eq (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' ((S.lineEvalMeasExp .alice W line u).effect o) *
            S.place .BB' ((S.pointMeasExpOption .bob W u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) :=
  overlap_identity P W (S.lineMeas .alice W line) (S.pointMeas .bob W u)
    (fun A B => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B)) line u S.psiHat
    (S.place .AB'') (S.place .BB') (S.place_finset_sum .AB'') (S.place_finset_sum .BB')
    (S.expLineOp .alice W line) (fun _ => rfl) _ (S.pointMeasExpOption_effect_eq_elim .bob W u)
    (fun hu f' f'' b' b'' => (stateQForm_place_AB''_mul_BB'_two S _ _ _ _
      (IsSelfAdjoint.of_nonneg ((S.lineMeas .alice W line).pos f')) (IsSelfAdjoint.of_nonneg ((S.pointMeas .bob W u).pos b'))
      (IsSelfAdjoint.of_nonneg (tauLineProj_nonneg P W line f'')) (IsSelfAdjoint.of_nonneg (tauPointProj_nonneg W u b''))).trans
      (by rw [stateQForm_eprState_tauPointProj_tauLineProj P W line u hu f'' b'']))
    (fun s A B => by simp [DistanceCalculus.heteroKron_finset_sum_left,
      DistanceCalculus.stateQForm_finset_sum]) (fun A => by simp [heteroKron_zero_right, DistanceCalculus.stateQForm_zero])

/-- The identity of `sum_stateQForm_evalClass_AB''_BB'_eq` with the two
placements exchanged, so that the completed point measurement is carried by
`AB''` and the evaluation classes by `BB'`. -/
theorem sum_stateQForm_evalClass_BB'_AB''_eq (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AB'' ((S.pointMeasExpOption .alice W u).effect o) *
            S.place .BB' ((S.lineEvalMeasExp .bob W line u).effect o)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  simp only [place_AB''_mul_place_BB'_comm S]
  exact overlap_identity P W (S.lineMeas .bob W line) (S.pointMeas .alice W u)
    (fun A B => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron B A)) line u S.psiHat
    (S.place .BB') (S.place .AB'') (S.place_finset_sum .BB') (S.place_finset_sum .AB'')
    (S.expLineOp .bob W line) (fun _ => rfl) _ (S.pointMeasExpOption_effect_eq_elim .alice W u)
    (fun hu f' f'' b' b'' => (congrArg _ (place_AB''_mul_place_BB'_comm S _ _).symm).trans
      ((stateQForm_place_AB''_mul_BB'_two S _ _ _ _
      (IsSelfAdjoint.of_nonneg ((S.pointMeas .alice W u).pos b')) (IsSelfAdjoint.of_nonneg ((S.lineMeas .bob W line).pos f'))
      (IsSelfAdjoint.of_nonneg (tauPointProj_nonneg W u b'')) (IsSelfAdjoint.of_nonneg (tauLineProj_nonneg P W line f''))).trans
      (by rw [stateQForm_eprState_tauLineProj_tauPointProj P W line u hu f'' b''])))
    (fun s A B => by simp [DistanceCalculus.heteroKron_finset_sum_right,
      DistanceCalculus.stateQForm_finset_sum]) (fun A => by simp [heteroKron_zero_left, DistanceCalculus.stateQForm_zero])


end ProjectiveSetting

end

end MIPStarRE.QPBT
