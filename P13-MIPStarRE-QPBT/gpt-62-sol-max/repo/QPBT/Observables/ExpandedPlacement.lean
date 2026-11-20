module

public import QPBT.Observables.ExpandedDefs
public import QPBT.Games.DistanceTheorems.TensorState
public import QPBT.Observables.WinImplications.InterchangedCommutation
public import QPBT.Games.EPR

/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Coordinate tensors -/

namespace ProjectiveSetting

/-- The diagonal overlap of the two Pauli point measurements on an EPR pair is
one. Thus the ancillary measurement contributes no consistency defect. This is
the perfect ancillary consistency in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem sum_tauPointProj_pair_stateQForm_eprState {P : AdmissibleParams}
    (W : PauliKind) (u : PauliPoint P) :
    ∑ a : PauliScalar P,
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauPointProj W u a) (tauPointProj W u a)) = 1 := by
  simp_rw [stateQForm_eprState_heteroKron _ _ (tauPointProj_transpose W u _),
    tauPointProj_mul_tauPointProj]
  exact sum_stateQForm_eprState_left _ (tauPointMeas W u).sum_eq_one

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/

section

variable (S : ProjectiveSetting P ε)
include S

/-- Place a strategy-local operator on the player side that supplies the local
space of a register placement. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
noncomputable def placeStrategySide :
    (side : PlayerSide) → Op (S.LocalSpace side) →
      Op (S.toStrategy.ιA × S.toStrategy.ιB)
  | .alice, T => heteroKron T 1
  | .bob, T => heteroKron 1 T

/-- Place a local operator on the selected EPR pair and the given player's original register. -/
abbrev placeOnEpr (first : Bool) :
    (side : PlayerSide) → Op (S.ExpandedLocalSpace side) → Op S.ExpandedSpace
  | .alice, O => if first then S.place .AA' O else S.place .AB'' O
  | .bob, O => if first then S.place .BA'' O else S.place .BB' O

/-- The placement of a difference is the difference of the placements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_sub (p : Placement)
    (O₁ O₂ : Op (S.ExpandedLocalSpace p.side)) :
    S.place p (O₁ - O₂) = S.place p O₁ - S.place p O₂ := map_sub (S.placeLinear p) _ _

end

/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : ProjectiveSetting P ε) :
    S.psiHat = reindexState (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (vecTensor (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))
        (eprState (PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [psiHat_eq_reindexState, reindexState_norm_eq, vecTensor_norm_eq,
    vecTensor_norm_eq, S.toStrategy.ψ_norm, eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/

section

variable (S : ProjectiveSetting P ε)
include S

/-- Under the `AA' | BA''(B'B'')` bipartition, an `AA'` placement is the
ordinary left tensor placement. -/
theorem reindexOp_aaBaBipartition_left
    (O : Op (S.ExpandedLocalSpace .alice)) :
    reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) =
      S.place .AA' O := rfl

/-- Under the `AA' | BA''(B'B'')` bipartition, a `BA''` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_aaBaBipartition_right
    (O : Op (S.ExpandedLocalSpace .bob)) :
    reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place .BA'' O := by
  rw [place_eq_reindex, placeSplit, reindexOp_trans, reindexOp_swapPaired_heteroKron_one]

/-- Under the `AB'' | BB'(A'A'')` bipartition, an `AB''` placement is the
ordinary left tensor placement. -/
theorem reindexOp_abBbBipartition_left
    (O : Op (S.ExpandedLocalSpace .alice)) :
    reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) =
      S.place .AB'' O := rfl

/-- Under the `AB'' | BB'(A'A'')` bipartition, a `BB'` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_abBbBipartition_right
    (O : Op (S.ExpandedLocalSpace .bob)) :
    reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place .BB' O := by
  rw [place_eq_reindex, placeSplit, reindexOp_trans, reindexOp_swapPaired_heteroKron_one]

end

end ProjectiveSetting

section

variable {I : Type*} [DecidableEq I] (p : Placement) (V : Op I)
include I p V

/-- The operator induced on each EPR pair by a factorized local placement. -/
def Placement.firstEpr : Op (I × I) :=
  match p with
  | .AA' => heteroKron V 1
  | .BA'' => heteroKron 1 V
  | _ => heteroKron (1 : Op I) 1

def Placement.secondEpr : Op (I × I) :=
  match p with
  | .BB' => heteroKron V 1
  | .AB'' => heteroKron 1 V
  | _ => heteroKron (1 : Op I) 1

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

section

variable (S : ProjectiveSetting P ε)
include S

/-- Unshuffle a factorized placement into its strategy and two ancillary factors. -/
theorem reindexOp_sixRegShuffle_place (p : Placement)
    (A : Op (S.LocalSpace p.side)) (V : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB) (S.place p (heteroKron A V)) =
      heteroKron (heteroKron (S.placeStrategySide p.side A) (p.firstEpr V)) (p.secondEpr V) := by
  rw [place_eq_reindex, ← reindexOp_trans]
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  cases p <;> simp [placeSplit, aaBaBipartition, abBbBipartition, swapPaired,
    reindexOp, sixRegShuffle, heteroKron, Matrix.kronecker, Matrix.one_apply, Prod.ext_iff,
    placeStrategySide, Placement.side, Placement.firstEpr, Placement.secondEpr,
    ite_and, mul_ite, ite_mul] <;> split_ifs <;> ac_rfl

/-- Expectations on the expanded state factor when the unshuffled ancillas factor. -/
theorem stateQForm_psiHat_of_reindex {M}
    {A : Op (S.toStrategy.ιA × S.toStrategy.ιB)} {B C : Op (PauliRegister P × PauliRegister P)}
    (he : reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB) M =
      heteroKron (heteroKron A B) C) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    stateQForm S.psiHat M = stateQForm S.toStrategy.ψ A *
      stateQForm (eprState (PauliRegister P)) B * stateQForm (eprState (PauliRegister P)) C := by
  rw [psiHat_eq_reindexState, stateQForm_reindexState, he,
    stateQForm_vecTensor_right_hermitian _ _ _ _ hC,
    stateQForm_vecTensor_right_hermitian _ _ _ _ hB]

/-- The product of the two placements has one active EPR factor. -/
theorem stateQForm_placeOnEpr_mul (first : Bool)
    (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T U : Op (PauliRegister P)) (hT : T.IsHermitian) (hU : U.IsHermitian) :
    stateQForm S.psiHat
        (S.placeOnEpr first .alice (heteroKron A T) * S.placeOnEpr first .bob (heteroKron B U)) =
      stateQForm S.toStrategy.ψ (heteroKron A B) *
        stateQForm (eprState (PauliRegister P)) (if first then heteroKron T U else heteroKron U T) := by
  let V := if first then heteroKron T U else heteroKron U T
  have hV : V.IsHermitian := by
    cases first
    · exact heteroKron_isHermitian hU hT
    · exact heteroKron_isHermitian hT hU
  have h := S.stateQForm_psiHat_of_reindex (B := if first then V else 1) (C := if first then 1 else V)
    (A := heteroKron A B)
    (M := S.placeOnEpr first .alice (heteroKron A T) * S.placeOnEpr first .bob (heteroKron B U))
    (by cases first <;> simp [V, placeOnEpr, reindexOp_mul, S.reindexOp_sixRegShuffle_place,
      placeStrategySide, Placement.side, Placement.firstEpr, Placement.secondEpr,
      heteroKron_mul, heteroKron_one_one])
    (by split <;> first | exact hV | exact Matrix.isHermitian_one)
    (by split <;> first | exact hV | exact Matrix.isHermitian_one)
  cases first <;> simpa [V, stateQForm_one, eprState_norm, mul_assoc] using h

/-- An isometric ancillary factor does not change the norm of a placed action. -/
theorem norm_place_heteroKron_psiHat
    (p : Placement) (T : Op (S.LocalSpace p.side)) (V : Op (PauliRegister P))
    (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place p (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState (S.placeStrategySide p.side T) S.toStrategy.ψ‖ := by
  rw [psiHat_eq_reindexState, norm_applyOperatorToState_reindexState,
    reindexOp_sixRegShuffle_place]
  rw [applyOperatorToState_heteroKron_vecTensor, applyOperatorToState_heteroKron_vecTensor,
    vecTensor_norm_eq, vecTensor_norm_eq]
  have l := MagicSquareRigidity.norm_applyOperatorToState_of_isometry
    (WinImplications.heteroKron_left_isometry (ιB := PauliRegister P) V hV)
      (eprState (PauliRegister P))
  have r := MagicSquareRigidity.norm_applyOperatorToState_of_isometry
    (WinImplications.heteroKron_right_isometry (ιA := PauliRegister P) V hV)
      (eprState (PauliRegister P))
  cases p <;> simp only [Placement.firstEpr, Placement.secondEpr, heteroKron_one_one,
    applyOperatorToState_one, l, r, eprState_norm, mul_one]

end

end ProjectiveSetting

end

end MIPStarRE.QPBT
