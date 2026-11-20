module

public import QPBT.Observables.ExpandedDefs
public import QPBT.Observables.WinImplications.InterchangedCommutation
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables

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
open MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/

section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A : Op ι)
  (B : Op κ) (u x : EuclideanSpace ℂ ι) (v y : EuclideanSpace ℂ κ)

/-- A Kronecker product of operators acts factorwise on a coordinate tensor.
Formalization-only support for `def:expanded-state`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem applyOperatorToState_heteroKron_vecTensor :
    applyOperatorToState (heteroKron A B) (vecTensor u v) =
      vecTensor (applyOperatorToState A u) (applyOperatorToState B v) := by
  classical
  ext p
  obtain ⟨i, j⟩ := p
  change (Matrix.mulVec (heteroKron A B) (vecTensor u v).ofLp) (i, j) =
    (Matrix.mulVec A u.ofLp) i * (Matrix.mulVec B v.ofLp) j
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  change A i k * B j l * (u.ofLp k * v.ofLp l) =
    _
  ring

/-- The inner product of coordinate tensors is the product of the factor
inner products. Formalization-only support for the EPR product calculation in
`lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem inner_vecTensor :
    inner ℂ (vecTensor u v) (vecTensor x y) = inner ℂ u x * inner ℂ v y := by
  change (∑ p : ι × κ,
      (x.ofLp p.1 * y.ofLp p.2) * star (u.ofLp p.1 * v.ofLp p.2)) =
    (∑ i : ι, x.ofLp i * star (u.ofLp i)) *
      ∑ j : κ, y.ofLp j * star (v.ofLp j)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  congr 1 with i
  rw [Finset.mul_sum]
  congr 1 with j
  simp
  ring

/-- A Hermitian Kronecker product evaluated on a coordinate tensor factors as
the product of the two real quadratic forms. Formalization-only support for
the EPR product calculation in `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem stateQForm_vecTensor_heteroKron
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    DistanceCalculus.stateQForm (vecTensor u v) (heteroKron A B) =
      DistanceCalculus.stateQForm u A * DistanceCalculus.stateQForm v B := by
  unfold DistanceCalculus.stateQForm
  rw [applyOperatorToState_heteroKron_vecTensor, inner_vecTensor]
  have himA : (inner ℂ u (applyOperatorToState A u)).im = 0 := ((Matrix.isSymmetric_toEuclideanLin_iff).mpr hA).im_inner_self_apply u
  aesop

end

/-- Kronecker products preserve Hermiticity. -/
theorem heteroKron_isHermitian {ι κ : Type*} {A : Op ι} {B : Op κ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (heteroKron A B).IsHermitian := by
  simp [Matrix.IsHermitian, heteroKron, Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

namespace ProjectiveSetting

section

variable {P : AdmissibleParams} (W : PauliKind) (u : PauliPoint P)

/-- The diagonal overlap of the two Pauli point measurements on an EPR pair is
one. Thus the ancillary measurement contributes no consistency defect. This is
the perfect ancillary consistency in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem sum_tauPointProj_pair_stateQForm_eprState :
    ∑ a : PauliScalar P,
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauPointProj W u a) (tauPointProj W u a)) = 1 := by
  have hterm (a : PauliScalar P) :
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauPointProj W u a) (tauPointProj W u a)) =
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauPointProj W u a) 1) := by
    unfold DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [applyOperatorToState] using
      congrFun ((by
                  let T := tauPointProj W u a
                  have hfactor : heteroKron T T = heteroKron T 1 * heteroKron 1 T := by
                    simp [heteroKron_mul]
                  rw [hfactor, ← Matrix.mulVec_mulVec,
                    ← epr_action_eq_of_transpose (tauPointProj_transpose W u a),
                    Matrix.mulVec_mulVec, heteroKron_mul, Matrix.mul_one,
                    tauPointProj_mul_tauPointProj, if_pos rfl])) p
  simp_rw [hterm]
  have hsumop :
      (∑ a : PauliScalar P,
          heteroKron (tauPointProj W u a) 1) =
        heteroKron (∑ a : PauliScalar P, tauPointProj W u a)
          (1 : Op (PauliRegister P)) := by
    ext i j
    simp [heteroKron, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.sum_apply, Finset.sum_mul]
  have htausum : ∑ a : PauliScalar P, tauPointProj W u a = 1 :=
    (tauPointMeas W u).sum_eq_one
  rw [← show DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (∑ a : PauliScalar P,
        heteroKron (tauPointProj W u a) 1) =
        ∑ a : PauliScalar P,
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauPointProj W u a) (1 : Op (PauliRegister P))) by
    simp [DistanceCalculus.stateQForm, applyOperatorToState]]
  simp_all [DistanceCalculus.stateQForm, heteroKron_one_one, WinImplications.applyOperatorToState_one, eprState_norm]

end

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/

/-- Place a strategy-local operator on the player side that supplies the local
space of a register placement. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
noncomputable def placeStrategySide (S : ProjectiveSetting P ε) :
    (side : PlayerSide) → Op (S.LocalSpace side) →
      Op (S.toStrategy.ιA × S.toStrategy.ιB)
  | .alice, T => heteroKron T 1
  | .bob, T => heteroKron 1 T

/-- The placement of a difference is the difference of the placements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem place_sub (S : ProjectiveSetting P ε) (p : Placement)
    (O₁ O₂ : Op (S.ExpandedLocalSpace p.side)) :
    S.place p (O₁ - O₂) = S.place p O₁ - S.place p O₂ := by
  ext i j
  cases p <;> simp only [place, Matrix.sub_apply, sub_mul, mul_sub]

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
  simp [psiHat_eq_reindexState, reindexState_norm_eq, vecTensor_norm_eq, S.toStrategy.ψ_norm, eprState_norm]

/-! ## Opposite-placement bipartitions -/

section

variable (P : AdmissibleParams) (ιA ιB : Type*)

/-- Regroup `AA'A''BB'B''` as `AA' | BA''(B'B'')`. This is the tensor
bipartition used for data processing on the `AA'`--`BA''` placement pair in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
def aaBaBipartition :
    SixReg P ιA ιB ≃
      (ιA × PauliRegister P) ×
        ((ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)) where
  toFun p := ((p.1.1, p.1.2.1), ((p.2.1, p.1.2.2), (p.2.2.1, p.2.2.2)))
  invFun p := ((p.1.1, (p.1.2, p.2.1.2)),
    (p.2.1.1, (p.2.2.1, p.2.2.2)))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Regroup `AA'A''BB'B''` as `AB'' | BB'(A'A'')`. This is the tensor
bipartition used for data processing on the `AB''`--`BB'` placement pair in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
def abBbBipartition :
    SixReg P ιA ιB ≃
      (ιA × PauliRegister P) ×
        ((ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)) where
  toFun p := ((p.1.1, p.2.2.2), ((p.2.1, p.2.2.1), (p.1.2.1, p.1.2.2)))
  invFun p := ((p.1.1, (p.2.2.1, p.2.2.2)),
    (p.2.1.1, (p.2.1.2, p.1.2)))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

end

/-- Under the `AA' | BA''(B'B'')` bipartition, an `AA'` placement is the
ordinary left tensor placement. -/
theorem reindexOp_aaBaBipartition_left (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .alice)) :
    reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) =
      S.place .AA' O := by
  ext i j
  simp [reindexOp, aaBaBipartition, place, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, LocalSpace, Prod.ext_iff]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-- Under the `AA' | BA''(B'B'')` bipartition, a `BA''` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_aaBaBipartition_right (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .bob)) :
    reindexOp (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place .BA'' O := by
  ext i j
  simp [reindexOp, aaBaBipartition, place, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, LocalSpace, Prod.ext_iff]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-- Under the `AB'' | BB'(A'A'')` bipartition, an `AB''` placement is the
ordinary left tensor placement. -/
theorem reindexOp_abBbBipartition_left (S : ProjectiveSetting P ε)
    (O : Op (S.ExpandedLocalSpace .alice)) :
    reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron O
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P)))) =
      S.place .AB'' O := by
  ext i j
  simp [reindexOp, abBbBipartition, place, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, LocalSpace, Prod.ext_iff]
  split_ifs
  all_goals simp_all
  all_goals rfl

section

variable (S : ProjectiveSetting P ε) (A T : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
  (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1)

/-- Under the `AB'' | BB'(A'A'')` bipartition, a `BB'` placement is the
ordinary right tensor placement, with identity on the unused EPR pair. -/
theorem reindexOp_abBbBipartition_right
    (O : Op (S.ExpandedLocalSpace .bob)) :
    reindexOp (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
        (heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place .BB' O := by
  ext i j
  simp [reindexOp, abBbBipartition, place, heteroKron, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, LocalSpace, Prod.ext_iff]
  split_ifs
  all_goals simp_all
  all_goals rfl

/-! ## The four placements -/

/-- The two opposite bipartitions differ only by interchanging the identical
EPR pairs and flipping one pair. Both induce the same regrouped state. -/
theorem reindexState_abBb_eq_aaBa (S : ProjectiveSetting P ε) :
    reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat =
    reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB) S.psiHat := by
  ext p
  let R := PauliRegister P
  have h := congrArg (fun v : _ => v (p.1.2, p.2.1.2))
    (reindexState_prodComm_eprState R)
  change eprState R (p.2.1.2, p.1.2) = _ at h
  change (S.toStrategy.ψ (p.1.1, p.2.1.1) * eprState R p.2.2) * eprState R (p.2.1.2, p.1.2) =
    (S.toStrategy.ψ (p.1.1, p.2.1.1) * eprState R (p.1.2, p.2.1.2)) * eprState R p.2.2
  rw [h, mul_right_comm]

theorem opposite_place_norm_sub_eq (S : ProjectiveSetting P ε)
    (A : Op (S.ExpandedLocalSpace .alice)) (B : Op (S.ExpandedLocalSpace .bob)) :
    ‖applyOperatorToState (S.place .AB'' A - S.place .BB' B) S.psiHat‖ =
    ‖applyOperatorToState (S.place .AA' A - S.place .BA'' B) S.psiHat‖ := by
  have h := congrArg (fun ψ : _ => ‖applyOperatorToState (heteroKron A 1 - heteroKron 1 (heteroKron B 1)) ψ‖)
    (reindexState_abBb_eq_aaBa S)
  simpa only [WinImplications.norm_applyOperatorToState_reindexState, WinImplications.reindexOp_sub,
    reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right,
    reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right] using h

theorem opposite_place_qform_mul_eq (S : ProjectiveSetting P ε)
    (A : Op (S.ExpandedLocalSpace .alice)) (B : Op (S.ExpandedLocalSpace .bob)) :
    DistanceCalculus.stateQForm S.psiHat (S.place .AB'' A * S.place .BB' B) =
    DistanceCalculus.stateQForm S.psiHat (S.place .AA' A * S.place .BA'' B) := by
  have h := congrArg (fun ψ : _ => DistanceCalculus.stateQForm ψ (heteroKron A 1 * heteroKron 1 (heteroKron B 1)))
    (reindexState_abBb_eq_aaBa S)
  simpa only [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
    reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right,
    reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right] using h

/-- The `AA'` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_AA'_heteroKron :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AA' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron T (1 : Op S.toStrategy.ιB))
          (heteroKron V (1 : Op (PauliRegister P))))
        (heteroKron (1 : Op (PauliRegister P))
          (1 : Op (PauliRegister P))) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring

/-- The `BA''` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_BA''_heteroKron (T : Op S.toStrategy.ιB)
    (V : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .BA'' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron (1 : Op S.toStrategy.ιA) T)
          (heteroKron (1 : Op (PauliRegister P)) V))
        (heteroKron (1 : Op (PauliRegister P))
          (1 : Op (PauliRegister P))) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring

/-- The `BB'` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_BB'_heteroKron (T : Op S.toStrategy.ιB)
    (V : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .BB' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron (1 : Op S.toStrategy.ιA) T)
          (heteroKron (1 : Op (PauliRegister P))
            (1 : Op (PauliRegister P))))
        (heteroKron V (1 : Op (PauliRegister P))) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring

/-- The `AB''` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_AB''_heteroKron :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AB'' (heteroKron T V)) =
      heteroKron (heteroKron (heteroKron T (1 : Op S.toStrategy.ιB))
          (heteroKron (1 : Op (PauliRegister P))
            (1 : Op (PauliRegister P))))
        (heteroKron (1 : Op (PauliRegister P)) V) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, place, sixRegShuffle, Equiv.coe_fn_mk, heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring

/-- The product of opposite `AA'` and `BA''` placements separates into the
strategy product, the first EPR-pair product, and the identity on the second
EPR pair. -/
theorem reindexOp_sixRegShuffle_place_AA'_mul_BA'' (T : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T)) =
      heteroKron (heteroKron (heteroKron A B) (heteroKron T T))
        (1 : Op (PauliRegister P × PauliRegister P)) := by
  rw [WinImplications.reindexOp_mul,
    reindexOp_sixRegShuffle_place_AA'_heteroKron,
    reindexOp_sixRegShuffle_place_BA''_heteroKron]
  simp [heteroKron_mul, heteroKron_one_one]

/-- The diagonal quadratic form for the `AA'`--`BA''` product factors into
the strategy overlap and the first EPR-pair overlap. -/
theorem stateQForm_place_AA'_mul_BA''
    (T : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T)) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T T) := by
  have hAB :=
    heteroKron_isHermitian hA hB
  have hTT :=
    heteroKron_isHermitian hT hT
  rw [psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    reindexOp_sixRegShuffle_place_AA'_mul_BA'',
    stateQForm_vecTensor_heteroKron _ _ _ _ (heteroKron_isHermitian hAB hTT) Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB hTT,
    DistanceCalculus.stateQForm_one, eprState_norm]
  ring

include hV in
/-- Placing a factorized operator on the register pair `AA'`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem norm_place_AA'_heteroKron_psiHat :
    ‖applyOperatorToState (S.place .AA' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron T (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ := by
  classical
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_sixRegShuffle_place_AA'_heteroKron,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, vecTensor_norm_eq, vecTensor_norm_eq,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    MagicSquareRigidity.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_left_isometry (A := V) hV),
    eprState_norm]
  ring

/-- Placing a factorized operator on the register pair `BA''`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem norm_place_BA''_heteroKron_psiHat
    (T : Op S.toStrategy.ιB) (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place .BA'' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA) T) S.toStrategy.ψ‖ := by
  classical
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_sixRegShuffle_place_BA''_heteroKron,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, vecTensor_norm_eq, vecTensor_norm_eq,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    MagicSquareRigidity.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_right_isometry V hV),
    eprState_norm]
  ring

/-- Placing a factorized operator on the register pair `BB'`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem norm_place_BB'_heteroKron_psiHat
    (T : Op S.toStrategy.ιB) (V : Op (PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place .BB' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA) T) S.toStrategy.ψ‖ := by
  classical
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_sixRegShuffle_place_BB'_heteroKron,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, vecTensor_norm_eq, vecTensor_norm_eq,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    MagicSquareRigidity.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_left_isometry (A := V) hV),
    eprState_norm]
  ring

include hV in
/-- Placing a factorized operator on the register pair `AB''`. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem norm_place_AB''_heteroKron_psiHat :
    ‖applyOperatorToState (S.place .AB'' (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron T (1 : Op S.toStrategy.ιB)) S.toStrategy.ψ‖ := by
  classical
  rw [psiHat_eq_reindexState,
    WinImplications.norm_applyOperatorToState_reindexState,
    reindexOp_sixRegShuffle_place_AB''_heteroKron,
    applyOperatorToState_heteroKron_vecTensor,
    applyOperatorToState_heteroKron_vecTensor, vecTensor_norm_eq, vecTensor_norm_eq,
    heteroKron_one_one, WinImplications.applyOperatorToState_one,
    MagicSquareRigidity.norm_applyOperatorToState_of_isometry
      (WinImplications.heteroKron_right_isometry V hV),
    eprState_norm]
  ring

end

/-- A factorized operator placed on one of the four register pairs has, on the
expanded state, the state-dependent norm of its strategy factor on the original
state, provided its Pauli factor is an isometry. This is the placement
bookkeeping behind `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:420-505`, blueprint
`ch14_qpbt_observables.tex:1002-1031`. -/
theorem norm_place_heteroKron_psiHat (S : ProjectiveSetting P ε)
    (p : Placement) (T : Op (S.LocalSpace p.side)) (V : Op (PauliRegister P))
    (hV : Vᴴ * V = 1) :
    ‖applyOperatorToState (S.place p (heteroKron T V)) S.psiHat‖ =
      ‖applyOperatorToState (S.placeStrategySide p.side T) S.toStrategy.ψ‖ := by
  cases p with
  | AA' => solve_by_elim [norm_place_AA'_heteroKron_psiHat]
  | BA'' => solve_by_elim [norm_place_BA''_heteroKron_psiHat]
  | BB' => solve_by_elim [norm_place_BB'_heteroKron_psiHat]
  | AB'' => solve_by_elim [norm_place_AB''_heteroKron_psiHat]

end ProjectiveSetting

end

end MIPStarRE.QPBT
