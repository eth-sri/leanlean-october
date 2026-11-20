module

public import QPBT.Combining.ExtendedLineGame

/-!
# Correlations on the two-player expanded state

The six-register state of `eq:def-psihat` factors as the two-player state
`ExtendedLineGame.pairState` and an unused normalized EPR pair, for each of
the opposite register placements `AA'`--`BA''` and `AB''`--`BB'`. Therefore
arbitrary Hermitian operators on the expanded local spaces have the same
correlation in the two descriptions. An individual operator need not factor
between its strategy register and its Pauli register.

These are formalization-only auxiliary identities for the strategy construction
in the proof of `lem:qld-4-7`. They do not establish its passing value or the
existence of its input measurements. Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 remains open.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-372`,
  equation `eq:def-psihat`.
- The same source, `lem:qld-4-7`, proof at lines 1279-1288.
- Blueprint `def:expanded-state`, `def:symmetric-equivalents`, and `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#302.
-/

@[expose] public section

-- The six-register products require the same instance-search size as ExpandedPlacement.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open scoped MatrixOrder ComplexOrder
open MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon : Real}

/-- Regroup the six registers as `(AA', BA'')` and the unused pair `(B', B'')`.
This is the first opposite-placement partition of `eq:def-psihat`. -/
def aaBaRegrouping (setting : ProjectiveSetting P epsilon) :
    SixReg P setting.toStrategy.ιA setting.toStrategy.ιB ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (PauliRegister P × PauliRegister P) :=
  (aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm

/-- Arbitrary Hermitian expanded operators have the same correlation on
`pairState` as their `AA'`--`BA''` placements on `psiHat`. Hermiticity holds for
POVM effects; no factorization or consistency hypothesis is required. This
transports Born correlations in the first proof paragraph of `lem:qld-4-7`. -/
theorem stateQForm_pairState_eq_AA'_BA'' (setting : ProjectiveSetting P epsilon)
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob))
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    DistanceCalculus.stateQForm (pairState setting) (heteroKron A B) =
      DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AA' A * setting.place .BA'' B) := by
  let I : Op (PauliRegister P × PauliRegister P) := 1
  have hop : reindexOp (aaBaRegrouping setting) (heteroKron (heteroKron A B) I) =
      setting.place .AA' A * setting.place .BA'' B := by
    change reindexOp (aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB)
      (reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I)) = _
    rw [show reindexOp (Equiv.prodAssoc _ _ _).symm
        (heteroKron (heteroKron A B) I) = heteroKron A (heteroKron B I) from
      Matrix.kronecker_assoc A B I]
    rw [show heteroKron A (heteroKron B I) =
        heteroKron A 1 * heteroKron 1 (heteroKron B I) by
      simp [heteroKron_mul]]
    exact (WinImplications.reindexOp_mul _ _ _).trans
      (congrArg₂ _
        (reindexOp_aaBaBipartition_left setting A)
        (reindexOp_aaBaBipartition_right setting B))
  calc
    _ =
        DistanceCalculus.stateQForm
          (vecTensor (pairState setting) (eprState (PauliRegister P)))
          (heteroKron (heteroKron A B) I) := by
      rw [stateQForm_vecTensor_heteroKron _ _ _ _
        (heteroKron_isHermitian hA hB) Matrix.isHermitian_one]
      simp [DistanceCalculus.stateQForm_one, eprState_norm]
    _ = _ := by
      rw [← (show reindexState (aaBaRegrouping _) setting.psiHat = vecTensor (pairState _) (eprState (PauliRegister _)) by rfl),
        WinImplications.stateQForm_reindexState, hop]

/-- Arbitrary Hermitian expanded operators have the same correlation on
`pairState` as their `AB''`--`BB'` placements on `psiHat`. This is the second
orientation of the Born-correlation transport for `lem:qld-4-7`; EPR symmetry
reverses the active ancillary registers without transposing either operator. -/
theorem stateQForm_pairState_eq_AB''_BB' {setting : ProjectiveSetting P epsilon}
    {A : Op (setting.ExpandedLocalSpace .alice)}
    {B : Op (setting.ExpandedLocalSpace .bob)}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    DistanceCalculus.stateQForm (pairState setting) (heteroKron A B) =
      DistanceCalculus.stateQForm setting.psiHat
        (setting.place .AB'' A * setting.place .BB' B) := by
  rw [opposite_place_qform_mul_eq]
  solve_by_elim [stateQForm_pairState_eq_AA'_BA'']

end ExtendedLineGame

end

end MIPStarRE.QPBT
