module

public import QPBT.Combining.ExtendedLineGame
public import QPBT.Observables.ExpandedPlacement

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

open MIPStarRE.Quantum
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon : Real}

section

variable (setting : ProjectiveSetting P epsilon)
include setting

/-- Regroup the six registers as `(AA', BA'')` and the unused pair `(B', B'')`.
This is the first opposite-placement partition of `eq:def-psihat`. -/
def aaBaRegrouping :
    setting.ExpandedSpace ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (PauliRegister P × PauliRegister P) :=
  (aaBaBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm

/-- Regroup the six registers as `(AB'', BB')` and the unused pair `(A', A'')`.
This is the second opposite-placement partition of `eq:def-psihat`. -/
def abBbRegrouping :
    setting.ExpandedSpace ≃
      (setting.ExpandedLocalSpace .alice × setting.ExpandedLocalSpace .bob) ×
        (PauliRegister P × PauliRegister P) :=
  (abBbBipartition P setting.toStrategy.ιA setting.toStrategy.ιB).trans
    (Equiv.prodAssoc _ _ _).symm

/-- In the `AA'`--`BA''` grouping, the expanded state is `pairState` tensored
with the unused EPR pair. This is a coordinate consequence of `eq:def-psihat`,
not an assumption on the strategy or its measurement effects. -/
theorem reindexState_aaBaRegrouping_psiHat :
    reindexState (aaBaRegrouping setting) setting.psiHat =
      vecTensor (pairState setting) (eprState (PauliRegister P)) := by rfl

/-- The `AB''`--`BB'` grouping has the same two-player state because an EPR
pair is invariant under exchanging its registers. The other EPR pair is unused.
This is a coordinate consequence of `eq:def-psihat`. -/
theorem reindexState_abBbRegrouping_psiHat :
    reindexState (abBbRegrouping setting) setting.psiHat =
      vecTensor (pairState setting) (eprState (PauliRegister P)) := by
  ext p
  have hswap := congrArg
    (fun v : EuclideanSpace Complex (PauliRegister P × PauliRegister P) =>
      v (p.1.1.2, p.1.2.2)) (reindexState_prodComm_eprState (PauliRegister P))
  change eprState (PauliRegister P) (p.1.2.2, p.1.1.2) =
    eprState (PauliRegister P) (p.1.1.2, p.1.2.2) at hswap
  change
    (setting.toStrategy.ψ (p.1.1.1, p.1.2.1) * eprState (PauliRegister P) p.2) *
        eprState (PauliRegister P) (p.1.2.2, p.1.1.2) =
      (setting.toStrategy.ψ (p.1.1.1, p.1.2.1) *
        eprState (PauliRegister P) (p.1.1.2, p.1.2.2)) *
          eprState (PauliRegister P) p.2
  rw [hswap]
  ring

end

/-- The unused normalized EPR factor does not contribute to the correlation. -/
private theorem stateQForm_pairState_eq_reindex (S : ProjectiveSetting P epsilon)
    (e : S.ExpandedSpace ≃
      (S.toStrategy.ιA × PauliRegister P) ×
        ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)))
    (hψ : reindexState (e.trans (Equiv.prodAssoc _ _ _).symm) S.psiHat =
      vecTensor (pairState S) (eprState (PauliRegister P)))
    (A : Op (S.toStrategy.ιA × PauliRegister P)) (B : Op (S.toStrategy.ιB × PauliRegister P)) :
    DistanceCalculus.stateQForm (pairState S) (heteroKron A B) =
      DistanceCalculus.stateQForm S.psiHat
        (reindexOp e (heteroKron A 1) * reindexOp e (heteroKron 1 (heteroKron B 1))) := by
  let I : Op (PauliRegister P × PauliRegister P) := 1
  have h := stateQForm_vecTensor_right_hermitian (heteroKron A B) (1 : Op (PauliRegister P × PauliRegister P))
    (pairState S) (eprState (PauliRegister P)) Matrix.isHermitian_one
  rw [← hψ, DistanceCalculus.stateQForm_reindexState,
    DistanceCalculus.stateQForm_one, eprState_norm, one_pow, mul_one] at h
  change DistanceCalculus.stateQForm S.psiHat
    (reindexOp e (reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I))) = _ at h
  rw [show reindexOp (Equiv.prodAssoc _ _ _).symm (heteroKron (heteroKron A B) I) = _ from
    Matrix.kronecker_assoc A B I] at h
  rw [← reindexOp_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  exact h.symm

/-- Correlations on the expanded state, in the `AA'_BA''` register partition. -/
theorem stateQForm_pairState_eq_AA'_BA'' (S : ProjectiveSetting P epsilon)
    (A : Op (S.ExpandedLocalSpace .alice)) (B : Op (S.ExpandedLocalSpace .bob)) :
    DistanceCalculus.stateQForm (pairState S) (heteroKron A B) =
      S.placedCorrelation .AA' .BA'' A B := by
  have h := stateQForm_pairState_eq_reindex S (aaBaBipartition P _ _)
    (reindexState_aaBaRegrouping_psiHat S) A B
  rwa [reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right] at h

/-- Correlations on the expanded state, in the `AB''_BB'` register partition. -/
theorem stateQForm_pairState_eq_AB''_BB' (S : ProjectiveSetting P epsilon)
    (A : Op (S.ExpandedLocalSpace .alice)) (B : Op (S.ExpandedLocalSpace .bob)) :
    DistanceCalculus.stateQForm (pairState S) (heteroKron A B) =
      S.placedCorrelation .AB'' .BB' A B := by
  have h := stateQForm_pairState_eq_reindex S (abBbBipartition P _ _)
    (reindexState_abBbRegrouping_psiHat S) A B
  rwa [reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right] at h

end ExtendedLineGame

end

end MIPStarRE.QPBT
