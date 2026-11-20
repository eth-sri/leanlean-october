module

public import QPBT.Extraction.SuppliedPointConsistency
public import QPBT.Extraction.BlockMeasurement
public import QPBT.Extraction.PullingDefect

/-!
# Evaluated total-Pauli consistency before extraction

The supplied-witness point estimates combine with point self-consistency and
the two orientations of the game's Pauli-basis check. All estimates act on the
original six-register state, before conjugation by the swaps.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1810`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

/-- The opposite party. -/
@[simp, reducible] def PlayerSide.other : PlayerSide → PlayerSide
  | .alice => .bob
  | .bob => .alice

/-- Defect of the evaluated Pauli readout against the other player's pulled readout. -/
def ProjectiveSetting.evaluatedPauliDefect {P : AdmissibleParams} {ε δ : ℝ}
    (S : ProjectiveSetting P ε) (w : GlobalPairWitness S δ) (side : PlayerSide) (W : PauliKind) : ℝ :=
  measurementDefect (uniformDistribution (PauliPoint P))
    (fun u => S.playerMeasurement side (S.pauliEvalMeas side W u))
    (fun u => S.blockMeasurement side.other (tildeMMeasurement w side.other W (indicatorVec u))) S.psiHat

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The total-Pauli readout is consistent with the opposite pulled readout. -/
theorem evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
    {P : AdmissibleParams} {epsilon deltaG : ℝ}
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hd : 0 ≤ deltaG)
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) :
    S.evaluatedPauliDefect w side W ≤
      deltaConstructPaulis (2 + 4 * Real.sqrt 172) epsilon deltaG P.m P.d P.q := by
  let mu := uniformDistribution (PauliPoint P)
  let PA := fun u => S.playerMeasurement .alice (S.pointMeas .alice W u)
  let PB := fun u => S.playerMeasurement .bob (S.pointMeas .bob W u)
  let QA := fun u => S.playerMeasurement .alice (S.pauliEvalMeas .alice W u)
  let QB := fun u => S.playerMeasurement .bob (S.pauliEvalMeas .bob W u)
  let T := fun (side : PlayerSide) (u : PauliPoint P) =>
    S.blockMeasurement side (tildeMMeasurement w side W (indicatorVec u))
  have hpoints : measurementDefect mu PA PB S.psiHat ≤ 86 * epsilon := by
    simpa only [measurementDefect, PA, PB, S.playerMeasurement_effect,
      S.consistencyDefect_placePlayers, pauli_edge_card, Nat.cast_ofNat] using point_self_consistency_le S W
  have hforward : measurementDefect mu PA QB S.psiHat ≤ 86 * epsilon := by
    simpa only [measurementDefect, PA, QB, S.playerMeasurement_effect,
      S.consistencyDefect_placePlayers] using WinImplications.win_pauli_basis_cons_explicit P epsilon S he W
  have hreverse : measurementDefect mu QA PB S.psiHat ≤ 86 * epsilon := by
    simpa only [measurementDefect, QA, PB, S.playerMeasurement_effect,
      S.consistencyDefect_placePlayers] using WinImplications.win_pauli_basis_cons_interchanged_explicit P epsilon S he W
  have hleft := tilde_point_defect_le w .alice W he hd
  have hright := tilde_point_defect_le w .bob W he hd
  have hscalar :
      deltaConstructPaulis (2 + 2 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q +
        2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      deltaConstructPaulis (2 + 4 * Real.sqrt 172)
        epsilon deltaG P.m P.d P.q := by
    rw [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 172)]
    unfold deltaConstructPaulis
    have hr : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / P.q := by positivity
    nlinarith [Real.sqrt_nonneg (172 : ℝ), Real.sqrt_nonneg epsilon]
  rw [ProjectiveSetting.evaluatedPauliDefect, measurementDefect_symm]
  cases side
  · exact (consistencyDefect_trans_le mu (T .bob) PA PB QA S.psiHat _ _ _
      (uniformDistribution_isProbability _) S.psiHat_norm hright
      ((measurementDefect_symm mu PB PA S.psiHat).trans_le hpoints)
      ((measurementDefect_symm mu PB QA S.psiHat).trans_le hreverse)).trans hscalar
  · exact (consistencyDefect_trans_le mu (T .alice) PB PA QB S.psiHat _ _ _
      (uniformDistribution_isProbability _) S.psiHat_norm hleft hpoints hforward).trans hscalar

end

end MIPStarRE.QPBT
