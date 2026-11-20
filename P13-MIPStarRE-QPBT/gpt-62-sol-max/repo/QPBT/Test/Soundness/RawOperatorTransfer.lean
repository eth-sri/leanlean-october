module

public import QPBT.Test.Soundness.RawOperatorTransferCore

/-!
# Final raw Pauli-effect soundness bounds

This module absorbs the completed-to-raw transfer loss into the Pauli
soundness error and exposes the fixed explicit baseline and existential
source-facing bounds. The operator transfer itself is implemented in
`MIPStarRE.QPBT.Test.Soundness.RawOperatorTransferCore`.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Universal scalar used to absorb the completed-to-raw transfer loss. -/
private noncomputable def rawPauliTransferFactor : ℝ :=
  2 + 4 * (Fintype.card PauliEdge : ℝ)

section

variable {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
include P a b ε ha hb hb1 hε0 hε1

private theorem epsilon_le_deltaQld :
    ε ≤ P.qldError a b ε := by
  exact (by simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le : ε ≤ ε ^ b).trans
    (rpow_noise_le_deltaQld ha hε0)

private theorem raw_pauli_error_absorb :
    2 * P.qldError a b ε +
        4 * P.qldError a b ε ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
      P.qldError (rawPauliTransferFactor * (21 * a ^ 2)) b ε := by
  let d := P.qldError a b ε
  let K := rawPauliTransferFactor
  have hd : 0 ≤ d := deltaQld_nonneg (zero_le_one.trans ha) hε0
  have hεd : ε ≤ d := epsilon_le_deltaQld ha hb hb1 hε0 hε1
  have hK : 1 ≤ K := by
    dsimp only [K, rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have hbase : 3 * d + 6 * d ^ 2 ≤
      P.qldError (21 * a ^ 2) b ε :=
    three_add_six_sq_deltaQld_le ha hb hε0 hε1
  calc
    2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε ≤
        (2 + 4 * (Fintype.card PauliEdge : ℝ)) * d + 4 * d ^ 2 := by
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard (sub_nonneg.mpr hεd)]
    _ ≤ K * (3 * d + 6 * d ^ 2) := by
      dsimp only [K, rawPauliTransferFactor]
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard hd, mul_nonneg hcard (sq_nonneg d), sq_nonneg d]
    _ ≤ K * P.qldError (21 * a ^ 2) b ε :=
      mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hK)
    _ ≤ P.qldError (K * (21 * a ^ 2)) b ε := by
      exact scale_deltaQld_le (by nlinarith [sq_nonneg a]) hε0 hK

end

/-- The arbitrary-strategy soundness estimates for the raw prescribed Pauli
answer effects of `thm:pauli`. The completed-family Naimark estimates remain
internal and their transfer loss is absorbed into the existential prefactor. -/
theorem exists_arbitrary_strategy_raw_isometry_bounds :
    ∃ A b : ℝ, 1 ≤ A ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            w.rawWithin (P.qldError A b ε) := by
  obtain ⟨a, b, ha, hb, hb1, hcompleted⟩ := exists_arbitrary_strategy_isometry_bounds
  let A := rawPauliTransferFactor * (21 * a ^ 2)
  have hfactor : 1 ≤ rawPauliTransferFactor := by
    dsimp only [rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have h21 : 1 ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hA : 1 ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ rawPauliTransferFactor * (21 * a ^ 2) :=
        mul_le_mul hfactor h21 zero_le_one (zero_le_one.trans hfactor)
  have ha21 : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have h21A : 21 * a ^ 2 ≤ A := by
    dsimp only [A]
    exact le_mul_of_one_le_left (by positivity) hfactor
  have haA : a ≤ A := ha21.trans h21A
  have hsmall : ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
        ∃ w : PauliSoundnessWitness P S,
          w.rawWithin (P.qldError A b ε) := by
    intro P ε hε0 hε1 S hwin
    obtain ⟨w, hstate, hcompletedA, hcompletedB⟩ :=
      hcompleted P ε hε0 hε1 S hwin
    let d := P.qldError a b ε
    have habsorb : 2 * d + 4 * d ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
          P.qldError A b ε := by
      dsimp only [d, A]
      exact raw_pauli_error_absorb ha hb hb1 hε0 hε1
    have hmono : d ≤ P.qldError A b ε := by
      dsimp only [d]
      exact deltaQld_mono ha haA le_rfl hb hε0 hε1
    have transfer {x y : ℝ}
        (h : x ≤ 2 * y + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε)
        (hy : y ≤ d) : x ≤ P.qldError A b ε :=
      (show x ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε by linarith).trans habsorb
    exact ⟨w, hstate.trans hmono,
      fun W => transfer (raw_pauli_operator_distanceA_le_completed S hwin w hstate W) (hcompletedA W),
      fun W => transfer (raw_pauli_operator_distanceB_le_completed S hwin w hstate W) (hcompletedB W)⟩
  refine ⟨A, b, hA, hb, hb1, ?_⟩
  intro P ε hε0 S hwin
  rcases le_or_gt ε 1 with hε1 | hε1
  · exact hsmall P ε hε0 hε1 S hwin
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : P.qldError A b 1 ≤
        P.qldError A b ε :=
      deltaQld_mono_epsilon hA hb zero_le_one hε1.le
    exact ⟨w, hstate.trans hmono, fun W => (hAraw W).trans hmono,
      fun W => (hBraw W).trans hmono⟩

end

end MIPStarRE.QPBT
