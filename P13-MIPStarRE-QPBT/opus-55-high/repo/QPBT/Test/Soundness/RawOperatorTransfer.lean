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
noncomputable def rawPauliTransferFactor : ℝ :=
  2 + 4 * (Fintype.card PauliEdge : ℝ)

variable {P : AdmissibleParams} {a b ε : ℝ}

theorem epsilon_le_deltaQld (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaQld a b ε P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have ha0 := zero_le_one.trans ha
  have hpref :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hmd ha0)
  have hεpow : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le
  have hq := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have htwo := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  nlinarith

theorem raw_pauli_error_absorb (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    2 * deltaQld a b ε P.m P.d P.q +
        4 * deltaQld a b ε P.m P.d P.q ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
      deltaQld (rawPauliTransferFactor * (21 * a ^ 2)) b ε P.m P.d P.q := by
  let d := deltaQld a b ε P.m P.d P.q
  let K := rawPauliTransferFactor
  have hd : 0 ≤ d := deltaQld_nonneg (zero_le_one.trans ha) hε0
  have hεd : ε ≤ d := epsilon_le_deltaQld ha hb hb1 hε0 hε1
  have hK : 1 ≤ K := by
    dsimp only [K, rawPauliTransferFactor]
    have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
    linarith
  have hbase : 3 * d + 6 * d ^ 2 ≤
      deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
    three_add_six_sq_deltaQld_le ha hb hε0 hε1
  calc
    2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε ≤
        (2 + 4 * (Fintype.card PauliEdge : ℝ)) * d + 4 * d ^ 2 := by
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith
    _ ≤ K * (3 * d + 6 * d ^ 2) := by
      dsimp only [K, rawPauliTransferFactor]
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith
    _ ≤ K * deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
      mul_le_mul_of_nonneg_left hbase (zero_le_one.trans hK)
    _ ≤ deltaQld (K * (21 * a ^ 2)) b ε P.m P.d P.q :=
      scale_deltaQld_le (by nlinarith) hε0 hK

/-- The arbitrary-strategy soundness estimates for the raw prescribed Pauli
answer effects of `thm:pauli`. The completed-family Naimark estimates remain
internal and their transfer loss is absorbed into the existential prefactor. -/
theorem exists_arbitrary_strategy_raw_isometry_bounds :
    ∃ A b : ℝ, 1 ≤ A ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld A b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
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
  have haA := ha21.trans h21A
  have hsmall : ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
        ∃ w : PauliSoundnessWitness P S,
          ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
              deltaQld A b ε P.m P.d P.q ∧
          (∀ W : PauliKind,
            rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
          (∀ W : PauliKind,
            rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
    intro P ε hε0 hε1 S hwin
    obtain ⟨w, hstate, hcompletedA, hcompletedB⟩ :=
      hcompleted P ε hε0 hε1 S hwin
    let d := deltaQld a b ε P.m P.d P.q
    have habsorb : 2 * d + 4 * d ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε ≤
          deltaQld A b ε P.m P.d P.q := by
      dsimp only [d, A]
      exact raw_pauli_error_absorb ha hb hb1 hε0 hε1
    have hmono : d ≤ deltaQld A b ε P.m P.d P.q := by
      dsimp only [d]
      exact deltaQld_mono ha haA le_rfl hb hε0 hε1
    refine ⟨w, hstate.trans hmono, ?_, ?_⟩
    · intro W
      calc
        rawPauliOperatorDistanceA P S w W ≤
            2 * pauliOperatorDistanceA P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceA_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          grind
        _ ≤ _ := habsorb
    · intro W
      calc
        rawPauliOperatorDistanceB P S w W ≤
            2 * pauliOperatorDistanceB P S w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceB_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          grind
        _ ≤ _ := habsorb
  refine ⟨A, b, hA, hb, hb1, ?_⟩
  intro P ε hε0 S hwin
  rcases le_or_gt ε 1 with hε1 | hε1
  · simp_all
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : deltaQld A b 1 P.m P.d P.q ≤
        deltaQld A b ε P.m P.d P.q :=
      deltaQld_mono_epsilon hA hb zero_le_one hε1.le
    grind

end

end MIPStarRE.QPBT
