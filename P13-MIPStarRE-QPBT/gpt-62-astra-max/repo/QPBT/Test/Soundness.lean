module

public import QPBT.Test.Soundness.RawOperatorTransferCore

/-!
# Pauli basis test soundness

This module states the source-shaped soundness theorem and provides auxiliary
range-projection estimates, ancilla isometries, and the transfer of supplied
extraction data to the three soundness estimates.
The scalar square-root error bound is in `MIPStarRE.QPBT.Combining.RootErrorBounds`.
The completed-family estimates are supplied by the Naimark reduction. The
final transfer bounds the rejected wrong-form mass and restores the raw Pauli
effects required by the paper before extending the result to the full error
domain.

## References

The main declaration is blueprint
`thm:pauli`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
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

private theorem epsilon_le_deltaQld {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ deltaQld a b ε P.m P.d P.q := by
  have hmd : _ ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hpref :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hmd (zero_le_one.trans ha))
  have hεpow : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le
  have hq := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have htwo := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold deltaQld
  simp only [Real.rpow_eq_pow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpref)
    (add_nonneg (add_nonneg (Real.rpow_nonneg hε0 b) hq) htwo)]

private theorem raw_pauli_error_absorb {P : AdmissibleParams}
    {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b < 1)
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
    linarith
  calc
    _ ≤
        (2 + 4 * (Fintype.card PauliEdge : ℝ)) * d + 4 * d ^ 2 := by
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard (sub_nonneg.mpr hεd)]
    _ ≤ K * (3 * d + 6 * d ^ 2) := by
      dsimp only [K, rawPauliTransferFactor]
      have hcard : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      nlinarith [mul_nonneg hcard hd, mul_nonneg hcard (sq_nonneg d), sq_nonneg d]
    _ ≤ K * deltaQld (21 * a ^ 2) b ε P.m P.d P.q :=
      mul_le_mul_of_nonneg_left (three_add_six_sq_deltaQld_le ha hb hε0 hε1) (zero_le_one.trans hK)
    _ ≤ _ := scale_deltaQld_le (by nlinarith [sq_nonneg a]) hε0 hK

/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`thm:pauli`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
blueprint `def:povm-distance`.
-/
theorem pauli_soundness :
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
    linarith
  have hA : 1 ≤ A := by
    dsimp only [A]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ _ :=
        mul_le_mul hfactor (by nlinarith [sq_nonneg a]) zero_le_one (zero_le_one.trans hfactor)
  have ha21 : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have h21A : 21 * a ^ 2 ≤ A := by
    dsimp only [A]
    exact le_mul_of_one_le_left (by positivity) hfactor
  have haA := ha21.trans h21A
  have hsmall : ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
      ∀ S : _, 1 - ε ≤ S.value →
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
    have hmono : d ≤ deltaQld A b ε P.m P.d P.q := id (deltaQld_mono ha haA le_rfl hb hε0 hε1)
    refine ⟨w, hstate.trans hmono, ?_, ?_⟩
    · intro W
      calc
        _ ≤
            2 * pauliOperatorDistanceA w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceA_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          linarith [hcompletedA W]
        _ ≤ _ := habsorb
    · intro W
      calc
        _ ≤
            2 * pauliOperatorDistanceB w W + 4 * d ^ 2 +
              4 * (Fintype.card PauliEdge : ℝ) * ε :=
          raw_pauli_operator_distanceB_le_completed S hwin w hstate W
        _ ≤ 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
          linarith [hcompletedB W]
        _ ≤ _ := habsorb
  refine ⟨A, b, hA, hb, hb1, ?_⟩
  intro P ε hε0 S hwin
  rcases le_or_gt ε 1 with hε1 | hε1
  · solve_by_elim [hsmall]
  · obtain ⟨w, hstate, hAraw, hBraw⟩ :=
      hsmall P 1 zero_le_one le_rfl S (by simpa using S.value_nonneg)
    have hmono : deltaQld A b 1 P.m P.d P.q ≤
        _ :=
      deltaQld_mono_epsilon hA hb zero_le_one hε1.le
    exact ⟨w, hstate.trans hmono, fun W => (hAraw W).trans hmono,
      fun W => (hBraw W).trans hmono⟩

end

end MIPStarRE.QPBT
