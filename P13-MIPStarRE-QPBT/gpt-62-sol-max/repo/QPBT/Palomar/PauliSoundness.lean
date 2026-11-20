module

public import QPBT.Palomar.PauliExtractionBridge

/-!
# Compact Pauli basis test soundness

This module transports qudit soundness to the compact Palomar game, then
reindexes its witnesses into the fixed binary coordinates.  The statements use the once-and-for-all field model,
arbitrary compact strategies, raw prescribed-answer effects, the unsquared
state norm, and separate unaveraged Alice and Bob squared operator sums.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1491`,
paper `thm:pauli` and `cor:pauli-binary`;
`references/qpbt-paper/04_preliminaries.tex:1163-1208`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

/-- `thm:pauli`: compact Pauli-basis soundness with the exact registered
error function and the three distinct source conclusions. -/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : PauliStrategy P
            (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (pauliGame P
              (MIPStarRE.QPBT.binaryRepresentation
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
              (MIPStarRE.QPBT.fixedBinTrace
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : ExtractionWitness
              (R := PauliRegister P
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) S,
            stateError w ≤ deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliAliceError P S w
                  (MIPStarRE.QPBT.fixedBinTrace
                    (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind,
              rawPauliBobError P S w
                  (MIPStarRE.QPBT.fixedBinTrace
                    (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                deltaQld a b epsilon P.m P.d P.q := by
  obtain ⟨a, b, ha, hb, hb_one, hsound⟩ := MIPStarRE.QPBT.pauli_soundness
  refine ⟨a, b, ha, hb, hb_one, ?_⟩
  intro P epsilon hepsilon S hvalue
  obtain ⟨w, hstate, hAlice, hBob⟩ :=
    hsound P.toAdmissibleParams epsilon hepsilon
      _ (hvalue.trans_eq (pauliStrategyToLibrary_value P.toAdmissibleParams S).symm)
  refine ⟨ExtractionWitness.ofPauliSoundnessWitness w, ?_, ?_, ?_⟩
  · exact (stateError_ofPauliSoundnessWitness w).trans_le hstate
  · intro W
    exact (rawPauliAliceError_ofPauliSoundnessWitness w W).trans_le
      (hAlice (pauliKindEquiv W))
  · intro W
    exact (rawPauliBobError_ofPauliSoundnessWitness w W).trans_le
      (hBob (pauliKindEquiv W))

/-- Changing coordinates in the qudit soundness witness preserves all three errors. -/
theorem _root_.MIPStarRE.QPBT.pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (ε : ℝ), 0 ≤ ε → ∀ S : PauliStrategy P P.model.K,
        1 - ε ≤ S.value P.game →
        ∃ w : ExtractionWitness (R := QubitRegister P P.model.basisDim) S,
          stateError w ≤ deltaQld a b ε P.m P.d P.q ∧
          (∀ W, rawQubitAliceError P S w P.model.binaryCoordinates W ≤ deltaQld a b ε P.m P.d P.q) ∧
          ∀ W, rawQubitBobError P S w P.model.binaryCoordinates W ≤ deltaQld a b ε P.m P.d P.q := by
  obtain ⟨a, b, ha, hb, hb_one, hsound⟩ := pauli_soundness
  refine ⟨a, b, ha, hb, hb_one, fun P epsilon he S hv => ?_⟩
  obtain ⟨w, hstate, hAlice, hBob⟩ := hsound P epsilon he S hv
  exact ⟨w.reindex (binaryLabels P), (stateError_reindex _ _).trans_le hstate,
    fun W => (rawQubitAliceError_reindex w W).trans_le (hAlice W),
    fun W => (rawQubitBobError_reindex w W).trans_le (hBob W)⟩

/-- `cor:pauli-binary`: compact Pauli-basis soundness in the qubit
coordinates of the original fixed self-dual normal basis. -/
theorem pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : PauliStrategy P
            (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (pauliGame P
              (MIPStarRE.QPBT.binaryRepresentation
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
              (MIPStarRE.QPBT.fixedBinTrace
                (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : ExtractionWitness
              (R := QubitRegister P
                (MIPStarRE.QPBT.fixedFieldModel P.q
                  P.is_admissible_size).basisDim) S,
            stateError w ≤ deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawQubitAliceError P S w
                  (MIPStarRE.QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : PauliKind,
              rawQubitBobError P S w
                  (MIPStarRE.QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                deltaQld a b epsilon P.m P.d P.q := MIPStarRE.QPBT.pauli_soundness_qubit

end

end MIPStarRE.QPBT.Palomar
