module

public import QPBT.Palomar.PauliExtractionBridge

/-!
# Compact Pauli basis test completeness

This module transports the registered value-one SPCC strategy to the compact
Palomar game.  Its public statement uses the concrete Pauli SPCC predicate and
the once-and-for-all field model, while symmetric-game and relabeling objects
occur only in the proof.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`,
paper `lem:pauli-completeness`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

/-- `lem:pauli-completeness`: every compact Pauli basis game has a symmetric
projective, consistent, support-wise commuting strategy of value exactly one. -/
theorem exists_spcc_value_one (P : PauliParams) :
    ∃ S : SymmetricPauliStrategy P
        (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
      S.IsPauliSPCC P
          (MIPStarRE.QPBT.binaryRepresentation
            (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) ∧
      S.toStrategy.value
          (pauliGame P
            (MIPStarRE.QPBT.binaryRepresentation
              (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
            (MIPStarRE.QPBT.fixedBinTrace
              (MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) = 1 := by
  classical
  let Q := P.toAdmissibleParams
  obtain ⟨T, hspcc, hvalue⟩ := MIPStarRE.QPBT.exists_spcc_value_one Q
  let U := SymmetricStrategy.ofSymmetricStrategy T
  let G := SymmetricGame.ofSymmetricGame (MIPStarRE.QPBT.pauliBasisTestSymm Q)
  let x := (pauliQuestionEquiv Q).symm
  let a := (pauliAnswerEquivCompact Q).symm
  let S := U.relabel x a
  refine ⟨S, (isPauliSPCC_iff_isSPCC Q S).2 ?_, ?_⟩
  · exact (SymmetricStrategy.relabel_isSPCC_iff G _ U x a rfl).2
      ((SymmetricStrategy.isSPCC_ofSymmetricStrategy_iff T).2 hspcc)
  · change S.toStrategy.value (pauliGame _ (binaryRepresentation Q.model) (fixedBinTrace Q.model)) = 1
    rw [← pauliSymmetricGame_toGame]
    exact (Strategy.value_relabel G.toGame U.toStrategy x x a a).trans
      ((SymmetricStrategy.value_ofSymmetricStrategy T).trans hvalue)

end

end MIPStarRE.QPBT.Palomar
