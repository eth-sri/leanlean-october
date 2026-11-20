module

public import QPBT.Combining.DirectLowDegree.Soundness
public import QPBT.Games.MeasurementCompression

/-!
# Direct low-degree soundness for arbitrary strategies

This module transports directly indexed low-degree soundness at simultaneity
parameter `1` from projective strategies to arbitrary strategies. Both local
measurement families are dilated by the existing one-measurement Naimark
construction. The polynomial-tuple POVMs returned by projective soundness are
then compressed to the original player carriers at the distinguished ancillary
coordinate.

Ground-slice compression preserves all three consistency defects exactly, so
the error function and its universal constants are unchanged. The compressed
polynomial POVMs are not asserted to be projective.

## Main result

* `exists_direct_ld_soundness_of_k_eq_one_any_strategy` removes the projectivity
  premise from the formalization-only direct `k = 1` soundness route.

## References

The projective soundness input formalizes the shape of paper
`lem:ld-soundness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`.
The Naimark transport supports the first paragraph of the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
This module is formalization-only support and does not claim completion of that lemma.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Formalization-only soundness transport for the directly indexed low-degree
game at simultaneity parameter `1`, with no projectivity premise on the input
strategy.

Apply Naimark dilation to both question-indexed POVM families, use
`exists_direct_ld_soundness_of_k_eq_one` on the resulting projective strategy,
and compress its two polynomial-tuple POVMs at the distinguished ancillary
coordinates. The padded-state defect identity preserves the two point versus
polynomial bounds and the polynomial self-consistency bound exactly, with the
same witnesses `a`, `b`, and `deltaLd` as the projective theorem.

This theorem is formalization-only support for the Naimark step in the proof of paper
`lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1277-1289`.
Its separate blueprint entry is `thm:qld-direct-soundness-any-strategy`.
It does not assert projectivity of the compressed POVMs and does not add a
hypothesis to any paper-labelled theorem. -/
theorem direct_ld_soundness_of_k_eq_one_any_strategy_explicit :
    ∀ (D : DirectLdParams) (ε : ℝ), D.k = 1 → 0 < ε →
        ∀ S : Strategy (directLdGame D), 1 - ε ≤ S.value →
          ∃ GA : DirectPolyMeasTuple D S.ιA,
            ∃ GB : DirectPolyMeasTuple D S.ιB,
              bipartiteDefect
                  (uniformDistribution (DirectPoint D))
                  (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D))
                  (fun u => GB.postprocess (evalDirectPolyTupleAt u))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              bipartiteDefect
                  (uniformDistribution (DirectPoint D))
                  (fun u => GA.postprocess (evalDirectPolyTupleAt u))
                  (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
                  (directLdPointValuesOrZero D))
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k ∧
              bipartiteDefect (uniformDistribution Unit)
                  (fun _ => GA)
                  (fun _ => GB)
                  S.ψ ≤ deltaLd pauliBaselineLowDegreeConstant
                    pauliBaselineLowDegreePower ε D.q D.m D.d D.k := by
  intro D ε hk hε S hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    direct_ld_soundness_of_k_eq_one_explicit D ε hk hε
      S.naimark S.naimark_isProjective (S.naimark_value.symm ▸ hwin)
  change bipartiteDefect _ _ _ (padState none none S.ψ) ≤ _ at h1 h2 h3
  rw [consistencyDefect_padState_compressAt] at h1 h2 h3
  have hA (q) : (S.naimark.A q).compressAt none = S.A q := Measurement.compressAt_dilatedMeasurement _ _
  have hB (q) : (S.naimark.B q).compressAt none = S.B q := Measurement.compressAt_dilatedMeasurement _ _
  refine ⟨GA.compressAt none, GB.compressAt none, ?_, ?_, h3⟩
  · simpa only [MIPStarRE.Quantum.Measurement.compressAt_postprocess, hA] using h1
  · simpa only [MIPStarRE.Quantum.Measurement.compressAt_postprocess, hB] using h2

end

end MIPStarRE.QPBT
