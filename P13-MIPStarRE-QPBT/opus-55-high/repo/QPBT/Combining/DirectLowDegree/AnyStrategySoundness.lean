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

/-- Dilate every direct-game question measurement and pad the bipartite state
at the two distinguished `none` coordinates. -/
@[reducible] def directLdNaimarkStrategy (D : DirectLdParams)
    (S : Strategy (directLdGame D)) : Strategy (directLdGame D) :=
  paddedStrategy S (none : Option (DirectLdAnswer D))
    (none : Option (DirectLdAnswer D))
    (fun question => dilatedMeasurement (default : DirectLdAnswer D) (S.A question))
    (fun question => dilatedMeasurement (default : DirectLdAnswer D) (S.B question))

variable (D : DirectLdParams) (S : Strategy (directLdGame D))

/-- Every local measurement of the dilated direct-game strategy is projective. -/
theorem directLdNaimarkStrategy_isProjective : (directLdNaimarkStrategy D S).IsProjective :=
  paddedStrategy_isProjective S none none _ _
    (fun question => dilatedMeasurement_isProjective
      (default : DirectLdAnswer D) (S.A question))
    (fun question => dilatedMeasurement_isProjective
      (default : DirectLdAnswer D) (S.B question))

/-- The direct-game value is unchanged by the two local Naimark dilations. -/
theorem directLdNaimarkStrategy_value : (directLdNaimarkStrategy D S).value = S.value :=
  paddedStrategy_value S none none _ _
    (fun question answer => dilatedMeasurement_compression
      (default : DirectLdAnswer D) answer (S.A question))
    (fun question answer => dilatedMeasurement_compression
      (default : DirectLdAnswer D) answer (S.B question))

end

end MIPStarRE.QPBT
