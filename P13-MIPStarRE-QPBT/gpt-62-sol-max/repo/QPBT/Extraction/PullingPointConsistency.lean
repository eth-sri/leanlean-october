module

public import QPBT.Extraction.PointConsistency
public import QPBT.Extraction.PullingMeasurement

/-!
# Point overlaps for the difference-polynomial measurement

Evaluation of the difference polynomial gives `g(u) - g_h(u)`. Unlike
evaluation after decoding, this formula holds for every polynomial outcome.
The resulting point overlaps are the ones supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`,
  especially `eq:qld-pulling-2b` and `eq:qld-pulling-12`.
- The point-placement and convolution identities identify these overlaps with
  the two consistency relations of the supplied global measurement.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter. These
  identities do not construct the global witness. This module was
  originally filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Evaluation of the difference measurement is a convolution with the ideal
Pauli point projectors. No encoding hypothesis on `g` is needed. -/
theorem pullingMeas_eval_effect {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P)
    (a : PauliScalar P) :
    ((pullingMeas w side W).postprocess (fun g => evalPoly g u)).effect a =
      ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
        (tauDotProj W (indicatorVec u) (evalPoly g u - a)) := by
  rw [pullingMeas, Measurement.postprocess_comp]
  have heval (outcome : Poly P × PauliRegister P) :
      evalPoly (pullingPoly outcome) u =
        evalPoly outcome.1 u - dotProduct outcome.2 (indicatorVec u) := by
    change MvPolynomial.eval u (outcome.1.1 - lowDegreeEncoding outcome.2) = _
    rw [MvPolynomial.eval_sub]
    exact congrArg (evalPoly outcome.1 u - ·) (lowDegreeEnc_eq_dotProduct outcome.2 u)
  simp only [Measurement.postprocess_effect, Finset.sum_filter, heval,
    tensorMeasurement, Measurement.ofSumEqOne, pauliRegisterMeas]
  rw [Fintype.sum_prod_type]
  unfold tauDotProj bracketOp
  simp_rw [heteroKron_finset_sum_right, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  have hlabel : evalPoly g u - dotProduct h (indicatorVec u) = a ↔
      dotProduct h (indicatorVec u) = evalPoly g u - a := by
    constructor <;> intro heq <;> linear_combination -heq
  simp only [hlabel]


end

end MIPStarRE.QPBT
