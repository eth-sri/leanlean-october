module

public import QPBT.Combining.DirectLowDegree.CoefficientConsistency
public import QPBT.Combining.DirectLowDegree.Transport.LineResampling

/-!
# Extended direct coefficient-collision loss

This module compares the sum of the axis and diagonal coefficient-collision
losses at the extended directly indexed parameters with the original `m*d/q`
ratio.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- The axis loss `d/q` plus the diagonal loss `(2m+2)d/q` at the extended
direct parameters is at most five times the original loss `md/q`.

This is a Lean-only scalar auxiliary for combining the two coefficient-POVM
consistency estimates. It uses only admissibility of the original parameters. -/
theorem extendedDirectLd_coefficientCollisionLoss_le_five_mul
    (P : AdmissibleParams) :
    ((P.extendedDirectLd.d : ℝ) +
        (P.extendedDirectLd.m * P.extendedDirectLd.d : ℝ)) /
        (P.extendedDirectLd.q : ℝ) ≤
      5 * ((P.m * P.d : ℝ) / (P.q : ℝ)) := by
  have hm : (1 : ℝ) ≤ (P.m : ℝ) := by
    exact_mod_cast P.one_le_m
  have hqNat : 0 < P.q := zero_lt_two.trans_le P.hq.two_le
  have hq : (0 : ℝ) < (P.q : ℝ) := by
    exact_mod_cast hqNat
  push_cast
  rw [show 5 * ((P.m : ℝ) * (P.d : ℝ) / (P.q : ℝ)) =
    (5 * ((P.m : ℝ) * (P.d : ℝ))) / (P.q : ℝ) by ring]
  apply (div_le_div_iff_of_pos_right hq).2
  nlinarith

end MIPStarRE.QPBT
