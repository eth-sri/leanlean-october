module

public import QPBT.Observables.ExpandedPlacement
public import QPBT.Observables.LineMeasurement.Restriction

/-!
# Pauli-register line projectors

This module constructs the projective measurement `tau^{W,line}` of one
generalized-Pauli register whose outcome is the restriction to a canonical
line of the low-degree encoding of the measured basis label. It records that
the outcome projectors are orthogonal projections summing to the identity,
that they are symmetric matrices (so that they act identically on either half
of an EPR pair), and that on an axis-parallel line they vanish outside the
embedded degree-`d` subspace.

## References

The projectors are `tau^{W,line}_{f''}` of `def:expanded-line-measurement`,
with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`. Their
perfect self-consistency on an EPR pair is the ancillary input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

section

variable (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams)
include P W line

/-- The Pauli-register projector onto labels whose low-degree encoding
restricts to `f` on `line`. This is `tau^{W,line}_f` in the proof of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def tauLineProj (f : PauliLinePoly P) :
    Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      restrictToLine P.toLdParams line (lowDegreeEncoding h) = f),
    pauliProj W h

/-- Pauli line readout is a deterministic relabeling of a Pauli register. -/
noncomputable def tauLineMeas :
    Measurement (PauliLinePoly P) (PauliRegister P) :=
  (pauliRegisterMeas W).postprocess (fun h => restrictToLine P.toLdParams line (lowDegreeEncoding h))

theorem tauLineMeas_isProjective : Measurement.IsProjective (tauLineMeas P W line) :=
  SandwichProduct.postprocess_isProjective _ (pauliRegisterMeas_isProjective W) _

/-- On an axis-parallel line, Pauli line projectors vanish outside the
embedded degree-`d` subspace, because every restricted low-degree encoding has
degree at most `d` there. This is the ancillary half of the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem tauLineProj_eq_zero_of_axis (haxis : line.kind = .axis)
    (f : PauliLinePoly P) (hf : ¬ f.FitsDegree P.d) :
    tauLineProj P W line f = 0 := by
  classical
  unfold tauLineProj
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  apply hf
  rw [← (Finset.mem_filter.mp he).2]
  exact restrictToLine_lowDegreeEncoding_fitsDegree_of_axis P.toLdParams line
    haxis e

end

end

end MIPStarRE.QPBT
