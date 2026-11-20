module

public import QPBT.Combining.ExtendedLineGame.StateTransport
public import QPBT.Combining.Points.Placement
public import QPBT.Extraction.Observables
public import QPBT.Extraction.NonencodingSupport

/-!
# Consistency of the pulled-apart Pauli measurements

This module records the two estimates by which the polynomial marginals absorb
the expanded point measurements, with all heterogeneous placements written
explicitly. It also defines the mass of non-encoding marginal outcomes and
states the support estimate needed by the corrected decoder calculation.

The marginal agreement estimates and reverse-placement correlation transports
are developed from a supplied global polynomial-pair witness.

## References

The marginal estimates formalize blueprint
`lem:qld-constructing-the-paulis-helper`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1609-1664`.
The non-encoding support obligation contributes to blueprint
`lem:qld-construct-the-paulis`, from paper lines 1458-1608; see
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open ProjectiveSetting

noncomputable section

/-! ## Absorption of expanded point measurements -/

section

variable {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (w : GlobalPairWitness S δ)
include P ε δ S w

/-- Regrouping the polynomial outcomes by any scalar readout preserves the agreement operator. -/
theorem sum_marginalPoly_readout_mul (p : Placement) (W : PauliKind)
    (f : Poly P → PauliScalar P) (B : PauliScalar P → Op (S.ExpandedSpace)) :
    (∑ a, S.place p (((w.marginalPoly p.side W).postprocess f).effect a) * B a) =
      ∑ g, S.place p ((w.marginalPoly p.side W).effect g) * B (f g) := by
  simp only [Measurement.postprocess_effect, place_finsetSum, Finset.sum_mul, Finset.sum_fiberwise_apply]

/-- The defect after reading a polynomial marginal at a point, against the crossed point measurement. -/
abbrev marginalReadoutDefect (p q : Placement) (W : PauliKind)
    (f : (PauliPoint P) → Poly P → PauliScalar P) : ℝ :=
  S.placedDefect p q (uniformDistribution (PauliPoint P))
    (fun u => (w.marginalPoly p.side W).postprocess (f u)) (S.pointMeasExp q.side W)

/-- Evaluating the marginal retains the witness consistency with the opposite expanded points. -/
theorem marginalPoly_pointMeas_consistent {p : Placement}
    (hp : p.Primary) (W : PauliKind) :
    marginalReadoutDefect w p (overlapPartner p) W (fun u g => evalPoly g u) ≤ δ := by
  simpa only [marginalReadoutDefect, w.marginalPoly_postprocess_eval] using w.point_consistent hp W

end

/-! ## Non-encoding support -/

/-- The state-dependent mass assigned by a side's polynomial marginal to
outcomes outside the low-degree encoding image.  The finite support filter is
written explicitly so the restricted decoder identity is never applied to an
arbitrary polynomial representative.

This is the left-hand side of blueprint
`eq:qld-nonencoding-mass`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1458-1602`.
The support estimate is proved separately from the decoder identity; see
`docs/paper-gaps/qpbt_decoding-identity.tex`. -/
noncomputable def nonencodingMarginalMass {P : AdmissibleParams}
    {epsilon deltaS : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaS) (side : PlayerSide) (W : PauliKind) : ℝ := by
  classical
  exact ∑ g ∈ Finset.univ.filter (fun g : Poly P => ¬ IsEncoding g),
    DistanceCalculus.stateQForm S.psiHat
      (S.placeSide side (heteroKron ((w.marginalPoly side W).effect g) (1 : Op (PauliRegister P))))

end

end MIPStarRE.QPBT
