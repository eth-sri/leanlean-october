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

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open ProjectiveSetting

noncomputable section

/-! ## Absorption of expanded point measurements -/

namespace GlobalPairWitness

/-- Evaluating a single-basis marginal is the same finite postprocessing as
evaluating the corresponding component of the joint polynomial outcome. This
is the coarse-graining in the proof of blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`. -/
theorem marginalPoly_postprocess_eval {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (point : MIPStarRE.QPBT.PauliPoint P) :
    (w.marginalPoly side W).postprocess (fun poly => MvPolynomial.eval point poly.1) =
      (w.Smeas side).postprocess (evalAt W point) := by
  rw [marginalPoly, MIPStarRE.Quantum.Measurement.postprocess_comp]
  cases W <;> rfl

end GlobalPairWitness

/-- Regrouping polynomial outcomes by their value at a point preserves the
agreement operator. This is the finite-sum identity behind paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`, blueprint
`lem:qld-constructing-the-paulis-helper`. -/
theorem sum_marginalPoly_eval_mul {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (placement : Placement) (W : PauliKind) (point : MIPStarRE.QPBT.PauliPoint P)
    (family : PauliScalar P → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB)) :
     ∑ answer : PauliScalar P, S.place placement
      (((w.marginalPoly placement.side W).postprocess
         fun poly => MvPolynomial.eval point poly.1 ).effect answer) * family answer  =
      ∑ poly : Poly P, S.place placement ((w.marginalPoly placement.side W).effect poly) *
        family (MvPolynomial.eval point poly.1) := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, place_finsetSum,
    Finset.sum_mul]
  calc
    _ = ∑ answer : PauliScalar P,
        ∑ poly ∈ Finset.univ.filter  fun poly : Poly P =>
          MvPolynomial.eval point poly.1 = answer ,
          S.place placement ((w.marginalPoly placement.side W).effect poly) *
            family (MvPolynomial.eval point poly.1) := by
      apply Finset.sum_congr rfl
      intro answer _
      apply Finset.sum_congr rfl
      intro poly hpoly
      rw [(Finset.mem_filter.mp hpoly).2]
    _ = _ := Finset.sum_fiberwise _ _ _

/-- Alice's evaluated marginal on `AA'` retains the witness consistency with
Bob's expanded point measurement on `BA''`. This is the direct placement in
paper `14_analysis_of_the_pauli_basis_test.tex:1626-1637`, supporting blueprint
`lem:qld-constructing-the-paulis-helper`; no register transfer is used. -/
theorem marginalPoly_pointMeas_consistent_alice {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (MIPStarRE.QPBT.PauliPoint P))
      (fun point answer => S.place .AA'
        (((w.marginalPoly .alice W).postprocess
           fun poly => MvPolynomial.eval point poly.1 ).effect answer))
      (fun point answer => S.place .BA''
        ((S.pointMeasExp .bob W point).effect answer)) S.psiHat ≤ deltaG := by
  simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent_alice W

/-- Bob's evaluated marginal on `BB'` retains the witness consistency with
Alice's expanded point measurement on `AB''`. This is the reverse-player
direct placement of paper `14_analysis_of_the_pauli_basis_test.tex:1626-1637`,
supporting blueprint `lem:qld-constructing-the-paulis-helper`; no register
transfer is used. -/
theorem marginalPoly_pointMeas_consistent_bob {P : AdmissibleParams}
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (MIPStarRE.QPBT.PauliPoint P))
      (fun point answer => S.place .BB'
        (((w.marginalPoly .bob W).postprocess
           fun poly => MvPolynomial.eval point poly.1 ).effect answer))
      (fun point answer => S.place .AB''
        ((S.pointMeasExp .alice W point).effect answer)) S.psiHat ≤ deltaG := by
  simpa only [w.marginalPoly_postprocess_eval] using w.point_consistent_bob W

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
def nonencodingMarginalMass {P : AdmissibleParams}
    {epsilon deltaS : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaS) (side : PlayerSide) (W : PauliKind) : ℝ := by
  exact ∑ g ∈ Finset.univ.filter  fun g : Poly P => ¬ IsEncoding g ,
    (inner ℂ S.psiHat
      (applyOperatorToState
        (S.placeSide side
          (heteroKron ((w.marginalPoly side W).effect g)
            (1 : Op (PauliRegister P))))
        S.psiHat)).re

end

end MIPStarRE.QPBT
