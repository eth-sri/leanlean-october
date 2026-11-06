module

public import QPBT.Combining.Lines.Construction
public import QPBT.Combining.Lines.CombinedMeasurement
public import QPBT.Combining.Lines.ConsistencyPositivity
public import QPBT.Games.RestrictedAverage
public import QPBT.Combining.Lines.ConditionalCollision
public import QPBT.Combining.Lines.AxisLineResampling
public import QPBT.Combining.Lines.DiagonalResampling
public import QPBT.Combining.Lines.MixedResampling
public import QPBT.Combining.Lines.ProductWeightedCollision
public import QPBT.Combining.Lines.NondegeneratePastingDistribution
public import QPBT.Combining.Lines.NondegeneratePastingMass
public import QPBT.Combining.Lines.PairStateConsistencyTransport
public import QPBT.Combining.Lines.RestrictedAverage
public import QPBT.Combining.Lines.SubLineMixture
public import QPBT.Combining.Lines.UniformAffineCollision
public import QPBT.Combining.Lines.WeightedCollision
public import QPBT.Combining.Lines.PointwiseDefect
public import QPBT.Combining.Lines.Conditioning
public import QPBT.Combining.Points
public import QPBT.Combining.Witnesses
public import QPBT.Combining.Lines.AffineEvaluation
public import QPBT.Combining.Lines.FiberCollision
public import QPBT.Combining.Lines.ZeroDirectionMass

/-!
# Combined lines and restricted line distributions

This module states the construction of the joint X/Z line measurements, the
mixture and error-inflation estimates for restricted line distributions, and
the sub-line distribution used to combine the two bases.  The extended line
in the sub-line construction uses the directly indexed carrier, so the
sub-line statement is a formalization auxiliary assertion and carries no
divisibility hypothesis at dimension `2 * m + 2`.

## References

The declarations formalize `lem:qld-xz-lines` and
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; `exists_subLineWitness`
instead supports `lem:qld-sublines` through the directly indexed extended-line
carrier and probability law.  Their paper sources
are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1069`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Combined line measurements -/

/-- Conditional joint X/Z line measurements for a polynomially controlled
point-witness family supporting `lem:qld-xz-lines`.

**Conditional auxiliary supporting:** blueprint
`lem:qld-xz-lines`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`.
The matching conditional blueprint entry is `lem:combined-lines-given-points`.
The error depends polynomially on `ε` and `md/q`, and the witness retains all
directed opposite-placement comparisons. This formalization-only conditional form
takes the supplied point-error function `deltaQ` and its bound `hdeltaQ : IsPolyErr deltaQ`
before choosing the line-error function. It also assumes a supplied point witness
`points : CombinedPointsWitness S (deltaQ ε)` at strategy error `ε`.
The separate source-facing declaration `exists_combinedLinesWitness` supplies
the point-error function, its bound, and the point witness existentially.
The comparisons here use the completed answer alphabet; the conditional entry
does not certify the source comparison on field-valued answers.

**Domain repair (issue Dengnifer/MIPStarRE-QPBT-bak#389):** The former statement quantified an
arbitrary
scalar point error after choosing `deltaP`, although the pasting estimate depends
on that point error.  The repaired domain matches the point family supplied by
`exists_combinedPointsWitness`.  The source-facing theorem below still supplies
that family existentially and has an unchanged statement.  The obstruction and
the named construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The witness below uses `S.combinedLineMeasurement` explicitly. Its consistency
is proved by the point-to-line comparisons and pasting construction; see
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#414.

**Error contract:** the polynomial bound printed in the source is carried
by `IsPolyErr₂`, which states the corrected sum form
`f x y ≤ C * (x ^ r + y ^ s)` with `1 ≤ C` and positive exponents on the
closed nonnegative quadrant, in place of the product form `C * (x * y) ^ C`
of the source shorthand at `04_preliminaries.tex:22-29`.  The correction and
the two-dimensional strategy that refutes the product form are recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex` and tracked by issue
Dengnifer/MIPStarRE-QPBT-bak#196.
Here `poly(ε, md/q)` is read in that sense. -/
theorem exists_combinedLinesWitness_ofPointsWitness (deltaQ : ℝ -> ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ -> ℝ -> ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε)),
        Nonempty (CombinedLinesWitness S points
          (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨deltaP, hdeltaP, hconsistent⟩ :=
    combined_line_measurement_consistency deltaQ hdeltaQ
  refine ⟨deltaP, hdeltaP, ?_⟩
  intro P ε S points
  exact ⟨{ T := S.combinedLineMeasurement
           axis_degree_X := S.combinedLineMeasurement_axis_degree_X
           axis_degree_Z := S.combinedLineMeasurement_axis_degree_Z
           consistent := hconsistent P ε S points }⟩

/-! The source-facing declaration below supplies the point witness produced by
`lem:qld-4-10` existentially.  The `_ofPointsWitness` companion above is the
conditional form for a supplied polynomially controlled point family. -/

/-! ## Restricted line distributions -/

/-! ## The sub-line distribution -/

/-- Existence of the directly indexed sub-line distribution with its two
separate projected point marginals and axis-line closure.  It supports
`lem:qld-sublines` and `rem:qld-sublines-property-three` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1069` with
its proof at lines 1071--1116.

This is a formalization auxiliary assertion, not the source-labelled
`lem:qld-sublines`.  The extended line uses the directly indexed carrier and
line-point law of `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` in
place of the seed-indexed line-point distribution over `F_q^(2m+2)` of the
source statement, so the statement carries no divisibility hypothesis and its
transport to the source carrier remains open.  Its `source_mixture` field
asserts only the separate X and Z marginal mixtures, not a stronger joint
conditional law.

The witness is the sub-line law `subLineDist` of the sampling procedure.  Its
pointwise fields follow from `subLineTripleOf_incidence`,
`subLineTripleOf_compatibility`, and `subLineTripleOf_axis_closure`, after
recovering the sampling data with `exists_samplingData_of_mem_subLineDist_support`.
Its extended-line marginal is `subLineDist_map_fst`, and its two projected
point marginals are the separate mixtures of `subLineDist_source_mixture`. -/
theorem exists_subLineWitness (P : AdmissibleParams) :
    Nonempty (SubLineWitness P) := by
  refine ⟨{ D := subLineDist P
            isProbability := subLineDist_isProbability P
            extended_marginal := subLineDist_map_fst P
            compatibility := ?_
            source_mixture := subLineDist_source_mixture P
            axis_closure := ?_ }⟩
  · intro sample hsample
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_samplingData_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_compatibility P kind k w hx hz
  · intro sample hsample haxis
    obtain ⟨kind, k, w, _, _, rfl⟩ :=
      exists_samplingData_of_mem_subLineDist_support P hsample
    exact subLineTripleOf_axis_closure P kind k w haxis

end

end MIPStarRE.QPBT
