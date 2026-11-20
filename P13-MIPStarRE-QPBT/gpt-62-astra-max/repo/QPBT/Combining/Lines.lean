module

public import QPBT.Combining.Lines.Construction
public import QPBT.Combining.Lines.PairStateConsistencyTransport

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
            isProbability := (by
                               refine Distribution.bind_isProbability _ _
                                 (uniformDistribution_isProbability _) fun c _ => ?_
                               fin_cases c
                               · exact Distribution.IsProbability.map (subLineSamplingDist_isProbability P) _
                               · exact Distribution.IsProbability.map (subLineSamplingDist_isProbability P) _)
            extended_marginal := (by
                                   classical
                                   have haxis : (subLineBranchDist P .axis).map Prod.fst =
                                       (directALinePointDist P.extendedDirectLd).map Prod.fst := by
                                     rw [subLineBranchDist_map_fst, directALinePointDist, Distribution.map_map]
                                     rfl
                                   have hdiag : (subLineBranchDist P .diagonal).map Prod.fst =
                                       (directDLinePointDist P.extendedDirectLd).map Prod.fst := by
                                     rw [subLineBranchDist_map_fst, directDLinePointDist, Distribution.map_map]
                                     rfl
                                   rw [subLineDist, Distribution.bind_map, directLinePointDist,
                                     ← Distribution.bind_uniform_fin_two, Distribution.bind_map]
                                   refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
                                   fin_cases c
                                   · exact haxis
                                   · exact hdiag)
            incidence := ?_
            compatibility := ?_
            source_mixture := (⟨subLineComponentDist P, (by
                                                          refine Distribution.bind_isProbability _ _
                                                            (uniformDistribution_isProbability _) fun c _ => ?_
                                                          fin_cases c
                                                          · exact Distribution.IsProbability.map
                                                              (uniformDistribution_isProbability _) _
                                                          · exact Distribution.IsProbability.map
                                                              (uniformDistribution_isProbability _) _),
                                subLineDist_map_subLineXProjection P,
                                subLineDist_map_subLineZProjection P⟩)
            axis_closure := ?_ }⟩
  · intro sample hsample u hu
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_samplingData_of_mem_subLineDist_support hsample
    exact ⟨projX_mem_pointSet P _ _ _ (subLineTripleOf_xBase kind hx)
              (subLineTripleOf_xSpan kind hx) hu,
            projZ_mem_pointSet P _ _ _ (subLineTripleOf_zBase kind hz)
              (subLineTripleOf_zSpan kind hz) hu⟩
  · intro sample hsample
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_samplingData_of_mem_subLineDist_support hsample
    solve_by_elim [subLineTripleOf_compatibility]
  · intro sample hsample haxis
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      exists_samplingData_of_mem_subLineDist_support hsample
    have hkind : kind = .axis := by
      have h : (subLineExtLine P kind k w).kind = kind := by cases kind <;> rfl
      rw [← h]
      exact haxis
    subst hkind
    constructor <;> assumption

end

end MIPStarRE.QPBT
