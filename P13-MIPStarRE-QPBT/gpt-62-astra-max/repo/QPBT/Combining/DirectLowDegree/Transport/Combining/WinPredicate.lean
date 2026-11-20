module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.QuestionLaw

/-!
# Branch-wise acceptance transport for the combined strategy

By `directRejectedMass_directCombinedStrategy_le`, the branch-wise estimates of
`lem:ld-combined-value` reduce to the following statement: the relabelling of
`def:ld-combined-strategy` sends an answer pair accepted by the win predicate
of the original game at the measured questions to an answer pair accepted by
the win predicate of the combined game.  This module proves that statement for
each of the nine ordered type pairs of the combined game.

Three of the nine branches are deterministic.  The two questions of a branch
whose type pair is diagonal are equal, so the acceptance clause of the original
game forces the two measured outcomes to be equal, and the relabelling, being a
function, sends them to equal combined outcomes.  The two branches pairing an
axis-parallel line with a diagonal line impose no condition in either game.

The six remaining branches pair a line with a point, and split according to
whether the stored coordinate index of the common sample is a point coordinate
or a combining coordinate.  On a point coordinate the acceptance clause of the
combined game is obtained from the acceptance clause of the original game by
the affine change of parameter `directCombinedRebaseParameter`: the parameter
presenting the sampled point on the sampled line of the combined space presents
the point part of the sampled point on the image line, after the shift.  On a
combining coordinate the sampled line lies in a fiber of the projection to the
point coordinates, the combining part of the sampled point is the affine
function `α₀ + t w` of the parameter, and the acceptance clause of the combined
game is the identity `∑ r (α₀ + t w)_r b_r = ∑ r α_r b_r`.

All declarations below are formalization-only support for
`lem:ld-combined-value`; none is a paper-labelled result.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two parts of a point along a line -/

section

variable (D : DirectLdParams) {i : Fin D.combined.m} (n : ℕ)
  (p : Fin D.combined.m → DirectScalarQ D) (q : DirectLdQuestion D)
  (V : Fin D.combined.m → DirectScalarQ D) (hn : 1 ≤ n)
  (z base dir : Fin D.combined.m → DirectScalarQ D) (a : DirectLdAnswer D)
  (dirn : Fin D.combined.m → DirectScalarQ D) (hcoef : directCombinedCoefficientPart D dir = 0)
  (hdir : directCombinedCoefficientPart D dirn = 0) (s T : DirectScalarQ D)
  (b : Fin D.k → DirectScalarQ D) (t : DirectScalarQ D)
  (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D) (c : Fin D.k → DirectScalarQ D)
  (hf : ∀ r, evalCoefficient (f r) (t + s) = c r) (ht : z = base + t • dirn)

theorem directCombinedPointPart_add_smul :
    directCombinedPointPart (p + t • V) =
      directCombinedPointPart p + t • directCombinedPointPart V := rfl

theorem directCombinedCoefficientPart_add_smul :
    directCombinedCoefficientPart D (p + t • V) =
      directCombinedCoefficientPart D p + t • directCombinedCoefficientPart D V := rfl

/-- The coordinate direction of a point coordinate of the combined dimension
has vanishing combining part. -/
@[simp] theorem directCombinedCoefficientPart_coordinateDirection_pointVar (j : Fin D.m) :
    directCombinedCoefficientPart D
        (coordinateDirection (combinedPointVar D.m D.k j)) = 0 := by
  funext r
  show (coordinateDirection (combinedPointVar D.m D.k j)) (combinedCoefficientVar D.m D.k r) = 0
  rw [coordinateDirection,
    Pi.single_eq_of_ne (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j)]

/-! ## Degree bounds at the combined parameters -/

private theorem diagonalDegreeBound :
    D.m * D.d + 1 ≤ D.combined.m * D.combined.d := by
  have h1 := Nat.mul_le_mul D.hk D.hd
  rw [← (Nat.add_mul _ _ _).symm]
  bound

/-! ## Evaluation of the combined answers -/

include ht hn in
/-- Evaluation of the answer of cases 3 and 5 of `def:ld-combined-strategy`:
along a line contained in a fiber of the projection to the point coordinates,
the combining part of the point at parameter `t` is `α₀ + t w`, so the affine
answer built from the measured point answer `b` takes at `t` the combined
value of `b` at that point. -/
private theorem fiberAnswerEval :
    evalCoefficient
        (coefficientsOfPolynomial n
          (fiberLinePolynomial (directCombinedCoefficientPart D base)
            (directCombinedCoefficientPart D dirn) b)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * b r := by
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D base +
        t • directCombinedCoefficientPart D dirn := by
    conv_lhs => rw [ht]
    rfl
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (fiberLinePolynomial_natDegree_le _ _ _) hn),
    fiberLinePolynomial_eval, hz]
  rfl

include ht hf hdir in
/-- Evaluation of the answer of case 2 of `def:ld-combined-strategy`: along an
axis-parallel line of the combined space with a point coordinate as stored
index, the combining part of the sampled point equals that of the canonical
base, and the shifted parameter presents the point part of the sampled point on
the measured line. -/
private theorem axisAnswerEval :
    evalCoefficient
        (coefficientsOfPolynomial D.combined.d
          (combinedAxisPolynomial (directCombinedCoefficientPart D base) s f)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hz : directCombinedCoefficientPart D z = directCombinedCoefficientPart D base := by
    conv_lhs => rw [ht]
    rw [directCombinedCoefficientPart_add_smul, hdir, smul_zero, add_zero]
  simp [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedAxisPolynomial_natDegree_le _ _ _)
        (le_of_eq (rfl).symm)), combinedAxisPolynomial_eval]
  simp_all

/-- Evaluation of the answer of case 4 of `def:ld-combined-strategy`: along a
diagonal line of the combined space with a point coordinate as stored index,
the combining part of the point at parameter `t` is `α₀ + t w`, and the shifted
parameter presents the point part of that point on the measured line. -/
private theorem diagonalAnswerEval
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hf : ∀ r, evalCoefficient (f r) (t + s) = c r)
    (ht : z = base + t • dirn) :
    evalCoefficient
        (coefficientsOfPolynomial (D.combined.m * D.combined.d)
          (combinedDiagonalPolynomial (directCombinedCoefficientPart D base)
            (directCombinedCoefficientPart D dirn) s f)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D base +
        t • directCombinedCoefficientPart D dirn := by
    conv_lhs => rw [ht]
    rfl
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedDiagonalPolynomial_natDegree_le _ _ _ _)
        (diagonalDegreeBound D)),
    combinedDiagonalPolynomial_eval, hz]
  simp_all

/-! ## Structural clauses of the win predicate -/

/-- An answer pair accepted at two equal questions of the directly indexed game
consists of two equal answers: the three diagonal clauses of
`def:ld-win-predicate` are equalities of answers. -/
theorem directLdAnswer_eq_of_win_self {a b : DirectLdAnswer D}
    (hwin : directLdWinPredicate D q q a b = true) : a = b := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;> cases b <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- Two equal answers of the correct constructor are accepted at two equal
questions of the directly indexed game. -/
theorem directLdWinPredicate_self (hvalid : validDirectLdAnswer q.1 a = true) :
    directLdWinPredicate D q q a a = true := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- The relabelling of `def:ld-combined-strategy` always produces an answer of
the constructor required by the type of the combined question. -/
theorem validDirectLdAnswer_directCombinedAnswerMap
    (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) :
    validDirectLdAnswer q.1 (directCombinedAnswerMap D q a) = true := by
  obtain ⟨t, xq⟩ := q
  cases t
  · rfl
  all_goals rcases hsplit : directCombinedIndexSplit xq.index with j | r <;>
        simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]

/-- An ordered pair of a well-formed axis-parallel line answer and a well-formed
diagonal line answer is accepted: `def:ld-win-predicate` imposes no condition on
that ordered type pair. -/
theorem directLdWinPredicate_aline_dline
    (xq yq : DirectLdSpace D) (a b : DirectLdAnswer D)
    (ha : validDirectLdAnswer LdType.aline a = true)
    (hb : validDirectLdAnswer LdType.dline b = true) :
    directLdWinPredicate D (.aline, xq) (.dline, yq) a b = true := by
  simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- A coordinate index of the combined dimension split off as a point
coordinate is that point coordinate. -/
theorem eq_combinedPointVar_of_indexSplit {j : Fin D.m}
    (h : directCombinedIndexSplit i = Sum.inl j) :
    i = combinedPointVar D.m D.k j := by
  have hi : finSumFinEquiv (directCombinedIndexSplit i) =
      _ := congrArg _ h
  simp [directCombinedIndexSplit] at hi
  exact hi

/-- A coordinate index of the combined dimension split off as a combining
coordinate is that combining coordinate. -/
theorem eq_combinedCoefficientVar_of_indexSplit {r : Fin D.k}
    (h : directCombinedIndexSplit i = Sum.inr r) :
    i = combinedCoefficientVar D.m D.k r := by
  have hi : finSumFinEquiv (directCombinedIndexSplit i) =
      _ := congrArg _ h
  simp [directCombinedIndexSplit] at hi
  exact hi

/-! ## The acceptance clause on a point coordinate -/

include hcoef in
/-- Case 2 of `def:ld-combined-strategy` at the parameter presenting the
sampled point: the affine shift `s` relating the two presentations of the image
line carries the acceptance clause of the original game at the shifted
parameter to the acceptance clause of the combined game. -/
theorem directCombinedAxisAnswer_eval
    (hs : directCombinedPointPart (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart dir)
          (directCombinedPointPart (lineRepMap dir z)) +
        s • directCombinedPointPart dir)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D) (c : Fin D.k → DirectScalarQ D)
    (hT : z = lineRepMap dir z + T • dir)
    (hcond : ∀ t : DirectScalarQ D,
      directCombinedPointPart z =
          lineRepMap (directCombinedPointPart dir) (directCombinedPointPart z) +
            t • directCombinedPointPart dir →
        ∀ r, evalCoefficient (f r) t = c r) :
    evalCoefficient
        (coefficientsOfPolynomial D.combined.d
          (combinedAxisPolynomial
            (directCombinedCoefficientPart D (lineRepMap dir z)) s f)) T =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hbase := lineRepMap_directCombinedPointPart_lineRepMap D dir z
  refine axisAnswerEval D z _ dir hcoef s T f c (hcond _ ?_) hT
  conv_lhs => rw [hT]
  rw [directCombinedPointPart_add_smul, hs, hbase]
  module

/-- Case 4 of `def:ld-combined-strategy` at the parameter presenting the
sampled point. -/
theorem directCombinedDiagonalAnswer_eval
    (hs : directCombinedPointPart (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart dir)
          (directCombinedPointPart (lineRepMap dir z)) +
        s • directCombinedPointPart dir)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hT : z = lineRepMap dir z + T • dir)
    (hcond : ∀ t : DirectScalarQ D,
      directCombinedPointPart z =
          lineRepMap (directCombinedPointPart dir) (directCombinedPointPart z) +
            t • directCombinedPointPart dir →
        ∀ r, evalCoefficient (f r) t = c r) :
    evalCoefficient
        (coefficientsOfPolynomial (D.combined.m * D.combined.d)
          (combinedDiagonalPolynomial
            (directCombinedCoefficientPart D (lineRepMap dir z))
            (directCombinedCoefficientPart D dir) s f)) T =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hbase := lineRepMap_directCombinedPointPart_lineRepMap D dir z
  refine diagonalAnswerEval D z _ dir s T f c (hcond _ ?_) hT
  conv_lhs => rw [hT]
  rw [directCombinedPointPart_add_smul, hs, hbase]
  module

end

/-! ## The branch-wise acceptance transport -/

variable (D : DirectLdParams) (t t₁ t₂ : LdType) (sample : DirectLdSpace D.combined)

/-- The acceptance transport of `lem:ld-combined-value` on one ordered type
pair: the relabelling of `def:ld-combined-strategy` sends an answer pair
accepted by the win predicate of the original game at the measured questions to
an answer pair accepted by the win predicate of the combined game. -/
def DirectCombinedWinTransport : Prop :=
  ∀ a b : DirectLdAnswer D,
    directLdWinPredicate D
        (directCombinedMeasuredQuestion (t₁, directLdMap t₁ sample))
        (directCombinedMeasuredQuestion (t₂, directLdMap t₂ sample))
        a b = true →
      directLdWinPredicate D.combined
        (t₁, directLdMap t₁ sample) (t₂, directLdMap t₂ sample)
        (directCombinedAnswerMap D (t₁, directLdMap t₁ sample) a)
        (directCombinedAnswerMap D (t₂, directLdMap t₂ sample) b) = true

private theorem DirectCombinedWinTransport.swap {D : DirectLdParams} {i j : LdType}
    {s : DirectLdSpace D.combined} (h : DirectCombinedWinTransport D i j s) :
    DirectCombinedWinTransport D j i s := by
  intro a b hw
  rw [directLdWinPredicate_swap] at hw ⊢
  solve_by_elim [h]

/-- The axis-parallel-line versus point branch. -/
theorem directCombinedWinTransport_aline_point :
    DirectCombinedWinTransport D .aline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit sample.index with j | r₀
  · have hindex :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .aline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a with
    | pointVals _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
    | dlinePolys _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
    | alinePolys f =>
      cases b with
      | alinePolys _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
      | dlinePolys _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
      | pointVals c =>
        have hsplitL : directCombinedIndexSplit
            (directLdMap LdType.aline sample).index = Sum.inl j := hsplit
        have hcond : directAlinePointCondition D
            (directLdMap .aline (directCombinedSampleProjection D j sample))
            (directLdMap .point (directCombinedSampleProjection D j sample))
            f c := by
          simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
        have hdirpt : directCombinedPointPart (coordinateDirection sample.index) =
            coordinateDirection j := by
          simp_all
        have hcoef : directCombinedCoefficientPart D
            (coordinateDirection sample.index) = 0 := by
          simp_all
        have hmdir : directCombinedMeasuredDirection D
            (LdType.aline, directLdMap LdType.aline sample) =
            directCombinedPointPart (coordinateDirection sample.index) := by
          simp_all [directCombinedMeasuredDirection, directLdMap, directCombinedIndexSplit_combinedPointVar, directCombinedPointPart_coordinateDirection_pointVar]
        have hs : directCombinedPointPart (D := D)
              (lineRepMap (coordinateDirection sample.index) sample.point) =
            lineRepMap (directCombinedPointPart (coordinateDirection sample.index))
                (directCombinedPointPart (D := D)
                  (lineRepMap (coordinateDirection sample.index) sample.point)) +
              directCombinedRebaseParameter D
                  (LdType.aline, directLdMap LdType.aline sample) •
                directCombinedPointPart (coordinateDirection sample.index) := by
          rw [← hmdir]
          apply directLineRepParameter_spec
        have hmapA : directCombinedAnswerMap D
            (LdType.aline, directLdMap LdType.aline sample) (.alinePolys f) =
            .alinePolys (fun _ => coefficientsOfPolynomial D.combined.d
                (combinedAxisPolynomial
                  (directCombinedCoefficientPart D
                    (directLdMap LdType.aline sample).point)
                  (directCombinedRebaseParameter D
                    (LdType.aline, directLdMap LdType.aline sample)) f)) := by
          simp [directCombinedAnswerMap, hsplitL]
        have hmapB : directCombinedAnswerMap D
            (LdType.point, directLdMap LdType.point sample) (.pointVals c) =
            .pointVals _ := rfl
        rw [hmapA, hmapB]
        simpa [directLdWinPredicate, validDirectLdAnswer] using (by
          intro T hT _
          apply directCombinedAxisAnswer_eval <;> try assumption
          rw [hdirpt]
          exact hcond)
  · have hindex :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    simp [directCombined_measuredQuestion_of_coefficientVar D .aline r₀ sample hindex] at hwin
    have hab := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
    | dlinePolys _ =>
      simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
    | pointVals bv =>
      have hsplitL : directCombinedIndexSplit
          (directLdMap LdType.aline sample).index = Sum.inr r₀ := hsplit
      have hmapB : directCombinedAnswerMap D
          (LdType.point, directLdMap LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap LdType.point sample).point r * bv r) := rfl
      simp [directCombinedAnswerMap, hsplitL]
      simpa [directLdWinPredicate, validDirectLdAnswer] using (by
        intro T hT _
        exact fiberAnswerEval D D.combined.d D.hd
          _
          _
          _ bv T hT)

/-- The diagonal-line versus point branch. -/
theorem directCombinedWinTransport_dline_point :
    DirectCombinedWinTransport D .dline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit sample.index with j | r₀
  · have hindex :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .dline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a with
    | pointVals _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
    | alinePolys _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
    | dlinePolys f =>
      cases b with
      | alinePolys _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
      | dlinePolys _ => simp_all [directLdWinPredicate, validDirectLdAnswer]
      | pointVals c =>
        have hsplitL : directCombinedIndexSplit
            (directLdMap LdType.dline sample).index = Sum.inl j := hsplit
        have hcond : directDlinePointCondition D
            (directLdMap .dline (directCombinedSampleProjection D j sample))
            (directLdMap .point (directCombinedSampleProjection D j sample))
            f c := by
          simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
        have hdirpt : directCombinedPointPart (directPrefixProjection sample.index
          sample.direction) =
            directPrefixProjection j
              (directCombinedPointPart sample.direction) := by
          simp_all
        have hmdir : directCombinedMeasuredDirection D
            (LdType.dline, directLdMap LdType.dline sample) =
            directCombinedPointPart (directPrefixProjection sample.index sample.direction) := by
          simp_all [directCombinedMeasuredDirection, directLdMap, directCombinedIndexSplit_combinedPointVar, directCombinedPointPart_directPrefixProjection_pointVar, directPrefixProjection_idem]
        have hs : directCombinedPointPart
              (lineRepMap (directPrefixProjection sample.index sample.direction) sample.point) =
            lineRepMap (directCombinedPointPart (directPrefixProjection sample.index
              sample.direction))
                (directCombinedPointPart
                  (lineRepMap (directPrefixProjection sample.index sample.direction) sample.point))
                    +
              directCombinedRebaseParameter D
                  (LdType.dline, directLdMap LdType.dline sample) •
                directCombinedPointPart (directPrefixProjection sample.index sample.direction) :=
                  by
          rw [← hmdir]
          apply directLineRepParameter_spec
        have hmapA : directCombinedAnswerMap D
            (LdType.dline, directLdMap LdType.dline sample) (.dlinePolys f) =
            .dlinePolys (fun _ => coefficientsOfPolynomial _
                (combinedDiagonalPolynomial
                  (directCombinedCoefficientPart D (directLdMap LdType.dline
                    sample).point)
                  (directCombinedCoefficientPart D
                    (directCombinedQuestionDirection D (LdType.dline, directLdMap
                      LdType.dline sample)))
                  (directCombinedRebaseParameter D
                    (LdType.dline, directLdMap LdType.dline sample)) f)) := by
          simp [directCombinedAnswerMap, hsplitL]
        have hmapB : directCombinedAnswerMap D
            (LdType.point, directLdMap LdType.point sample) (.pointVals c) =
            .pointVals _ := rfl
        rw [hmapA, hmapB]
        simpa [directLdWinPredicate, validDirectLdAnswer] using (by
          intro T hT _
          apply directCombinedDiagonalAnswer_eval <;> try assumption
          rw [hdirpt]
          exact hcond)
  · have hindex :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    simp [directCombined_measuredQuestion_of_coefficientVar D .dline r₀ sample hindex] at hwin
    have hab := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a with
    | alinePolys _ =>
      simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
    | dlinePolys _ =>
      simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
    | pointVals bv =>
      have hsplitL : directCombinedIndexSplit
          (directLdMap LdType.dline sample).index = Sum.inr r₀ := hsplit
      have hmapB : directCombinedAnswerMap D
          (LdType.point, directLdMap LdType.point sample) (.pointVals bv) =
          .pointVals (fun _ => ∑ r : Fin D.k, directCombinedCoefficientPart D
            (directLdMap LdType.point sample).point r * bv r) := rfl
      simp [directCombinedAnswerMap, hsplitL]
      simpa [directLdWinPredicate, validDirectLdAnswer] using (by
        intro T hT _
        exact fiberAnswerEval D _ ((Nat.mul_le_mul D.combined.hm D.combined.hd))
          _
          _
          _ bv T hT)

/-- A branch whose ordered type pair is diagonal: the two questions of the
combined game are equal, so the acceptance clause of the original game at the
two equal measured questions forces the two measured outcomes to be equal, and
the relabelling sends them to equal combined outcomes. -/
theorem directCombinedWinTransport_diagonal :
    DirectCombinedWinTransport D t t sample := by
  intro a b hwin
  have hab := directLdAnswer_eq_of_win_self D _ hwin
  subst hab
  exact directLdWinPredicate_self D.combined _ _
    (validDirectLdAnswer_directCombinedAnswerMap D
      _ a)

/-- The axis-parallel-line versus diagonal-line branch: the win predicate of
the combined game imposes no condition on that ordered type pair. -/
theorem directCombinedWinTransport_aline_dline :
    DirectCombinedWinTransport D .aline .dline sample := by
  intro a b _
  exact directLdWinPredicate_aline_dline D.combined _ _ _ _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.aline, directLdMap LdType.aline sample) a)
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.dline, directLdMap LdType.dline sample) b)

/-- The acceptance transport of `lem:ld-combined-value` on every one of the
nine ordered type pairs of the combined game.  This is the hypothesis of
`directRejectedMass_directCombinedStrategy_le` at the question pair attached to
a sample of the combined game. -/
theorem directCombinedWinTransport_all :
    DirectCombinedWinTransport D t₁ t₂ sample := by
  cases t₁ <;> cases t₂ <;>
    first | apply directCombinedWinTransport_diagonal
          | apply directCombinedWinTransport_aline_point
          | apply directCombinedWinTransport_dline_point
          | apply directCombinedWinTransport_aline_dline
          | apply DirectCombinedWinTransport.swap
            first | apply directCombinedWinTransport_aline_point
                  | apply directCombinedWinTransport_dline_point
                  | apply directCombinedWinTransport_aline_dline

end

end MIPStarRE.QPBT
