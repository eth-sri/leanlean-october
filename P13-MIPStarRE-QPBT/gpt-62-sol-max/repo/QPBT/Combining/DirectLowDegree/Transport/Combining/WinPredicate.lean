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

variable (D : DirectLdParams)
    (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D)
include D p V t

theorem directCombinedPointPart_add_smul :
    directCombinedPointPart D (p + t • V) =
      directCombinedPointPart D p + t • directCombinedPointPart D V := rfl

theorem directCombinedCoefficientPart_add_smul :
    directCombinedCoefficientPart D (p + t • V) =
      directCombinedCoefficientPart D p + t • directCombinedCoefficientPart D V := rfl

end

/-- The coordinate direction of a point coordinate of the combined dimension
has vanishing combining part. -/
@[simp] theorem directCombinedCoefficientPart_coordinateDirection_pointVar
    (D : DirectLdParams) (j : Fin D.m) :
    directCombinedCoefficientPart D
        (coordinateDirection (combinedPointVar D.m D.k j)) = 0 := by
  funext r
  show (coordinateDirection (combinedPointVar D.m D.k j) :
      Fin (D.m + D.k) → DirectScalarQ D) (combinedCoefficientVar D.m D.k r) = 0
  rw [coordinateDirection,
    Pi.single_eq_of_ne (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j)]

/-! ## Degree bounds at the combined parameters -/

private theorem diagonalDegreeBound (D : DirectLdParams) :
    D.m * D.d + 1 ≤ D.combined.m * D.combined.d := by
  have h1 : 1 ≤ D.k * D.d := by simpa using Nat.mul_le_mul D.hk D.hd
  grind only

private theorem oneLeCombinedDlineDegree (D : DirectLdParams) :
    1 ≤ D.combined.m * D.combined.d := by
  simpa using Nat.mul_le_mul D.combined.hm D.combined.hd

/-! ## Evaluation of the combined answers -/

/-- Evaluation of the answer of cases 3 and 5 of `def:ld-combined-strategy`:
along a line contained in a fiber of the projection to the point coordinates,
the combining part of the point at parameter `t` is `α₀ + t w`, so the affine
answer built from the measured point answer `b` takes at `t` the combined
value of `b` at that point. -/
private theorem fiberAnswerEval (D : DirectLdParams) (n : ℕ) (hn : 1 ≤ n)
    (z base dirn : Fin D.combined.m → DirectScalarQ D)
    (b : Fin D.k → DirectScalarQ D) (t : DirectScalarQ D)
    (ht : z = base + t • dirn) :
    evalCoefficient
        (coefficientsOfPolynomial n
          (fiberLinePolynomial (directCombinedCoefficientPart D base)
            (directCombinedCoefficientPart D dirn) b)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * b r := by
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D base +
        t • directCombinedCoefficientPart D dirn := by
    conv_lhs => rw [ht]
    exact directCombinedCoefficientPart_add_smul D base dirn t
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (fiberLinePolynomial_natDegree_le _ _ _) hn),
    fiberLinePolynomial_eval, hz]
  exact Finset.sum_congr rfl fun r _ => by simp

/-- The combined answer is evaluation on the projected point, weighted by the
coefficient part of the sampled point. The axis case has zero coefficient direction. -/
private theorem combinedAnswerEval (D : DirectLdParams) {n bound : ℕ}
    (z base dirn : Fin D.combined.m → DirectScalarQ D) (s t : DirectScalarQ D)
    (f : Fin D.k → Fin (n + 1) → DirectScalarQ D) (c : Fin D.k → DirectScalarQ D)
    (hdeg : (combinedDiagonalPolynomial (directCombinedCoefficientPart D base)
      (directCombinedCoefficientPart D dirn) s f).natDegree ≤ bound)
    (ht : z = base + t • dirn) (hf : ∀ r, evalCoefficient (f r) (t + s) = c r) :
    evalCoefficient (coefficientsOfPolynomial bound
      (combinedDiagonalPolynomial (directCombinedCoefficientPart D base)
        (directCombinedCoefficientPart D dirn) s f)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have hz := congrArg (directCombinedCoefficientPart D) ht
  rw [directCombinedCoefficientPart_add_smul] at hz
  rw [evalCoefficient_coefficientsOfPolynomial hdeg, combinedDiagonalPolynomial_eval, hz]
  simp [hf]

/-! ## Structural clauses of the win predicate -/

section

variable (D : DirectLdParams)
include D

/-- An answer pair accepted at two equal questions of the directly indexed game
consists of two equal answers: the three diagonal clauses of
`def:ld-win-predicate` are equalities of answers. -/
theorem directLdAnswer_eq_of_win_self
    (q : DirectLdQuestion D) {a b : DirectLdAnswer D}
    (hwin : directLdWinPredicate D q q a b = true) : a = b := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;> cases b <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- Two equal answers of the correct constructor are accepted at two equal
questions of the directly indexed game. -/
theorem directLdWinPredicate_self (q : DirectLdQuestion D)
    (a : DirectLdAnswer D) (hvalid : validDirectLdAnswer q.1 a = true) :
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
  · rcases hsplit : directCombinedIndexSplit D xq.index with j | r <;>
      simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]
  · rcases hsplit : directCombinedIndexSplit D xq.index with j | r <;>
      simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]

/-- An ordered pair of a well-formed axis-parallel line answer and a well-formed
diagonal line answer is accepted: `def:ld-win-predicate` imposes no condition on
that ordered type pair. -/
theorem directLdWinPredicate_aline_dline
    (xq yq : DirectLdSpace D) (a b : DirectLdAnswer D)
    (ha : validDirectLdAnswer LdType.aline a = true)
    (hb : validDirectLdAnswer LdType.dline b = true) :
    directLdWinPredicate D (.aline, xq) (.dline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- A coordinate index of the combined dimension split off as a point
coordinate is that point coordinate. -/
theorem eq_combinedPointVar_of_indexSplit
    {i : Fin D.combined.m} {j : Fin D.m}
    (h : directCombinedIndexSplit D i = Sum.inl j) :
    i = combinedPointVar D.m D.k j := by
  have hi : finSumFinEquiv (directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inl j) := congrArg _ h
  rw [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-- A coordinate index of the combined dimension split off as a combining
coordinate is that combining coordinate. -/
theorem eq_combinedCoefficientVar_of_indexSplit
    {i : Fin D.combined.m} {r : Fin D.k}
    (h : directCombinedIndexSplit D i = Sum.inr r) :
    i = combinedCoefficientVar D.m D.k r := by
  have hi : finSumFinEquiv (directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inr r) := congrArg _ h
  rw [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

end

/-! ## The acceptance clause on a point coordinate -/

/-- A parameter for the sampled point shifts by `s` when projected to the
canonical presentation of the measured line. -/
private theorem rebasePointParameter (D : DirectLdParams)
    (z dir : Fin D.combined.m → DirectScalarQ D) (s t : DirectScalarQ D)
    (hs : directCombinedPointPart D (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart D dir)
          (directCombinedPointPart D (lineRepMap dir z)) + s • directCombinedPointPart D dir)
    (ht : z = lineRepMap dir z + t • dir) :
    directCombinedPointPart D z =
      lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
        (t + s) • directCombinedPointPart D dir := by
  conv_lhs => rw [ht]
  rw [directCombinedPointPart_add_smul, hs, lineRepMap_directCombinedPointPart_lineRepMap]
  module

/-! ## The branch-wise acceptance transport -/

/-- The acceptance transport of `lem:ld-combined-value` on one ordered type
pair: the relabelling of `def:ld-combined-strategy` sends an answer pair
accepted by the win predicate of the original game at the measured questions to
an answer pair accepted by the win predicate of the combined game. -/
def DirectCombinedWinTransport (D : DirectLdParams) (t₁ t₂ : LdType)
    (sample : DirectLdSpace D.combined) : Prop :=
  ∀ a b : DirectLdAnswer D,
    directLdWinPredicate D
        (directCombinedMeasuredQuestion D (t₁, directLdMap D.combined t₁ sample))
        (directCombinedMeasuredQuestion D (t₂, directLdMap D.combined t₂ sample))
        a b = true →
      directLdWinPredicate D.combined
        (t₁, directLdMap D.combined t₁ sample) (t₂, directLdMap D.combined t₂ sample)
        (directCombinedAnswerMap D (t₁, directLdMap D.combined t₁ sample) a)
        (directCombinedAnswerMap D (t₂, directLdMap D.combined t₂ sample) b) = true

private theorem DirectCombinedWinTransport.swap {D : DirectLdParams} {t u : LdType}
    {sample : DirectLdSpace D.combined} (h : DirectCombinedWinTransport D t u sample) :
    DirectCombinedWinTransport D u t sample := by
  intro a b hab
  rw [directLdWinPredicate_symm] at hab ⊢
  exact h b a hab

section

variable (D : DirectLdParams)
include D

private theorem directCombinedRebaseParameter_spec
    (q : DirectLdQuestion D.combined) :
    directCombinedPointPart D q.2.point =
      lineRepMap (directCombinedMeasuredDirection D q) (directCombinedPointPart D q.2.point) +
        directCombinedRebaseParameter D q • directCombinedMeasuredDirection D q :=
  directLineRepParameter_spec _ _

/-- Every branch with a combining coordinate measures the same original point.
For a line answer the affine interpolation gives the relabeled value of that point. -/
private theorem directCombinedWinTransport_fiber (l : LdType)
    (sample : DirectLdSpace D.combined) {r : Fin D.k}
    (hsplit : directCombinedIndexSplit D sample.index = .inr r) :
    DirectCombinedWinTransport D l .point sample := by
  classical
  intro a b hwin
  have hi := eq_combinedCoefficientVar_of_indexSplit D hsplit
  rw [directCombined_measuredQuestion_of_coefficientVar D l _ _ hi,
    directCombined_measuredQuestion_of_coefficientVar D .point _ _ hi] at hwin
  have hab := directLdAnswer_eq_of_win_self D _ hwin
  subst b
  cases a <;> simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
  cases l
  · apply directLdWinPredicate_self
    simp [directCombinedAnswerMap, validDirectLdAnswer]
  · have hr : directCombinedIndexSplit D (directLdMap D.combined .aline sample).index = .inr r :=
      hsplit
    simp only [directCombinedAnswerMap, hr, directLdWinPredicate, validDirectLdAnswer,
      Bool.true_and, ite_true]
    exact decide_eq_true fun t ht _ => fiberAnswerEval D D.combined.d D.hd _ _ _ _ t ht
  · have hr : directCombinedIndexSplit D (directLdMap D.combined .dline sample).index = .inr r :=
      hsplit
    simp only [directCombinedAnswerMap, hr, directLdWinPredicate, validDirectLdAnswer,
      Bool.true_and, ite_true]
    exact decide_eq_true fun t ht _ => fiberAnswerEval D _ (oneLeCombinedDlineDegree D) _ _ _ _ t ht

section

variable (l : LdType)
    (hl : l ≠ .point) (sample : DirectLdSpace D.combined)
include l hl sample

/-- At a point coordinate both line clauses use the same affine parameter shift. -/
private theorem directCombinedWinTransport_pointVar {j : Fin D.m}
    (hj : directCombinedIndexSplit D sample.index = .inl j) :
    DirectCombinedWinTransport D l .point sample := by
  classical
  intro a b hwin
  have hi := eq_combinedPointVar_of_indexSplit D hj
  rw [directCombined_measuredQuestion_of_pointVar D l _ _ hi,
    directCombined_measuredQuestion_of_pointVar D .point _ _ hi] at hwin
  let q : DirectLdQuestion D.combined := (l, directLdMap D.combined l sample)
  let dir := directCombinedQuestionDirection D q
  have hdir : directCombinedPointPart D dir = directCombinedMeasuredDirection D q := by
    cases l <;> simp_all [dir, q, directCombinedQuestionDirection, directLdMap,
      directCombinedMeasuredDirection, directCombinedPointPart_coordinateDirection_pointVar,
      directCombinedPointPart_directPrefixProjection_pointVar, directPrefixProjection_idem]
  have hbase : q.2.point = lineRepMap dir sample.point := by cases l <;> first | contradiction | rfl
  have hs := directCombinedRebaseParameter_spec D q
  rw [hbase, ← hdir] at hs
  have hshift := fun t ht => rebasePointParameter D sample.point dir _ t hs ht
  cases l
  · exact (hl rfl).elim
  all_goals
    cases a <;> cases b <;> simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    rename_i f c
    have hj' : directCombinedIndexSplit D q.2.index = .inl j := hj
    change directLdWinPredicate D.combined q _ (directCombinedAnswerMap D q _) _ = true
    simp only [directCombinedAnswerMap, hj', directLdWinPredicate, validDirectLdAnswer,
      Bool.true_and, ite_true, q]
    apply decide_eq_true
    intro t ht _
    have h := hshift t ht
    rw [hdir] at h
    have hf := hwin (t + directCombinedRebaseParameter D q) (by
      simpa [q, directCombinedMeasuredDirection, directLdMap, hi, directCombinedSampleProjection,
        directCombinedPointPart_directPrefixProjection_pointVar, directPrefixProjection_idem]
        using h)
  · have hz : directCombinedCoefficientPart D dir = 0 := by
      simp [dir, q, directCombinedQuestionDirection, directLdMap, hi]
    have he := combinedAnswerEval D sample.point _ dir _ t f c
      (bound := D.combined.d) (by rw [hz]; exact
        (combinedAxisPolynomial_natDegree_le _ _ _).trans D.combined_d.ge) ht hf
    simpa only [hz, combinedAxisPolynomial, hbase] using! he
  · exact combinedAnswerEval D sample.point _ dir _ t f c
      ((combinedDiagonalPolynomial_natDegree_le _ _ _ _).trans (diagonalDegreeBound D)) ht hf

private theorem directCombinedWinTransport_line_point :
    DirectCombinedWinTransport D l .point sample := by
  rcases h : directCombinedIndexSplit D sample.index with j | r
  · exact directCombinedWinTransport_pointVar D l hl sample h
  · exact directCombinedWinTransport_fiber D l sample h

end

/-- A branch whose ordered type pair is diagonal: the two questions of the
combined game are equal, so the acceptance clause of the original game at the
two equal measured questions forces the two measured outcomes to be equal, and
the relabelling sends them to equal combined outcomes. -/
theorem directCombinedWinTransport_diagonal (t : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t t sample := by
  intro a b hwin
  have hab := directLdAnswer_eq_of_win_self D _ hwin
  subst hab
  exact directLdWinPredicate_self D.combined (t, directLdMap D.combined t sample) _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (t, directLdMap D.combined t sample) a)

/-- The axis-parallel-line versus diagonal-line branch: the win predicate of
the combined game imposes no condition on that ordered type pair. -/
theorem directCombinedWinTransport_aline_dline
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .aline .dline sample := by
  intro a b _
  exact directLdWinPredicate_aline_dline D.combined _ _ _ _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.aline, directLdMap D.combined LdType.aline sample) a)
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.dline, directLdMap D.combined LdType.dline sample) b)

/-- The acceptance transport of `lem:ld-combined-value` on every one of the
nine ordered type pairs of the combined game.  This is the hypothesis of
`directRejectedMass_directCombinedStrategy_le` at the question pair attached to
a sample of the combined game. -/
theorem directCombinedWinTransport_all (t₁ t₂ : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t₁ t₂ sample := by
  cases t₁ <;> cases t₂ <;> first
    | exact directCombinedWinTransport_diagonal D _ sample
    | exact directCombinedWinTransport_line_point D .aline (by decide) sample
    | exact directCombinedWinTransport_line_point D .dline (by decide) sample
    | exact directCombinedWinTransport_aline_dline D sample
    | exact (directCombinedWinTransport_line_point D .aline (by decide) sample).swap
    | exact (directCombinedWinTransport_line_point D .dline (by decide) sample).swap
    | exact (directCombinedWinTransport_aline_dline D sample).swap

end

end

end MIPStarRE.QPBT
