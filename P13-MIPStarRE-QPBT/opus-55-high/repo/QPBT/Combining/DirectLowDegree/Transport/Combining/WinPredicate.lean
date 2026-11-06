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

variable (D : DirectLdParams)

theorem directCombinedPointPart_add_smul (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D) :
    directCombinedPointPart D (p + t • V) =
      directCombinedPointPart D p + t • directCombinedPointPart D V := rfl

theorem directCombinedCoefficientPart_add_smul (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D) :
    directCombinedCoefficientPart D (p + t • V) =
      directCombinedCoefficientPart D p + t • directCombinedCoefficientPart D V := rfl

/-- The coordinate direction of a point coordinate of the combined dimension
has vanishing combining part. -/
@[simp] theorem directCombinedCoefficientPart_coordinateDirection_pointVar
    (j : Fin D.m) :
    directCombinedCoefficientPart D
        (coordinateDirection (combinedPointVar D.m D.k j)) = 0 := by
  funext r
  show (coordinateDirection (combinedPointVar D.m D.k j) :
      Fin (D.m + D.k) → DirectScalarQ D) (combinedCoefficientVar D.m D.k r) = 0
  rw [coordinateDirection,
    Pi.single_eq_of_ne (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j)]

/-! ## Degree bounds at the combined parameters -/

theorem diagonalDegreeBound :
    D.m * D.d + 1 ≤ D.combined.m * D.combined.d := by
  have h1 : 1 ≤ D.k * D.d := by simpa using Nat.mul_le_mul D.hk D.hd
  calc D.m * D.d + 1 ≤ D.m * D.d + D.k * D.d := Nat.add_le_add_left h1 _
    _ = (D.m + D.k) * D.d := (Nat.add_mul _ _ _).symm

theorem oneLeCombinedDlineDegree :
    1 ≤ D.combined.m * D.combined.d := by
  simpa using Nat.mul_le_mul D.combined.hm D.combined.hd

/-! ## Evaluation of the combined answers -/

/-- Evaluation of the answer of cases 3 and 5 of `def:ld-combined-strategy`:
along a line contained in a fiber of the projection to the point coordinates,
the combining part of the point at parameter `t` is `α₀ + t w`, so the affine
answer built from the measured point answer `b` takes at `t` the combined
value of `b` at that point. -/
theorem fiberAnswerEval (n : ℕ) (hn : 1 ≤ n)
    (z base dirn : Fin D.combined.m → DirectScalarQ D)
    (b : Fin D.k → DirectScalarQ D) (t : DirectScalarQ D)
    (ht : z = base + t • dirn) :
    evalCoefficient
        (coefficientsOfPolynomial n
          (fiberLinePolynomial (directCombinedCoefficientPart D base)
            (directCombinedCoefficientPart D dirn) b)) t =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * b r := by
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (fiberLinePolynomial_natDegree_le _ _ _) hn),
    fiberLinePolynomial_eval, ht, directCombinedCoefficientPart_add_smul]
  simp

/-! ## Structural clauses of the win predicate -/

/-- An answer pair accepted at two equal questions of the directly indexed game
consists of two equal answers: the three diagonal clauses of
`def:ld-win-predicate` are equalities of answers. -/
theorem directLdAnswer_eq_of_win_self (q : DirectLdQuestion D) {a b : DirectLdAnswer D}
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
theorem validDirectLdAnswer_directCombinedAnswerMap (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) :
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
theorem directLdWinPredicate_aline_dline (xq yq : DirectLdSpace D) (a b : DirectLdAnswer D)
    (ha : validDirectLdAnswer LdType.aline a = true)
    (hb : validDirectLdAnswer LdType.dline b = true) :
    directLdWinPredicate D (.aline, xq) (.dline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [directLdWinPredicate, validDirectLdAnswer]

/-- The win predicate of the directly indexed game is symmetric under
exchanging the two players. -/
theorem directLdWinPredicate_comm (q₁ q₂ : DirectLdQuestion D) (a b : DirectLdAnswer D) :
    directLdWinPredicate D q₁ q₂ a b = directLdWinPredicate D q₂ q₁ b a := by
  obtain ⟨t₁, x₁⟩ := q₁
  obtain ⟨t₂, x₂⟩ := q₂
  cases t₁ <;> cases t₂ <;> cases a <;> cases b <;>
    simp [directLdWinPredicate, validDirectLdAnswer, eq_comm, Bool.and_comm]

/-- A coordinate index of the combined dimension split off as a point
coordinate is that point coordinate. -/
theorem eq_combinedPointVar_of_indexSplit {i : Fin D.combined.m} {j : Fin D.m}
    (h : directCombinedIndexSplit D i = Sum.inl j) :
    i = combinedPointVar D.m D.k j := by
  have hi : finSumFinEquiv (directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inl j) := congrArg _ h
  rw [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-- A coordinate index of the combined dimension split off as a combining
coordinate is that combining coordinate. -/
theorem eq_combinedCoefficientVar_of_indexSplit {i : Fin D.combined.m} {r : Fin D.k}
    (h : directCombinedIndexSplit D i = Sum.inr r) :
    i = combinedCoefficientVar D.m D.k r := by
  have hi : finSumFinEquiv (directCombinedIndexSplit D i) =
      finSumFinEquiv (Sum.inr r) := congrArg _ h
  rw [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi
  exact hi

/-! ## The acceptance clause on a point coordinate -/

/-- Case 2 of `def:ld-combined-strategy` at the parameter presenting the
sampled point: the affine shift `s` relating the two presentations of the image
line carries the acceptance clause of the original game at the shifted
parameter to the acceptance clause of the combined game. -/
theorem directCombinedAxisAnswer_eval (z dir : Fin D.combined.m → DirectScalarQ D)
    (hcoef : directCombinedCoefficientPart D dir = 0) (s T : DirectScalarQ D)
    (hs : directCombinedPointPart D (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart D dir)
          (directCombinedPointPart D (lineRepMap dir z)) +
        s • directCombinedPointPart D dir)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D) (c : Fin D.k → DirectScalarQ D)
    (hT : z = lineRepMap dir z + T • dir)
    (hcond : ∀ t : DirectScalarQ D,
      directCombinedPointPart D z =
          lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
            t • directCombinedPointPart D dir →
        ∀ r, evalCoefficient (f r) t = c r) :
    evalCoefficient
        (coefficientsOfPolynomial D.combined.d
          (combinedAxisPolynomial
            (directCombinedCoefficientPart D (lineRepMap dir z)) s f)) T =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have h := hcond (T + s) (by
    conv_lhs => rw [hT]
    rw [directCombinedPointPart_add_smul, hs, lineRepMap_directCombinedPointPart_lineRepMap]
    module)
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedAxisPolynomial_natDegree_le _ _ _) (DirectLdParams.combined_d D).ge),
    combinedAxisPolynomial_eval]
  conv_rhs => rw [hT, directCombinedCoefficientPart_add_smul, hcoef]
  simp [h]

/-- Case 4 of `def:ld-combined-strategy` at the parameter presenting the
sampled point. -/
theorem directCombinedDiagonalAnswer_eval (z dir : Fin D.combined.m → DirectScalarQ D) (s T : DirectScalarQ D)
    (hs : directCombinedPointPart D (lineRepMap dir z) =
      lineRepMap (directCombinedPointPart D dir)
          (directCombinedPointPart D (lineRepMap dir z)) +
        s • directCombinedPointPart D dir)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hT : z = lineRepMap dir z + T • dir)
    (hcond : ∀ t : DirectScalarQ D,
      directCombinedPointPart D z =
          lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
            t • directCombinedPointPart D dir →
        ∀ r, evalCoefficient (f r) t = c r) :
    evalCoefficient
        (coefficientsOfPolynomial (D.combined.m * D.combined.d)
          (combinedDiagonalPolynomial
            (directCombinedCoefficientPart D (lineRepMap dir z))
            (directCombinedCoefficientPart D dir) s f)) T =
      ∑ r : Fin D.k, directCombinedCoefficientPart D z r * c r := by
  have h := hcond (T + s) (by
    conv_lhs => rw [hT]
    rw [directCombinedPointPart_add_smul, hs, lineRepMap_directCombinedPointPart_lineRepMap]
    module)
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedDiagonalPolynomial_natDegree_le _ _ _ _) (diagonalDegreeBound D)),
    combinedDiagonalPolynomial_eval]
  conv_rhs => rw [hT, directCombinedCoefficientPart_add_smul]
  simp [h]

/-! ## The branch-wise acceptance transport -/

/-- The acceptance transport of `lem:ld-combined-value` on one ordered type
pair: the relabelling of `def:ld-combined-strategy` sends an answer pair
accepted by the win predicate of the original game at the measured questions to
an answer pair accepted by the win predicate of the combined game. -/
def DirectCombinedWinTransport (t₁ t₂ : LdType)
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

/-- The acceptance transport is symmetric under exchanging the two players. -/
theorem DirectCombinedWinTransport.symm {t₁ t₂ : LdType} {sample : DirectLdSpace D.combined}
    (h : DirectCombinedWinTransport D t₁ t₂ sample) : DirectCombinedWinTransport D t₂ t₁ sample :=
  fun a b hwin => by
    rw [directLdWinPredicate_comm] at hwin ⊢
    exact h b a hwin

/-- The axis-parallel-line versus point branch. -/
theorem directCombinedWinTransport_aline_point (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .aline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = combinedPointVar D.m D.k j :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .aline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a <;> cases b <;> simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.aline sample).index = Sum.inl j := hsplit
    simp only [directCombinedAnswerMap, hsplitL]
    simp [directLdWinPredicate, validDirectLdAnswer]
    intro T hT _
    refine directCombinedAxisAnswer_eval D sample.point (coordinateDirection sample.index)
      (by rw [hindex]; simp) _ T ?_ _ _ hT ?_
    · rw [← show directCombinedMeasuredDirection D (.aline, directLdMap D.combined .aline sample) =
        directCombinedPointPart D (coordinateDirection sample.index) by
          simp [directCombinedMeasuredDirection, directLdMap, hindex]]
      exact directLineRepParameter_spec _ _
    · rw [hindex, directCombinedPointPart_coordinateDirection_pointVar]
      exact hwin
  · have hindex : sample.index = combinedCoefficientVar D.m D.k r₀ :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .aline r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a <;> simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.aline sample).index = Sum.inr r₀ := hsplit
    simp only [directCombinedAnswerMap, hsplitL]
    simp [directLdWinPredicate, validDirectLdAnswer]
    intro T hT _
    exact fiberAnswerEval D D.combined.d D.hd _ _ _ _ T hT

/-- The diagonal-line versus point branch. -/
theorem directCombinedWinTransport_dline_point (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .dline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex : sample.index = combinedPointVar D.m D.k j :=
      eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .dline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a <;> cases b <;> simp [directLdWinPredicate, validDirectLdAnswer] at hwin
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.dline sample).index = Sum.inl j := hsplit
    simp only [directCombinedAnswerMap, hsplitL]
    simp [directLdWinPredicate, validDirectLdAnswer]
    intro T hT _
    refine directCombinedDiagonalAnswer_eval D sample.point
      (directPrefixProjection sample.index sample.direction) _ T ?_ _ _ hT ?_
    · rw [← show directCombinedMeasuredDirection D (.dline, directLdMap D.combined .dline sample) =
        directCombinedPointPart D (directPrefixProjection sample.index sample.direction) by
          simp [directCombinedMeasuredDirection, directLdMap, hindex, directPrefixProjection_idem]]
      exact directLineRepParameter_spec _ _
    · rw [hindex, directCombinedPointPart_directPrefixProjection_pointVar]
      exact hwin
  · have hindex : sample.index = combinedCoefficientVar D.m D.k r₀ :=
      eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .dline r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
    subst hab
    cases a <;> simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.dline sample).index = Sum.inr r₀ := hsplit
    simp only [directCombinedAnswerMap, hsplitL]
    simp [directLdWinPredicate, validDirectLdAnswer]
    intro T hT _
    exact fiberAnswerEval D _ (oneLeCombinedDlineDegree D) _ _ _ _ T hT

/-- A branch whose ordered type pair is diagonal: the two questions of the
combined game are equal, so the acceptance clause of the original game at the
two equal measured questions forces the two measured outcomes to be equal, and
the relabelling sends them to equal combined outcomes. -/
theorem directCombinedWinTransport_diagonal (t : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t t sample := by
  intro a b hwin
  have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
  subst hab
  exact directLdWinPredicate_self D.combined (t, directLdMap D.combined t sample) _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (t, directLdMap D.combined t sample) a)

/-- The axis-parallel-line versus diagonal-line branch: the win predicate of
the combined game imposes no condition on that ordered type pair. -/
theorem directCombinedWinTransport_aline_dline (sample : DirectLdSpace D.combined) :
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
  cases t₁ <;> cases t₂
  · exact directCombinedWinTransport_diagonal D .point sample
  · exact (directCombinedWinTransport_aline_point D sample).symm
  · exact (directCombinedWinTransport_dline_point D sample).symm
  · exact directCombinedWinTransport_aline_point D sample
  · exact directCombinedWinTransport_diagonal D .aline sample
  · exact directCombinedWinTransport_aline_dline D sample
  · exact directCombinedWinTransport_dline_point D sample
  · exact (directCombinedWinTransport_aline_dline D sample).symm
  · exact directCombinedWinTransport_diagonal D .dline sample

end

end MIPStarRE.QPBT
