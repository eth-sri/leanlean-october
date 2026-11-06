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

theorem directCombinedPointPart_add_smul (D : DirectLdParams)
    (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D) :
    directCombinedPointPart D (p + t • V) =
      directCombinedPointPart D p + t • directCombinedPointPart D V := rfl

theorem directCombinedCoefficientPart_add_smul (D : DirectLdParams)
    (p V : Fin D.combined.m → DirectScalarQ D) (t : DirectScalarQ D) :
    directCombinedCoefficientPart D (p + t • V) =
      directCombinedCoefficientPart D p + t • directCombinedCoefficientPart D V := rfl

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
  calc D.m * D.d + 1 ≤ D.m * D.d + D.k * D.d := Nat.add_le_add_left h1 _
    _ = (D.m + D.k) * D.d := (Nat.add_mul _ _ _).symm

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

/-! ## Structural clauses of the win predicate -/

theorem directLdAnswer_eq_of_win_self (D : DirectLdParams)
    (q : DirectLdQuestion D) {a b : DirectLdAnswer D}
    (hwin : directLdWinPredicate D q q a b = true) : a = b := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;> cases b <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

theorem directLdWinPredicate_self (D : DirectLdParams) (q : DirectLdQuestion D)
    (a : DirectLdAnswer D) (hvalid : validDirectLdAnswer q.1 a = true) :
    directLdWinPredicate D q q a a = true := by
  obtain ⟨t, xq⟩ := q
  cases t <;> cases a <;>
    simp_all [directLdWinPredicate, validDirectLdAnswer]

theorem validDirectLdAnswer_directCombinedAnswerMap (D : DirectLdParams)
    (q : DirectLdQuestion D.combined) (a : DirectLdAnswer D) :
    validDirectLdAnswer q.1 (directCombinedAnswerMap D q a) = true := by
  obtain ⟨t, xq⟩ := q
  cases t
  · rfl
  · rcases hsplit : directCombinedIndexSplit D xq.index with j | r <;>
      simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]
  · rcases hsplit : directCombinedIndexSplit D xq.index with j | r <;>
      simp only [directCombinedAnswerMap, hsplit, validDirectLdAnswer]

theorem directLdWinPredicate_aline_dline (D : DirectLdParams)
    (xq yq : DirectLdSpace D) (a b : DirectLdAnswer D)
    (ha : validDirectLdAnswer LdType.aline a = true)
    (hb : validDirectLdAnswer LdType.dline b = true) :
    directLdWinPredicate D (.aline, xq) (.dline, yq) a b = true := by
  cases a <;> cases b <;> simp_all [directLdWinPredicate, validDirectLdAnswer]

theorem eq_combinedPointVar_of_indexSplit (D : DirectLdParams)
    {i : Fin D.combined.m} {j : Fin D.m}
    (h : directCombinedIndexSplit D i = Sum.inl j) :
    i = combinedPointVar D.m D.k j := by
  have hi := congrArg finSumFinEquiv h
  rwa [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi

theorem eq_combinedCoefficientVar_of_indexSplit (D : DirectLdParams)
    {i : Fin D.combined.m} {r : Fin D.k}
    (h : directCombinedIndexSplit D i = Sum.inr r) :
    i = combinedCoefficientVar D.m D.k r := by
  have hi := congrArg finSumFinEquiv h
  rwa [directCombinedIndexSplit, Equiv.apply_symm_apply] at hi

/-! ## The acceptance clause on a point coordinate -/

theorem directCombinedAxisAnswer_eval (D : DirectLdParams)
    (z dir : Fin D.combined.m → DirectScalarQ D)
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
  have hpt : directCombinedPointPart D z =
      lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
        (T + s) • directCombinedPointPart D dir := by
    conv_lhs => rw [hT]
    rw [directCombinedPointPart_add_smul, hs, lineRepMap_directCombinedPointPart_lineRepMap D dir z]
    module
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D (lineRepMap dir z) := by
    conv_lhs => rw [hT]
    rw [directCombinedCoefficientPart_add_smul, hcoef, smul_zero, add_zero]
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedAxisPolynomial_natDegree_le _ _ _)
        (le_of_eq (DirectLdParams.combined_d D).symm)),
    combinedAxisPolynomial_eval, hz]
  exact Finset.sum_congr rfl fun r _ => by rw [hcond (T + s) hpt]

theorem directCombinedDiagonalAnswer_eval (D : DirectLdParams)
    (z dir : Fin D.combined.m → DirectScalarQ D) (s T : DirectScalarQ D)
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
  have hpt : directCombinedPointPart D z =
      lineRepMap (directCombinedPointPart D dir) (directCombinedPointPart D z) +
        (T + s) • directCombinedPointPart D dir := by
    conv_lhs => rw [hT]
    rw [directCombinedPointPart_add_smul, hs, lineRepMap_directCombinedPointPart_lineRepMap D dir z]
    module
  have hz : directCombinedCoefficientPart D z =
      directCombinedCoefficientPart D (lineRepMap dir z) +
        T • directCombinedCoefficientPart D dir := by
    conv_lhs => rw [hT]
    exact directCombinedCoefficientPart_add_smul D (lineRepMap dir z) dir T
  rw [evalCoefficient_coefficientsOfPolynomial
      (le_trans (combinedDiagonalPolynomial_natDegree_le _ _ _ _) (diagonalDegreeBound D)),
    combinedDiagonalPolynomial_eval, hz]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hcond (T + s) hpt]; simp

/-! ## The branch-wise acceptance transport -/

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

theorem directCombinedWinTransport_aline_point (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .aline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex := eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .aline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a <;> cases b <;>
      try { simp [directLdWinPredicate, validDirectLdAnswer] at hwin }
    rename_i f c
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.aline sample).index = Sum.inl j := hsplit
    simp only [directCombinedAnswerMap, hsplitL, directLdWinPredicate,
      validDirectLdAnswer, Bool.true_and, ite_true, decide_eq_true_eq] at hwin ⊢
    intro T hT _
    refine directCombinedAxisAnswer_eval D sample.point (coordinateDirection sample.index)
      (by rw [hindex]; exact directCombinedCoefficientPart_coordinateDirection_pointVar D j)
      _ T ?_ f c hT ?_
    · have hmdir : directCombinedMeasuredDirection D
          (LdType.aline, directLdMap D.combined LdType.aline sample) =
          directCombinedPointPart D (coordinateDirection sample.index) := by
        simp only [directCombinedMeasuredDirection, directLdMap, hindex,
          directCombinedIndexSplit_combinedPointVar,
          directCombinedPointPart_coordinateDirection_pointVar]
      rw [← hmdir]; exact directLineRepParameter_spec _ _
    · rw [hindex, directCombinedPointPart_coordinateDirection_pointVar]
      exact hwin
  · have hindex := eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .aline r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    obtain rfl := directLdAnswer_eq_of_win_self D _ hwin
    cases a <;>
      try { simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin }
    rename_i bv
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.aline sample).index = Sum.inr r₀ := hsplit
    simp only [directCombinedAnswerMap, hsplitL, directLdWinPredicate,
      validDirectLdAnswer, Bool.true_and, ite_true, decide_eq_true_eq]
    intro T hT _
    exact fiberAnswerEval D D.combined.d D.hd _ _ _ bv T hT

private theorem directLdWinPredicate_symm (D : DirectLdParams)
    (qA qB : DirectLdQuestion D) (a b : DirectLdAnswer D) :
    directLdWinPredicate D qA qB a b = directLdWinPredicate D qB qA b a := by
  rcases qA with ⟨tA, xA⟩; rcases qB with ⟨tB, xB⟩
  cases tA <;> cases tB <;> cases a <;> cases b <;>
    simp [directLdWinPredicate, validDirectLdAnswer, eq_comm]

private theorem directCombinedWinTransport_symm {D : DirectLdParams} {t₁ t₂ : LdType}
    {sample : DirectLdSpace D.combined} (h : DirectCombinedWinTransport D t₁ t₂ sample) :
    DirectCombinedWinTransport D t₂ t₁ sample := fun a b hwin => by
  rw [directLdWinPredicate_symm]; apply h; rwa [directLdWinPredicate_symm]

theorem directCombinedWinTransport_dline_point (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .dline .point sample := by
  intro a b hwin
  rcases hsplit : directCombinedIndexSplit D sample.index with j | r₀
  · have hindex := eq_combinedPointVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_pointVar D .dline j sample hindex,
      directCombined_measuredQuestion_of_pointVar D .point j sample hindex] at hwin
    cases a <;> cases b <;>
      try { simp [directLdWinPredicate, validDirectLdAnswer] at hwin }
    rename_i f c
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.dline sample).index = Sum.inl j := hsplit
    simp only [directCombinedAnswerMap, hsplitL, directLdWinPredicate,
      validDirectLdAnswer, Bool.true_and, ite_true, decide_eq_true_eq] at hwin ⊢
    intro T hT _
    refine directCombinedDiagonalAnswer_eval D sample.point
      (directPrefixProjection sample.index sample.direction) _ T ?_ f c hT ?_
    · have hmdir : directCombinedMeasuredDirection D
          (LdType.dline, directLdMap D.combined LdType.dline sample) =
          directCombinedPointPart D (directPrefixProjection sample.index sample.direction) := by
        simp only [directCombinedMeasuredDirection, directLdMap, hindex,
          directCombinedIndexSplit_combinedPointVar,
          directCombinedPointPart_directPrefixProjection_pointVar,
          directPrefixProjection_idem]
      rw [← hmdir]; exact directLineRepParameter_spec _ _
    · rw [hindex, directCombinedPointPart_directPrefixProjection_pointVar]
      exact hwin
  · have hindex := eq_combinedCoefficientVar_of_indexSplit D hsplit
    rw [directCombined_measuredQuestion_of_coefficientVar D .dline r₀ sample hindex,
      directCombined_measuredQuestion_of_coefficientVar D .point r₀ sample hindex] at hwin
    obtain rfl := directLdAnswer_eq_of_win_self D _ hwin
    cases a <;>
      try { simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin }
    rename_i bv
    have hsplitL : directCombinedIndexSplit D
        (directLdMap D.combined LdType.dline sample).index = Sum.inr r₀ := hsplit
    simp only [directCombinedAnswerMap, hsplitL, directLdWinPredicate,
      validDirectLdAnswer, Bool.true_and, ite_true, decide_eq_true_eq]
    intro T hT _
    exact fiberAnswerEval D (D.combined.m * D.combined.d) (oneLeCombinedDlineDegree D)
      _ _ _ bv T hT

/-- A branch whose ordered type pair is diagonal. -/
theorem directCombinedWinTransport_diagonal (D : DirectLdParams) (t : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t t sample := by
  intro a b hwin
  have hab : a = b := directLdAnswer_eq_of_win_self D _ hwin
  subst hab
  exact directLdWinPredicate_self D.combined (t, directLdMap D.combined t sample) _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (t, directLdMap D.combined t sample) a)

/-- The axis-parallel-line versus diagonal-line branch. -/
theorem directCombinedWinTransport_aline_dline (D : DirectLdParams)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D .aline .dline sample := by
  intro a b _
  exact directLdWinPredicate_aline_dline D.combined _ _ _ _
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.aline, directLdMap D.combined LdType.aline sample) a)
    (validDirectLdAnswer_directCombinedAnswerMap D
      (LdType.dline, directLdMap D.combined LdType.dline sample) b)

/-- The acceptance transport of `lem:ld-combined-value` on every one of the
nine ordered type pairs of the combined game. -/
theorem directCombinedWinTransport_all (D : DirectLdParams) (t₁ t₂ : LdType)
    (sample : DirectLdSpace D.combined) :
    DirectCombinedWinTransport D t₁ t₂ sample := by
  cases t₁ <;> cases t₂
  · exact directCombinedWinTransport_diagonal D .point sample
  · exact directCombinedWinTransport_symm (directCombinedWinTransport_aline_point D sample)
  · exact directCombinedWinTransport_symm (directCombinedWinTransport_dline_point D sample)
  · exact directCombinedWinTransport_aline_point D sample
  · exact directCombinedWinTransport_diagonal D .aline sample
  · exact directCombinedWinTransport_aline_dline D sample
  · exact directCombinedWinTransport_dline_point D sample
  · exact directCombinedWinTransport_symm (directCombinedWinTransport_aline_dline D sample)
  · exact directCombinedWinTransport_diagonal D .dline sample

end

end MIPStarRE.QPBT
