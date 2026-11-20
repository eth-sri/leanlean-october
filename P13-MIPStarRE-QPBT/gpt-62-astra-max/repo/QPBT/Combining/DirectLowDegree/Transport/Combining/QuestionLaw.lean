module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Strategy

/-!
# The questions measured by the combined strategy

`lem:ld-combined-question-law` identifies the pair of questions measured by the
combined strategy of `def:ld-combined-strategy` on a sample of the combined
game.  The coordinate index of the common sample is uniform on the `m + k`
coordinates of the combined dimension, and the identification splits according
to whether that index is a point coordinate or a combining coordinate.

On a point coordinate `j`, all three question types measure the canonical
question of the same type of the original game attached to the *projected*
sample `directCombinedSampleProjection`: the point part of the sampled point,
the index `j`, and the point part of the sampled direction.  This uses the
coordinate order of `def:ld-combining-map`: the point coordinates precede the
combining coordinates, so the coordinate direction of a point coordinate has
point part the corresponding coordinate direction, and the prefix projection at
a point coordinate restricts to the prefix projection at that coordinate of the
point part.

On a combining coordinate, every direction produced by the question
distribution has vanishing point part, so all three question types measure the
point question at the point part of the sampled point.

The projected sample is read from the *canonical* base of the combined line,
which need not project to the canonical base of the image line; the two agree
after rebasing along the image direction, which is
`lineRepMap_directCombinedPointPart_lineRepMap`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:473-508`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries

noncomputable section

variable (D : DirectLdParams) (m : ℕ) (V : Fin D.combined.m → DirectScalarQ D) (k : ℕ)
  (t : LdType) (j : Fin D.m) (r : Fin D.k) (z : Fin D.combined.m → DirectScalarQ D)
  (sample : DirectLdSpace D.combined) (w : Fin D.combined.m → DirectScalarQ D)

local instance directCombinedIndexNonempty :
    Nonempty (Fin D.combined.m) :=
  ⟨D.combined.firstIndex⟩

/-! ## Coordinates of the combined dimension -/

@[simp] theorem combinedPointVar_val (j : Fin m) :
    (combinedPointVar m k j).val = j.val := by
  apply combinedPointPart.eq_1

@[simp] theorem combinedCoefficientVar_val (r : Fin k) :
    (combinedCoefficientVar m k r).val = m + r.val := by
  apply combinedCoefficientPart.eq_1

/-- The coordinate direction of a point coordinate of the combined dimension
has point part the corresponding coordinate direction. -/
@[simp] theorem directCombinedPointPart_coordinateDirection_pointVar :
    directCombinedPointPart (coordinateDirection (combinedPointVar D.m D.k j)) =
      coordinateDirection j := by
  funext j'
  show (coordinateDirection (combinedPointVar D.m D.k j)) (combinedPointVar D.m D.k j') =
    coordinateDirection j j'
  by_cases h : j' = j
  · subst h
    simp [coordinateDirection, Pi.single_eq_same]
  · rw [coordinateDirection, coordinateDirection,
      Pi.single_eq_of_ne fun hc => h (combinedPointVar_injective D.m D.k hc),
      Pi.single_eq_of_ne h]

/-- The coordinate direction of a combining coordinate of the combined
dimension has vanishing point part. -/
@[simp] theorem directCombinedPointPart_coordinateDirection_coefficientVar :
    directCombinedPointPart
        (coordinateDirection (combinedCoefficientVar D.m D.k r)) = 0 := by
  funext j
  show (coordinateDirection (combinedCoefficientVar D.m D.k r)) (combinedPointVar D.m D.k j) = 0
  rw [coordinateDirection,
    Pi.single_eq_of_ne (combinedCoefficientVar_ne_combinedPointVar D.m D.k r j).symm]

/-- Prefix projection at a point coordinate restricts to prefix projection at
that coordinate of the point part.  This is the coordinate order of
`def:ld-combining-map`: the point coordinates precede the combining ones. -/
@[simp] theorem directCombinedPointPart_directPrefixProjection_pointVar :
    directCombinedPointPart
        (directPrefixProjection (combinedPointVar D.m D.k j) w) =
      directPrefixProjection j (directCombinedPointPart w) := by
  funext j'
  rfl

/-- Prefix projection at a combining coordinate annihilates the point part:
every point coordinate precedes every combining coordinate. -/
@[simp] theorem directCombinedPointPart_directPrefixProjection_coefficientVar :
    directCombinedPointPart
        (directPrefixProjection (combinedCoefficientVar D.m D.k r) w) = 0 := by
  funext j'
  show (if (combinedPointVar D.m D.k j').val <
      (combinedCoefficientVar D.m D.k r).val
      then 0 else _) = 0
  simp
  omega

/-! ## Canonical bases -/

private theorem directCombinedPointPart_sub_smul
    (z V : Fin D.combined.m → DirectScalarQ D) (c : DirectScalarQ D) :
    directCombinedPointPart (z - c • V) =
      directCombinedPointPart z - c • directCombinedPointPart V :=
  rfl

/-- A line of the combined space whose direction has vanishing point part lies
in a fiber of the projection to the point coordinates, so its canonical base
projects to the point part of every one of its points. -/
theorem directCombinedPointPart_lineRepMap_of_pointPart_eq_zero
    (hV : directCombinedPointPart V = 0) :
    directCombinedPointPart (lineRepMap V z) = directCombinedPointPart z := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span V z)
  have hz : lineRepMap V z = z - c • V := by rw [hc]; abel
  rw [hz, directCombinedPointPart_sub_smul, hV, smul_zero, sub_zero]

/-- The canonical base of a line of the combined space projects to a point of
the image line, so rebasing its projection along the image direction returns
the canonical base of the image line.  The canonical base of a line of the
combined space need not itself project to the canonical base of its image; this
is why the answer relabellings of `def:ld-combined-strategy` carry the affine
shift `directCombinedRebaseParameter`. -/
theorem lineRepMap_directCombinedPointPart_lineRepMap :
    lineRepMap (directCombinedPointPart V)
        (directCombinedPointPart (lineRepMap V z)) =
      lineRepMap (directCombinedPointPart V) (directCombinedPointPart z) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span V z)
  have hz : lineRepMap V z = z - c • V := by rw [hc]; abel
  simp [hz, sub_eq_add_neg, ← neg_smul]
  apply lineRepMap_add_smul

/-! ## The measured questions -/

/-- The sample of the original game to which a sample of the combined game
projects at a point coordinate index: the point part of the sampled point, the
index, and the point part of the sampled direction. -/
def directCombinedSampleProjection : DirectLdSpace D :=
  ⟨directCombinedPointPart sample.point, j,
    directCombinedPointPart sample.direction⟩

/-- First half of `lem:ld-combined-question-law`: on a sample whose coordinate
index is the point coordinate `j`, the combined strategy measures, for every
question type, the canonical question of that type of the original game
attached to the projected sample. -/
theorem directCombined_measuredQuestion_of_pointVar
    (hindex : sample.index = combinedPointVar D.m D.k j) :
    directCombinedMeasuredQuestion (t, directLdMap t sample) =
      (t, directLdMap t (directCombinedSampleProjection D j sample)) := by
  cases t with
  | point => rfl
  | aline =>
      have hbase := lineRepMap_directCombinedPointPart_lineRepMap D
        (coordinateDirection (combinedPointVar D.m D.k j)) sample.point
      simp at hbase
      simp [directLdMap, directCombinedMeasuredQuestion, hindex, directCombinedIndexSplit_combinedPointVar, directCombinedSampleProjection]
      congr
  | dline =>
      have hbase := lineRepMap_directCombinedPointPart_lineRepMap D
        (directPrefixProjection (combinedPointVar D.m D.k j) sample.direction)
        sample.point
      simp only [directLdMap, directCombinedMeasuredQuestion, hindex,
        directCombinedIndexSplit_combinedPointVar,
        directCombinedSampleProjection,
        directCombinedPointPart_directPrefixProjection_pointVar,
        directPrefixProjection_idem]
      exact congrArg (fun x : DirectPoint D =>
        ((LdType.dline, ⟨x, j,
          directPrefixProjection j
            (directCombinedPointPart sample.direction)⟩) :
          DirectLdQuestion D)) hbase

/-- Second half of `lem:ld-combined-question-law`: on a sample whose coordinate
index is a combining coordinate, every direction produced by the question
distribution has vanishing point part, so the combined strategy measures, for
every question type, the point question at the point part of the sampled
point. -/
theorem directCombined_measuredQuestion_of_coefficientVar
    (hindex : sample.index = combinedCoefficientVar D.m D.k r) :
    directCombinedMeasuredQuestion (t, directLdMap t sample) =
      directLdPointQuestionOf D (directCombinedPointPart sample.point) := by
  cases t with
  | point => rfl
  | aline =>
      simp [directLdMap, directCombinedMeasuredQuestion, hindex, directCombinedIndexSplit_combinedCoefficientVar]
      exact congrArg (fun x : DirectPoint D =>
        directLdPointQuestionOf D x) (directCombinedPointPart_lineRepMap_of_pointPart_eq_zero D
          (coordinateDirection (combinedCoefficientVar D.m D.k r)) sample.point
          (directCombinedPointPart_coordinateDirection_coefficientVar D r))
  | dline =>
      simp [directLdMap, directCombinedMeasuredQuestion, hindex, directCombinedIndexSplit_combinedCoefficientVar]
      exact congrArg (fun x : DirectPoint D =>
        directLdPointQuestionOf D x) (directCombinedPointPart_lineRepMap_of_pointPart_eq_zero D
          (directPrefixProjection (combinedCoefficientVar D.m D.k r) sample.direction)
          sample.point
          (directCombinedPointPart_directPrefixProjection_coefficientVar D r
          sample.direction))

/-! ## The law of the projected sample -/

/-- A point of the combined space is recovered from its two parts. -/
@[simp] theorem combinedPoint_combinedPointPart_combinedCoefficientPart
    {K : Type*} {m k : ℕ} (z : Fin (m + k) → K) :
    combinedPoint (combinedPointPart z) (combinedCoefficientPart z) = z := by
  funext i
  rw [combinedPoint]
  rcases hi : finSumFinEquiv.symm i with j | r
  · show combinedPointPart z j = z i
    simp [combinedPointPart, combinedPointVar, ← hi]
  · show combinedCoefficientPart z r = z i
    simp [combinedCoefficientPart, combinedCoefficientVar, ← hi]

/-- The decomposition of a sample of the combined game into its coordinate
index and its two point parts on the one side, and its two combining parts on
the other. -/
private def directCombinedSpaceIndexEquiv :
    DirectLdSpace D.combined ≃
      ((Fin D.combined.m ×
          ((DirectPoint D) × (DirectPoint D))) ×
        ((Fin D.k → DirectScalarQ D) × (Fin D.k → DirectScalarQ D))) where
  toFun sample :=
    ((sample.index,
        (directCombinedPointPart sample.point,
          directCombinedPointPart sample.direction)),
      (directCombinedCoefficientPart D sample.point,
        directCombinedCoefficientPart D sample.direction))
  invFun x := ⟨combinedPoint x.1.2.1 x.2.1, x.1.1, combinedPoint x.1.2.2 x.2.2⟩
  left_inv sample := by
    obtain ⟨point, index, direction⟩ := sample
    dsimp only
    congr 1 <;>
      first
        | rfl
        | exact combinedPoint_combinedPointPart_combinedCoefficientPart _
  right_inv x := by
    obtain ⟨⟨i, u, v⟩, α, w⟩ := x
    dsimp only
    simp only [Prod.mk.injEq]
    exact ⟨⟨trivial, combinedPointPart_combinedPoint u α,
        combinedPointPart_combinedPoint v w⟩,
      combinedCoefficientPart_combinedPoint u α,
      combinedCoefficientPart_combinedPoint v w⟩

/-- The distributional half of `lem:ld-combined-question-law`: the coordinate
index of a uniform sample of the combined game and the two point parts of that
sample are jointly uniform on the product of the `m + k` coordinates with two
copies of `F_q^m`.  Conditioned on a point coordinate index, the point parts
are therefore uniform, so by
`directCombined_measuredQuestion_of_pointVar` the questions measured by the
combined strategy are the canonical questions of a uniform sample of the
original game at the same ordered type pair; conditioned on a combining
coordinate index, the point part of the sampled point is uniform, so by
`directCombined_measuredQuestion_of_coefficientVar` both measured questions are
the point question at a uniform point.  This single statement subsumes the two
marginal laws `directCombinedSample_pointParts_uniform` and
`directCombinedSample_index_uniform`, which it refines by recording that the
index and the point parts are independent. -/
theorem directCombinedSample_indexPointParts_uniform :
    (uniformDistribution (DirectLdSpace D.combined)).map
        (fun sample => (sample.index,
          (directCombinedPointPart sample.point,
            directCombinedPointPart sample.direction))) =
      uniformDistribution
        (Fin D.combined.m ×
          ((DirectPoint D) × (DirectPoint D))) :=
  uniformDistribution_map_fst_of_equiv (e := directCombinedSpaceIndexEquiv D) _
    fun _ => rfl

end

end MIPStarRE.QPBT
