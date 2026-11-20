module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryDefect
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Value

/-!
# The recovery of the polynomial-tuple measurements

`lem:ld-combining-recovery` turns the three conclusions of `lem:ld-soundness`
for the combined strategy at the combined parameters into the three conclusions
for the original strategy at the original parameters, by post-processing the
measurements of the combined game with the recovery map of
`def:ld-combining-map`.

The two point relations follow from the consistency-defect transport
inequality.  At a point `(u, α)` of the combined space the point measurement of
the combined strategy is the point measurement of the original strategy at `u`
post-processed by the combination with coefficients `α`, and the polynomial
measurement of the combined game read at that point is the same measurement
read through the recovery map and then combined with the same coefficients; the
two families therefore differ only on the recovery discrepancy event, whose
average is `(m + k) d / q`.  The uniform law on the combined space is the
product of the uniform laws on the point part and on the combining part, which
is the reindexing along
`directCombinedPointEquiv`.

The polynomial relation is data processing: the recovered measurements are
post-processings of the measurements of the combined game.

## Main statements

* `directCombinedPointEquiv` — the point of the combined space with given
  point and combining parts, as an identification.
* `directCombinedRecovery_relation_one` — the first conclusion.
* `directCombinedRecovery_relation_two` — the second conclusion.
* `directCombinedRecovery_relation_three` — the third conclusion.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

/-! ## The two blocks of a point of the combined space -/

section

variable (D : DirectLdParams)

/-- The identification of a point of the combined space with the pair formed by
its point part and its combining part. -/
def directCombinedPointEquiv :
    ((DirectPoint D) × (Fin D.k → DirectScalarQ D)) ≃
      (Fin D.combined.m → DirectScalarQ D) where
  toFun z := combinedPoint z.1 z.2
  invFun z := (directCombinedPointPart z, directCombinedCoefficientPart D z)
  left_inv z := by
    show (directCombinedPointPart (combinedPoint z.1 z.2),
      directCombinedCoefficientPart D (combinedPoint z.1 z.2)) = z
    rw [(directCombinedPointPart_combinedPoint D z.1 z.2), (directCombinedCoefficientPart_combinedPoint D z.1 z.2)]
  right_inv z := by
    funext i
    show Sum.elim (fun j => z (finSumFinEquiv (Sum.inl j)))
      (fun r => z (finSumFinEquiv (Sum.inr r))) (finSumFinEquiv.symm i) = z i
    rcases hi : finSumFinEquiv.symm i with j | r
    · simp only [Sum.elim_inl]
      rw [← hi, Equiv.apply_symm_apply]
    · simp only [Sum.elim_inr]
      rw [← hi, Equiv.apply_symm_apply]

/-! ## The point measurement of the combined strategy -/

/-- On a point question of the combined game the combined strategy measures the
point question of the original game at the point part. -/
private theorem directCombinedMeasuredQuestion_point
    (u : DirectPoint D) (α : Fin D.k → DirectScalarQ D) :
    directCombinedMeasuredQuestion
        (directLdPointQuestionOf D.combined (combinedPoint u α)) =
      directLdPointQuestionOf D u := by
  show directLdPointQuestionOf D
    (directCombinedPointPart (combinedPoint u α)) = _
  simp

end

/-! ## The discrepancy estimate in the shape of the transport -/

/-- A constant function on a one-element index set equals a function exactly
when the value of the function at the unique index is the constant. -/
private theorem const_eq_fun_iff {ι K : Type*} [Unique ι] (c : K) (h : ι → K) :
    ((fun _ : ι => c) = h) ↔ h default = c := by
  constructor
  · intro hh
    rw [← hh]
  · intro hh
    funext i
    rw [Unique.eq_default i, hh]

variable (D : DirectLdParams)

set_option maxHeartbeats 1600000 in
/-- The discrepancy estimate of `Recovery` in the shape required by the
transport: for a fixed point, a fixed point answer and a fixed outcome of the
combined game, the probability over the combining vector that the recovered
tuple of values differs from the point answer while the outcome read at the
combined point agrees with the combination is at most the local bound. -/
private theorem directCombinedRecoveryEvent_transport
    (u : DirectPoint D) (b : Fin D.k → DirectScalarQ D)
    (p : DirectPolyTuple D.combined) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D)) (fun α =>
        if evalDirectPolyTupleAt u (directTupleOfCombinedTuple D p) ≠ b ∧
            (fun _ : Fin D.combined.k => ∑ r : Fin D.k, α r * b r) =
              evalDirectPolyTupleAt (D := D.combined) (combinedPoint u α) p then
          (1 : ℝ) else 0) ≤
      directCombinedRecoveryLocalBound D (p default) u := by
  classical
  refine le_trans (le_of_eq (avgOver_congr _ _ _ fun α => ?_))
    (directCombinedRecoveryEvent_avg_le D _ u b)
  exact if_congr (and_congr Iff.rfl (const_eq_fun_iff _
    _)) rfl rfl

/-! ## The two point relations -/

/-- Read out the combined point measurement of either player. -/
def combinedPointRead {I : Type} [Fintype I] [DecidableEq I]
    (A : DirectLdQuestion D → Measurement (DirectLdAnswer D) I) (z : DirectPoint D.combined) :=
  let q := directLdPointQuestionOf D.combined z
  ((A (directCombinedMeasuredQuestion q)).postprocess (directCombinedAnswerMap D q)).postprocess
    (directLdPointValuesOrZero D.combined)

set_option maxHeartbeats 1600000 in
/-- First conclusion of `lem:ld-combining-recovery`: the point measurement of
the original strategy is consistent with the recovered polynomial tuple
evaluated at the sampled point, up to the defect of the first conclusion for
the combined strategy plus `(m + k) d / q`. -/
theorem directCombinedRecovery_bound {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : DirectLdQuestion D → Measurement (DirectLdAnswer D) I)
    (ψ : EuclideanSpace ℂ (I × J)) (hψ : ‖ψ‖ = 1)
    (GB : DirectPolyMeasTuple D.combined J) :
    bipartiteDefect (uniformDistribution (DirectPoint D))
        (fun u => (A (directLdPointQuestionOf D u)).postprocess
        (directLdPointValuesOrZero D))
        (fun u => (GB.postprocess (directTupleOfCombinedTuple D)).postprocess
        (evalDirectPolyTupleAt u))
        ψ ≤
      bipartiteDefect
          (uniformDistribution (Fin D.combined.m → DirectScalarQ D))
          (fun z => combinedPointRead D A z)
          (fun z => GB.postprocess (evalDirectPolyTupleAt (D := D.combined) z))
          ψ +
        ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by
  classical
  have hmeas : ∀ (u : DirectPoint D)
      (α : Fin D.k → DirectScalarQ D),
      combinedPointRead D A (combinedPoint u α) =
        ((A (directLdPointQuestionOf D u)).postprocess
          (directLdPointValuesOrZero D)).postprocess
          (fun b _ => ∑ r : Fin D.k, α r * b r) := by
    intro u α
    show _ = _
    refine Eq.trans (MIPStarRE.Quantum.Measurement.postprocess_comp _ _ _) ?_
    refine Eq.trans ?_ (MIPStarRE.Quantum.Measurement.postprocess_comp
      (A (directLdPointQuestionOf D u)) (directLdPointValuesOrZero D)
      (fun b (_ : Fin D.combined.k) => ∑ r : Fin D.k, α r * b r)).symm
    rw [directCombinedMeasuredQuestion_point]
    exact congrArg (fun h => (A (directLdPointQuestionOf D u)).postprocess h)
      ((by
         funext a
         cases a with
         | pointVals b =>
             funext j
             show (∑ r : Fin D.k,
               directCombinedCoefficientPart D (combinedPoint u α) r * b r) = _
             simp
             rfl
         | alinePolys g =>
             funext j
             show 0 =
               ∑ r : Fin D.k, α r * (0 : Fin D.k → DirectScalarQ D) r
             simp
         | dlinePolys g =>
             funext j
             show 0 =
               ∑ r : Fin D.k, α r * (0 : Fin D.k → DirectScalarQ D) r
             simp))
  simp_rw [MIPStarRE.Quantum.Measurement.postprocess_comp GB]
  refine le_trans (consistencyDefect_le_of_recoveryBound
    (fun u => (A (directLdPointQuestionOf D u)).postprocess
    (directLdPointValuesOrZero D))
    GB ψ hψ
    (fun u p => evalDirectPolyTupleAt u (directTupleOfCombinedTuple D p))
    (fun _ α b => (fun _ : Fin D.combined.k => ∑ r : Fin D.k, α r * b r))
    (fun u α p => evalDirectPolyTupleAt (combinedPoint u α) p)
    _
    _
    (directCombinedRecoveryEvent_transport D)
    (fun p => directCombinedRecoveryLocalBound_avg_le D (p default))) (le_of_eq (congrArg
    (fun x : ℝ => x + (D.combined.m * D.d : ℕ) / D.q) ?_))
  simp only [bipartiteDefect]
  rw [← consistencyDefect_uniform_question_equiv (directCombinedPointEquiv D)
    (fun z r => heteroKron ((combinedPointRead D A z).effect r) 1)
    (fun z r => heteroKron 1 ((GB.postprocess (evalDirectPolyTupleAt z)).effect r)) ψ]
  refine consistencyDefect_congr _ _ _ _ _ _ (fun z r => ?_) fun z r => rfl
  exact congrArg (fun M => heteroKron (M.effect r) (1 : Op J)) (hmeas z.1 z.2).symm

end

end MIPStarRE.QPBT
