module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryDefect
public import QPBT.Combining.DirectLowDegree.Transport.Combining.Value
public import QPBT.Games.DistanceTheorems.Calculus

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

variable (D : DirectLdParams)

/-- The identification of a point of the combined space with the pair formed by
its point part and its combining part. -/
def directCombinedPointEquiv :
    ((Fin D.m → DirectScalarQ D) × (Fin D.k → DirectScalarQ D)) ≃
      (Fin D.combined.m → DirectScalarQ D) where
  toFun z := combinedPoint z.1 z.2
  invFun z := (directCombinedPointPart D z, directCombinedCoefficientPart D z)
  left_inv z := by
    have h1 : directCombinedPointPart D (combinedPoint z.1 z.2) = z.1 :=
      directCombinedPointPart_combinedPoint D z.1 z.2
    have h2 : directCombinedCoefficientPart D (combinedPoint z.1 z.2) = z.2 :=
      directCombinedCoefficientPart_combinedPoint D z.1 z.2
    show (directCombinedPointPart D (combinedPoint z.1 z.2),
      directCombinedCoefficientPart D (combinedPoint z.1 z.2)) = z
    rw [h1, h2]
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
theorem directCombinedMeasuredQuestion_point (u : Fin D.m → DirectScalarQ D) (α : Fin D.k → DirectScalarQ D) :
    directCombinedMeasuredQuestion D
        (directLdPointQuestionOf D.combined (combinedPoint u α)) =
      directLdPointQuestionOf D u := by
  show directLdPointQuestionOf D
    (directCombinedPointPart D (combinedPoint u α)) = _
  rw [directCombinedPointPart_combinedPoint]

/-- On a point question of the combined game the combined answer, read as a
one-component tuple of scalars, is the combination of the measured point answer
with the combining part of the sampled point. -/
theorem directCombinedPointAnswerMap_comp (u : Fin D.m → DirectScalarQ D) (α : Fin D.k → DirectScalarQ D) :
    (fun a : DirectLdAnswer D => directLdPointValuesOrZero D.combined
        (directCombinedAnswerMap D
          (directLdPointQuestionOf D.combined (combinedPoint u α)) a)) =
      fun a : DirectLdAnswer D => (fun _ : Fin D.combined.k =>
        ∑ r : Fin D.k, α r * directLdPointValuesOrZero D a r) := by
  funext a
  cases a with
  | pointVals b =>
      funext j
      show (∑ r : Fin D.k,
        directCombinedCoefficientPart D (combinedPoint u α) r * b r) = _
      rw [directCombinedCoefficientPart_combinedPoint]
      rfl
  | alinePolys g =>
      funext j
      show (0 : DirectScalarQ D) =
        ∑ r : Fin D.k, α r * (0 : Fin D.k → DirectScalarQ D) r
      simp
  | dlinePolys g =>
      funext j
      show (0 : DirectScalarQ D) =
        ∑ r : Fin D.k, α r * (0 : Fin D.k → DirectScalarQ D) r
      simp

/-! ## The discrepancy estimate in the shape of the transport -/

/-- A constant function on a one-element index set equals a function exactly
when the value of the function at the unique index is the constant. -/
theorem const_eq_fun_iff {ι K : Type*} [Unique ι] (c : K) (h : ι → K) :
    ((fun _ : ι => c) = h) ↔ h default = c := by
  constructor
  · intro hh
    rw [← hh]
  · intro hh
    funext i
    rw [Unique.eq_default i, hh]

/-- The discrepancy estimate of `Recovery` in the shape required by the
transport: for a fixed point, a fixed point answer and a fixed outcome of the
combined game, the probability over the combining vector that the recovered
tuple of values differs from the point answer while the outcome read at the
combined point agrees with the combination is at most the local bound. -/
theorem directCombinedRecoveryEvent_transport (u : Fin D.m → DirectScalarQ D) (b : Fin D.k → DirectScalarQ D)
    (p : DirectPolyTuple D.combined) :
    avgOver (uniformDistribution (Fin D.k → DirectScalarQ D)) (fun α =>
        if evalDirectPolyTupleAt u (directTupleOfCombinedTuple D p) ≠ b ∧
            (fun _ : Fin D.combined.k => ∑ r : Fin D.k, α r * b r) =
              evalDirectPolyTupleAt (D := D.combined) (combinedPoint u α) p then
          (1 : ℝ) else 0) ≤
      directCombinedRecoveryLocalBound D (p default) u := by
  refine le_trans (le_of_eq (avgOver_congr _ _ _ fun α => ?_))
    (directCombinedRecoveryEvent_avg_le D (p default) u b)
  exact if_congr (and_congr Iff.rfl (const_eq_fun_iff _
    (evalDirectPolyTupleAt (D := D.combined) (combinedPoint u α) p))) rfl rfl

/-! ## The two point relations -/

/-- The point relation of `lem:ld-combining-recovery` for a point measurement
family `M` on the first tensor factor: `M` is consistent with the recovered
polynomial tuple evaluated at the sampled point, up to the defect of the
corresponding relation for the combined family plus `(m + k) d / q`. -/
theorem directCombinedRecovery_relation {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (M : DirectLdQuestion D → Measurement (DirectLdAnswer D) ιA)
    (GB : DirectPolyMeasTuple D.combined ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    consistencyDefect (uniformDistribution (Fin D.m → DirectScalarQ D))
        (fun u outcome => heteroKron
          (((M (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D)).effect outcome) 1)
        (fun u outcome => heteroKron 1
          (((GB.postprocess (directTupleOfCombinedTuple D)).postprocess
            (evalDirectPolyTupleAt u)).effect outcome)) ψ ≤
      consistencyDefect
          (uniformDistribution (Fin D.combined.m → DirectScalarQ D))
          (fun z outcome => heteroKron
            ((((M (directCombinedMeasuredQuestion D (directLdPointQuestionOf D.combined z))).postprocess
              (directCombinedAnswerMap D (directLdPointQuestionOf D.combined z))).postprocess
                (directLdPointValuesOrZero D.combined)).effect outcome) 1)
          (fun z outcome => heteroKron 1
            ((GB.postprocess (evalDirectPolyTupleAt (D := D.combined) z)).effect outcome)) ψ +
        ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by
  have hkey := consistencyDefect_le_of_recoveryBound
    (X := Fin D.m → DirectScalarQ D) (Y := Fin D.k → DirectScalarQ D)
    (fun u => (M (directLdPointQuestionOf D u)).postprocess (directLdPointValuesOrZero D))
    GB ψ hψ
    (fun u p => evalDirectPolyTupleAt u (directTupleOfCombinedTuple D p))
    (fun _ α b => (fun _ : Fin D.combined.k => ∑ r : Fin D.k, α r * b r))
    (fun u α p => evalDirectPolyTupleAt (D := D.combined) (combinedPoint u α) p)
    (fun u p => directCombinedRecoveryLocalBound D (p default) u)
    (((D.combined.m * D.d : ℕ) : ℝ) / D.q)
    (fun u b p => directCombinedRecoveryEvent_transport D u b p)
    (fun p => directCombinedRecoveryLocalBound_avg_le D (p default))
  refine le_of_eq_of_le (consistencyDefect_congr _ _ _ _ _ _ (fun u a => rfl) fun u a => by
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp]) (hkey.trans_eq (congrArg
    (fun x : ℝ => x + ((D.combined.m * D.d : ℕ) : ℝ) / D.q) ?_))
  rw [← consistencyDefect_uniform_question_equiv (directCombinedPointEquiv D)]
  refine consistencyDefect_congr _ _ _ _ _ _ (fun z r => ?_) fun z r => rfl
  refine congrArg (fun N : Measurement _ ιA => heteroKron (N.effect r) (1 : Op ιB)) ?_
  refine (MIPStarRE.Quantum.Measurement.postprocess_comp _ _ _).trans ?_
  refine Eq.trans ?_ (MIPStarRE.Quantum.Measurement.postprocess_comp _ _ _).symm
  dsimp only [directCombinedPointEquiv, Equiv.coe_fn_mk]
  rw [directCombinedMeasuredQuestion_point]
  exact congrArg (fun h => (M (directLdPointQuestionOf D z.1)).postprocess h)
    (directCombinedPointAnswerMap_comp D z.1 z.2).symm

end

end MIPStarRE.QPBT
