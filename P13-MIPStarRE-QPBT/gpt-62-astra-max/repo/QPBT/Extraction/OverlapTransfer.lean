module

public import QPBT.Extraction.PolynomialCollision
public import QPBT.Games.Sandwich.Support
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Transfer of the complete Pauli overlap between states

A selected sum of effects of a complete measurement is a positive contraction.
Applied to the product measurement, this bounds the complete overlap operator,
independently of the number of answers. Its expectation changes by at most twice
the distance between unit vectors. Schwartz--Zippel then removes unequal Pauli
encodings after the change of state.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Changing a unit vector changes the expectation of a contraction by at most
twice the vector distance. No positivity or self-adjointness is required. -/
theorem abs_stateQForm_sub_le_of_contraction {ι : Type*}
    [Fintype ι] [DecidableEq ι] (T : Op ι)
    (hT : ∀ v : EuclideanSpace ℂ ι, ‖applyOperatorToState T v‖ ≤ ‖v‖)
    (psi phi : EuclideanSpace ℂ ι) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    |stateQForm psi T - stateQForm phi T| ≤ 2 * ‖psi - phi‖ := by
  have hsplit : stateQForm psi T - stateQForm phi T =
      (inner ℂ (psi - phi) (applyOperatorToState T psi)).re +
        (inner ℂ phi (applyOperatorToState T (psi - phi))).re := by
    simp [stateQForm, applyOperatorToState]
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
    ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))) ?_
  refine LE.le.trans_eq (add_le_add (mul_le_mul_of_nonneg_left (hT psi) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (hT (psi - phi)) (norm_nonneg _))) ?_
  simp_all; ring

/-- The complete diagonal overlap of two local measurements is stable under a
change of unit state. The tensor factors can have different dimensions. -/
theorem abs_diagonal_overlap_state_sub_le {α I J : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Measurement α I) (B : Measurement α J)
    (psi phi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    |(∑ a, stateQForm psi (heteroKron (A.effect a) (B.effect a))) -
      ∑ a, stateQForm phi (heteroKron (A.effect a) (B.effect a))| ≤
        2 * ‖psi - phi‖ := by
  let s := Finset.univ.filter (fun ab : α × α => ab.1 = ab.2)
  have heq : (∑ ab ∈ s, (tensorMeasurement A B).effect ab) =
      ∑ a, heteroKron (A.effect a) (B.effect a) := by
    simp [s, Finset.sum_filter, Fintype.sum_prod_type, tensorMeasurement,
      Measurement.ofSumEqOne]
  have h := abs_stateQForm_sub_le_of_contraction _
    ((by
       have hpos : 0 ≤ ∑ a ∈ s, (tensorMeasurement A B).effect a := Finset.sum_nonneg (fun a _ => (tensorMeasurement A B).pos a)
       have hle : ∑ a ∈ s, (tensorMeasurement A B).effect a ≤ 1 := by
         rw [← (tensorMeasurement A B).sum_eq_one]
         exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
           (fun a _ _ => (tensorMeasurement A B).pos a)
       apply MagicSquareRigidity.norm_applyOperatorToState_le
       rw [(Matrix.nonneg_iff_posSemidef.mp hpos).isHermitian.eq]
       exact (MIPStarRE.Quantum.sq_le_self hpos hle).trans hle)) psi phi hpsi hphi
  simp [heq, stateQForm_finset_sum] at h
  exact h

/-- Averaging evaluated overlaps does not increase the state-transfer cost.
This controls the complete overlap in paper `eq:qld-unitary-9`. -/
theorem evaluated_overlap_state_transfer {Y α R I J : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype α] [DecidableEq α] [Fintype R] [DecidableEq R]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement α J) (eval : α → Y → R)
    (psi phi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    avgOver (uniformDistribution Y) (fun y => ∑ r, stateQForm psi
      (heteroKron ((A.postprocess (fun a => eval a y)).effect r)
        ((B.postprocess (fun a => eval a y)).effect r))) ≤
      avgOver (uniformDistribution Y) (fun y => ∑ r, stateQForm phi
        (heteroKron ((A.postprocess (fun a => eval a y)).effect r)
          ((B.postprocess (fun a => eval a y)).effect r))) + 2 * ‖psi - phi‖ := by
  have h := avgOver_mono (uniformDistribution Y) _ _ (fun y =>
    (le_abs_self _).trans (abs_diagonal_overlap_state_sub_le
      (A.postprocess (fun a => eval a y)) (B.postprocess (fun a => eval a y))
      psi phi hpsi hphi))
  rw [avgOver_sub, avgOver_const_of_isProbability _
    (uniformDistribution_isProbability _)] at h
  linarith

/-- Two distinct Pauli answers have encodings agreeing on at most an `md/q`
fraction of points. Injectivity follows from the exact decoder identity. -/
theorem pauli_encoding_collision_le {P : AdmissibleParams}
    (h k : PauliRegister P) (hne : h ≠ k) :
    avgOver (uniformDistribution (PauliPoint P))
      (fun u => if evalPoly (encodingPoly h) u = evalPoly (encodingPoly k) u
        then (1 : ℝ) else 0) ≤ (P.m * P.d : ℝ) / P.q := by
  apply poly_eval_collision_le
  intro heq
  apply hne
  simpa only [decodeFq_lowDegreeEncoding] using (congrArg (fun g : Poly P => decodeFq g) heq)

end

end MIPStarRE.QPBT
