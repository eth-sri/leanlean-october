module

public import QPBT.Combining.Witnesses

/-!
# Averaged affine coarse-graining of complete operator families

Uniform scalar coefficients give collision probability `1 / card K` for
distinct pairs over a finite field. Expanding the squared state-dependent
distance therefore proves contraction when the two operator families have
the same total operator. The placement lemmas apply this identity to the
complete point measurements and to both ordered measurement products.

## References

This is the finite-dimensional calculation used for the coarse-graining in
`lem:qld-4-12`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1018`.
The operator-family contraction is a formalization-only auxiliary lemma.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

private theorem avgOver_uniform_eq_indicator {K : Type*}
    [Fintype K] [DecidableEq K] [Nonempty K] (x : K) :
    avgOver (uniformDistribution K) (fun y => if y = x then (1 : ℝ) else 0) =
      (Fintype.card K : ℝ)⁻¹ := by
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  simp

/-- The uniform affine check accepts a distinct pair with probability `1/q`.
This also supplies `eq:qld-g-separable`, supporting blueprint `lem:qld-4-7`.
The proof is the existing affine coarse-graining calculation of this module. -/
theorem affine_collision_average {K : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    (p p' : K × K) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
      if coefficients.1 * p.1 + coefficients.2 * p.2 =
          coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
      if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
  classical
  calc
    _ =
        avgOver (uniformDistribution K) (fun alpha =>
          avgOver (uniformDistribution K) (fun beta =>
            if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
              (1 : ℝ) else 0)) := by
                simpa only using
                  (avgOver_uniform_prod (α := K) (β := K) (fun alpha beta =>
                    if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                      (1 : ℝ) else 0))
    _ = _ := by
      by_cases hp : p = p'
      · subst p'
        simp [avgOver_uniform_const]
      · rw [if_neg hp]
        by_cases hfirst : p.1 = p'.1
        · have hsecond : p.2 ≠ p'.2 := by
            intro h
            exact hp (Prod.ext hfirst h)
          simp_all [hfirst, avgOver_uniform_eq_indicator, avgOver_uniform_const]
        · have hdiff := sub_ne_zero.mpr hfirst
          calc
        _ =
            avgOver (uniformDistribution K) (fun beta =>
              avgOver (uniformDistribution K) (fun alpha =>
                if alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) then
                  (1 : ℝ) else 0)) := by
              rw [avgOver_uniform_comm]
              apply avgOver_congr
              intro beta
              apply avgOver_congr
              intro alpha
              congr 1
              apply propext
              exact calc
                _ ↔
                    alpha * (p.1 - p'.1) = beta * (p'.2 - p.2) := by
                      constructor <;> intro h <;> linear_combination h
                _ ↔ _ :=
                  (eq_div_iff hdiff).symm
            _ = _ := by
              calc
                _ =
                    avgOver (uniformDistribution K)
                      (fun _ => (Fintype.card K : ℝ)⁻¹) := by
                        apply avgOver_congr
                        intro beta
                        exact avgOver_uniform_eq_indicator _
                _ = _ := avgOver_uniform_const _

private theorem sum_fiber_norm_sq_eq_pair_sum
    {Γ R ι : Type*} [Fintype Γ] [Fintype R] [DecidableEq R]
    [Fintype ι] [DecidableEq ι]
    (f : Γ → R) (v : Γ → EuclideanSpace ℂ ι) :
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
      ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
  classical
  simp only [@norm_sq_eq_re_inner ℂ, sum_inner, inner_sum, map_sum, inner_re_symm (v _) (v _)]
  exact DistanceCalculus.sum_matching_fibers f f (fun g g' => (inner ℂ (v g) (v g')).re)

private theorem avg_affine_fiber_norm_sq_le
    {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (v : K × K → EuclideanSpace ℂ ι) (hsum : ∑ p, v p = 0) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) ≤
      ∑ p, ‖v p‖ ^ 2 := by
  classical
  let w (p p' : K × K) := (inner ℂ (v p) (v p')).re
  have hall : (∑ p, ∑ p', w p p') = 0 := by
    simp only [w, ← Complex.re_sum, ← inner_sum, hsum, inner_zero_right, Complex.zero_re,
      Finset.sum_const_zero]
  have hdiag : (∑ p, w p p) = ∑ p, ‖v p‖ ^ 2 := by
    simp [w, @norm_sq_eq_re_inner ℂ]
  have hnonneg : 0 ≤ ∑ p, ‖v p‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  simp_rw [sum_fiber_norm_sq_eq_pair_sum _ v, avgOver_sum]
  calc
    _ = ∑ p, ∑ p', (if p = p' then 1 else (Fintype.card K : ℝ)⁻¹) * w p p' := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
      rw [avgOver_ite_const, affine_collision_average]
    _ ≤ _ := by
      rw [sum_diagWeighted, hall, hdiag, mul_zero, add_zero]
      nlinarith [mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card K))) hnonneg]

/-- Uniform affine scalar coarse-graining does not increase the squared
state-dependent distance of complete operator families. -/
theorem opFamilyDistSq_uniform_affine_postprocess_le
    {X K ι : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (A B : X → K × K → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hsum : ∀ x, ∑ p, A x p = ∑ p, B x p) :
    opFamilyDistSq (uniformDistribution (X × (K × K)))
        (fun question c =>
          ∑ p ∈ Finset.univ.filter (fun p =>
            question.2.1 * p.1 + question.2.2 * p.2 = c), A question.1 p)
        (fun question c =>
          ∑ p ∈ Finset.univ.filter (fun p =>
            question.2.1 * p.1 + question.2.2 * p.2 = c), B question.1 p)
        ψ ≤ opFamilyDistSq (uniformDistribution X) A B ψ := by
  classical
  unfold opFamilyDistSq
  calc
    _ =
        avgOver (uniformDistribution X) (fun x =>
          avgOver (uniformDistribution (K × K)) (fun coefficients =>
            ∑ c : K,
              ‖applyOperatorToState
                ((∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                  ∑ p ∈ Finset.univ.filter (fun p =>
                    coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2)) := by
          simpa only using (avgOver_uniform_prod (α := X) (β := K × K)
            (fun x coefficients =>
              ∑ c : K,
                ‖applyOperatorToState
                  ((∑ p ∈ Finset.univ.filter (fun p =>
                      coefficients.1 * p.1 + coefficients.2 * p.2 = c), A x p) -
                    ∑ p ∈ Finset.univ.filter (fun p =>
                      coefficients.1 * p.1 + coefficients.2 * p.2 = c), B x p) ψ‖ ^ 2))
    _ ≤ _ := by
      apply avgOver_mono
      intro x
      let v := fun p =>
        applyOperatorToState (A x p - B x p) ψ
      have hvsum : ∑ p, v p = 0 := by
        simp only [v]
        calc
          _ =
              applyOperatorToState (∑ p, (A x p - B x p)) ψ :=
                (MagicSquareRigidity.applyOperatorToState_sum
                  (fun p => A x p - B x p) ψ).symm
          _ = 0 := by
            rw [Finset.sum_sub_distrib, hsum x, sub_self]
            simp [applyOperatorToState]
      calc
        _ =
            avgOver (uniformDistribution (K × K)) (fun coefficients =>
              ∑ c : K,
                ‖∑ p ∈ Finset.univ.filter (fun p =>
                  coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) := by
                  apply avgOver_congr
                  intro coefficients
                  apply Finset.sum_congr rfl
                  intro c _
                  congr 2
                  simp only [v, applyOperatorToState, map_sub, LinearMap.sub_apply,
                    map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]
        _ ≤ ∑ p, ‖v p‖ ^ 2 := avg_affine_fiber_norm_sq_le v hvsum
        _ = _ := rfl

end

end MIPStarRE.QPBT
