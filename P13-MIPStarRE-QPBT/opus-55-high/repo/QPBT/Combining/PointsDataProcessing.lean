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

variable {K : Type*}

theorem avgOver_uniform_eq_indicator [Fintype K] [DecidableEq K] [Nonempty K] (x : K) :
    avgOver (uniformDistribution K) (fun y => if y = x then (1 : ℝ) else 0) =
      (Fintype.card K : ℝ)⁻¹ := by
  rw [avgOver_uniform_eq_inv_card_mul_sum]
  simp

/-- The uniform affine check accepts a distinct pair with probability `1/q`.
This also supplies `eq:qld-g-separable`, supporting blueprint `lem:qld-4-7`.
The proof is the existing affine coarse-graining calculation of this module. -/
theorem affine_collision_average [Field K] [Fintype K] [DecidableEq K]
    (p p' : K × K) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
      if coefficients.1 * p.1 + coefficients.2 * p.2 =
          coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
      if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
  calc
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        if coefficients.1 * p.1 + coefficients.2 * p.2 =
            coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
        avgOver (uniformDistribution K) (fun alpha =>
          avgOver (uniformDistribution K) (fun beta =>
            if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
              (1 : ℝ) else 0)) := by
                simpa only using
                  (avgOver_uniform_prod (α := K) (β := K) (fun alpha beta =>
                    if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then
                      (1 : ℝ) else 0))
    _ = if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
      by_cases hp : p = p'
      · subst p'
        simp [avgOver_uniform_const]
      rw [if_neg hp]
      by_cases hfirst : p.1 = p'.1
      · have hdiff : p.2 - p'.2 ≠ 0 := sub_ne_zero.mpr fun h => hp (Prod.ext hfirst h)
        have h (alpha beta : K) :
            alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 ↔ beta = 0 := by
          rw [hfirst]
          refine ⟨fun h => (mul_eq_zero.mp ?_).resolve_right hdiff, by rintro rfl; simp⟩
          linear_combination h
        simp only [h, avgOver_uniform_eq_indicator, avgOver_uniform_const]
      · have hdiff : p.1 - p'.1 ≠ 0 := sub_ne_zero.mpr hfirst
        have h (alpha beta : K) : alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 ↔
            alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) := by
          rw [eq_div_iff hdiff]
          constructor <;> intro h <;> linear_combination h
        rw [avgOver_uniform_comm]
        simp only [h, avgOver_uniform_eq_indicator, avgOver_uniform_const]

theorem sum_fiber_norm_sq_eq_pair_sum
    {Γ R ι : Type*} [Fintype Γ] [Fintype R] [DecidableEq R]
    [Fintype ι] [DecidableEq ι]
    (f : Γ → R) (v : Γ → EuclideanSpace ℂ ι) :
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
      ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
  simp only [@norm_sq_eq_re_inner ℂ, sum_inner, inner_sum, map_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun g => ?_
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun g' => ?_
  split_ifs with h
  · simp [apply_ite, h, inner_re_symm]
  · simp [apply_ite, Ne.symm h]

theorem avg_affine_fiber_norm_sq_le
    {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι]
    (v : K × K → EuclideanSpace ℂ ι) (hsum : ∑ p, v p = 0) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) ≤
      ∑ p, ‖v p‖ ^ 2 := by
  have hall : (∑ p, ∑ p', (inner ℂ (v p) (v p')).re) = 0 := by
    simpa [hsum] using (sum_fiber_norm_sq_eq_pair_sum (fun _ : K × K => ()) v).symm
  have h (p p' : K × K) : (if p = p' then (1 : ℝ) else (Fintype.card K : ℝ)⁻¹) *
      (inner ℂ (v p) (v p')).re = (Fintype.card K : ℝ)⁻¹ * (inner ℂ (v p) (v p')).re +
        if p = p' then (1 - (Fintype.card K : ℝ)⁻¹) * ‖v p‖ ^ 2 else 0 := by
    split_ifs with h <;> simp [h, @norm_sq_eq_re_inner ℂ]
    ring
  simp_rw [sum_fiber_norm_sq_eq_pair_sum, avgOver_sum, ← boole_mul _ (Complex.re _),
    avgOver_mul_const,
    affine_collision_average, h, Finset.sum_add_distrib, ← Finset.mul_sum, hall]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_zero, zero_add, ← Finset.mul_sum]
  exact mul_le_of_le_one_left (by positivity) (sub_le_self _ (by positivity))

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
  unfold opFamilyDistSq
  rw [avgOver_uniform_prod (f := fun x (c : K × K) => ∑ r : K, ‖applyOperatorToState
    ((∑ p ∈ Finset.univ.filter (fun p => c.1 * p.1 + c.2 * p.2 = r), A x p) -
      ∑ p ∈ Finset.univ.filter (fun p => c.1 * p.1 + c.2 * p.2 = r), B x p) ψ‖ ^ 2)]
  refine avgOver_mono _ _ _ fun x => le_of_eq_of_le ?_
    (avg_affine_fiber_norm_sq_le (fun p => applyOperatorToState (A x p - B x p) ψ) ?_)
  · simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply,
      Finset.sum_sub_distrib]
  · rw [← MagicSquareRigidity.applyOperatorToState_sum, Finset.sum_sub_distrib, hsum x, sub_self]
    simp [applyOperatorToState]

variable {P : AdmissibleParams} {ε : ℝ}

/-- Register placement preserves the total of a finite operator family. -/
theorem place_sum (S : ProjectiveSetting P ε) (p : Placement) {α : Type*} [Fintype α]
    (A : α → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a, A a) = ∑ a, S.place p (A a) := by
  ext i j
  cases p <;> simp [ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]

theorem place_one (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (1 : Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j
  cases p <;> simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
  all_goals split_ifs <;> simp_all

/-- A complete measurement remains complete after register placement. -/
theorem sum_placed_measurement_eq_one (S : ProjectiveSetting P ε) (p : Placement) {α : Type*} [Fintype α]
    (M : Measurement α (S.ExpandedLocalSpace p.side)) :
    (∑ a, S.place p (M.effect a)) = 1 := by
  rw [← place_sum, M.sum_eq_one, place_one]

/-- Ordered products of two complete measurements have total identity after placement. -/
theorem sum_placed_measurement_products_eq_one
    (S : ProjectiveSetting P ε) (p : Placement)
    {α β : Type*} [Fintype α] [Fintype β]
    (M : Measurement α (S.ExpandedLocalSpace p.side))
    (N : Measurement β (S.ExpandedLocalSpace p.side)) :
    (∑ ab : α × β, S.place p (M.effect ab.1 * N.effect ab.2)) = 1 := by
  rw [← place_sum, Fintype.sum_prod_type]
  simp [← Finset.mul_sum, ← Finset.sum_mul, M.sum_eq_one, N.sum_eq_one, place_one]

end

end MIPStarRE.QPBT
