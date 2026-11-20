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

section

variable {K Γ R ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype Γ] [Fintype R]
  [DecidableEq R] [Fintype ι] [DecidableEq ι]

/-- The uniform affine check accepts a distinct pair with probability `1/q`.
This also supplies `eq:qld-g-separable`, supporting blueprint `lem:qld-4-7`.
The proof is the existing affine coarse-graining calculation of this module. -/
theorem affine_collision_average
    (p p' : K × K) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
      if coefficients.1 * p.1 + coefficients.2 * p.2 =
          coefficients.1 * p'.1 + coefficients.2 * p'.2 then (1 : ℝ) else 0) =
      if p = p' then 1 else (Fintype.card K : ℝ)⁻¹ := by
  classical
  calc
    _ =
        _ := avgOver_uniform_prod fun alpha beta => if alpha * p.1 + beta * p.2 = alpha * p'.1 + beta * p'.2 then 1 else 0
    _ = _ := by
      by_cases hp : p = p'
      · subst p'
        simp [avgOver_uniform_const]
      · rw [if_neg hp]
        by_cases hfirst : p.1 = p'.1
        · have hdiff := sub_ne_zero.mpr (by
            intro h
            exact hp (Prod.ext hfirst h))
          calc
        _ =
            avgOver (uniformDistribution K) (fun _ =>
              avgOver (uniformDistribution K) (fun beta =>
                if beta = 0 then (1 : ℝ) else 0)) := by
              apply avgOver_congr
              intro alpha
              apply avgOver_congr
              intro beta
              congr 1
              apply propext
              constructor
              · intro h
                rw [hfirst] at h
                have : beta * (p.2 - p'.2) = 0 := by
                  linear_combination h
                exact (mul_eq_zero.mp this).resolve_right hdiff
              · intro h
                subst beta
                simp [hfirst]
            _ = _ := by rw [avgOver_uniform_eq_indicator, avgOver_uniform_const]
        · calc
        _ =
            avgOver (uniformDistribution K) (fun beta =>
              avgOver (uniformDistribution K) (fun alpha =>
                if alpha = beta * (p'.2 - p.2) / (p.1 - p'.1) then
                  1 else 0)) := by
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
                  (eq_div_iff (sub_ne_zero.mpr hfirst)).symm
            _ = _ := by
              calc
                _ =
                    _ := by
                        apply avgOver_congr
                        intro beta
                        exact avgOver_uniform_eq_indicator _
                _ = _ := avgOver_uniform_const _

private theorem sum_fiber_norm_sq_eq_pair_sum
    (f : Γ → R) (v : Γ → EuclideanSpace ℂ ι) :
    (∑ r : R, ‖∑ g ∈ Finset.univ.filter (fun g => f g = r), v g‖ ^ 2) =
      ∑ g : Γ, ∑ g' : Γ,
        if f g = f g' then (inner ℂ (v g) (v g')).re else 0 := by
  classical
  calc
    _ =
        _ := by
              apply Finset.sum_congr rfl
              intro r _
              simp only [@norm_sq_eq_re_inner ℂ, sum_inner, inner_sum, map_sum]
              apply Finset.sum_congr rfl
              intro g _
              apply Finset.sum_congr rfl
              intro g' _
              apply inner_re_symm
    _ = ∑ r : R, ∑ g : Γ, ∑ g' : Γ,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          congr 1 with r
          rw [Finset.sum_filter]
          congr 1 with g
          by_cases hg : f g = r
          · rw [if_pos hg, Finset.sum_filter]
            congr 1 with g'
            by_cases hg' : f g' = r <;> simp [hg, hg']
          · simp [hg]
    _ = ∑ g : Γ, ∑ r : R, ∑ g' : Γ,
        if f g = r ∧ f g' = r then (inner ℂ (v g) (v g')).re else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro g _
          rw [Finset.sum_comm]
    _ = _ := by
          congr 1 with g
          congr 1 with g'
          by_cases hgg' : f g = f g'
          · rw [if_pos hgg', Fintype.sum_eq_single (f g)]
            · simp [hgg']
            · intro r hr
              simp [Ne.symm hr]
          · rw [if_neg hgg']
            apply Finset.sum_eq_zero
            intro r _
            simp only [ite_eq_right_iff]
            intro h
            exact (hgg' (h.1.trans h.2.symm)).elim

private theorem avg_affine_fiber_norm_sq_le
    (v : K × K → EuclideanSpace ℂ ι) (hsum : ∑ p, v p = 0) :
    avgOver (uniformDistribution (K × K)) (fun coefficients =>
        ∑ c : K,
          ‖∑ p ∈ Finset.univ.filter (fun p =>
            coefficients.1 * p.1 + coefficients.2 * p.2 = c), v p‖ ^ 2) ≤
      ∑ p, ‖v p‖ ^ 2 := by
  classical
  let w : _ → _ → ℝ := fun p p' => (inner ℂ (v p) (v p')).re
  let qinv := (Fintype.card K : ℝ)⁻¹
  have hall : (∑ p, ∑ p', w p p') = 0 := by
    simpa [w, hsum] using (sum_fiber_norm_sq_eq_pair_sum (fun _ : K × K => ()) v).symm
  have hdiag : (∑ p, w p p) = ∑ p, ‖v p‖ ^ 2 := by
    congr 1 with p
    exact (@norm_sq_eq_re_inner ℂ _ _ _ _ (v p)).symm
  have hnonneg : 0 ≤ ∑ p, ‖v p‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hqinv : 0 ≤ qinv := by positivity
  calc
    _ =
        _ := by
            apply avgOver_congr
            intro coefficients
            apply sum_fiber_norm_sq_eq_pair_sum
    _ = ∑ p, ∑ p', avgOver (uniformDistribution (K × K)) (fun coefficients =>
          if coefficients.1 * p.1 + coefficients.2 * p.2 =
              coefficients.1 * p'.1 + coefficients.2 * p'.2 then w p p' else 0) := by
            rw [avgOver_sum]
            congr 1 with p
            rw [avgOver_sum]
    _ = ∑ p, ∑ p', if p = p' then w p p' else qinv * w p p' := by
            congr 1 with p
            congr 1 with p'
            calc
              _ =
                  avgOver (uniformDistribution (K × K)) (fun coefficients =>
                    (if coefficients.1 * p.1 + coefficients.2 * p.2 =
                        coefficients.1 * p'.1 + coefficients.2 * p'.2 then
                      (1 : ℝ) else 0) * w p p') := by
                        apply avgOver_congr
                        intro coefficients
                        split <;> simp_all
              _ = (if p = p' then 1 else qinv) * w p p' := by
                    rw [avgOver_mul_const, affine_collision_average]
              _ = _ := by
                    split <;> simp_all
    _ = (1 - qinv) * ∑ p, ‖v p‖ ^ 2 := by
          calc
            _ =
                qinv * (∑ p, ∑ p', w p p') + (1 - qinv) * ∑ p, w p p := by
                  simp [Finset.mul_sum]
                  rw [← Finset.sum_add_distrib]
                  congr 1 with p
                  calc
                    _ =
                        ∑ p', (qinv * w p p' +
                          if p = p' then (1 - qinv) * w p p' else 0) := by
                            congr 1 with p'
                            by_cases h : p = p' <;> simp [h]
                            ring
                    _ = _ := by
                          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                          congr 1
                          rw [Fintype.sum_eq_single p]
                          · simp
                          · intro p' hp'
                            simp [Ne.symm hp']
            _ = _ := by rw [hall, hdiag]; ring
    _ ≤ _ := by nlinarith

end

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
        _ := by
          simpa only using (avgOver_uniform_prod (β := K × K)
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
      let v : K × K → EuclideanSpace ℂ ι := fun p =>
        applyOperatorToState (A x p - B x p) ψ
      have hvsum : ∑ p, v p = 0 := by
        refine Eq.trans ((MagicSquareRigidity.applyOperatorToState_sum
          (fun p => A x p - B x p) ψ).symm) ?_
        simp_all
        simp [applyOperatorToState]
      calc
        _ =
            _ := by
                  apply avgOver_congr
                  intro coefficients
                  congr 1 with c
                  simp [v, applyOperatorToState, LinearMap.sub_apply, map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib]
        _ ≤ _ := avg_affine_fiber_norm_sq_le v hvsum
        _ = _ := rfl

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (p : Placement)
  {α β : Type*} [Fintype α] [Fintype β] (M : Measurement α (S.ExpandedLocalSpace p.side))

/-- Register placement preserves the total of a finite operator family. -/
theorem place_sum
    (A : α → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a, A a) = ∑ a, S.place p (A a) := by
  classical
  ext i j
  cases p <;> simp [ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]

private theorem place_one :
    S.place p (1 : Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j
  cases p <;> simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]
  all_goals split_ifs <;> simp_all [Prod.ext_iff]

/-- A complete measurement remains complete after register placement. -/
theorem sum_placed_measurement_eq_one :
    (∑ a, S.place p (M.effect a)) = 1 := by
  rw [← place_sum, M.sum_eq_one, place_one]

/-- Ordered products of two complete measurements have total identity after placement. -/
theorem sum_placed_measurement_products_eq_one
    (N : Measurement β (S.ExpandedLocalSpace p.side)) :
    (∑ ab : α × β, S.place p (M.effect ab.1 * N.effect ab.2)) = 1 := by
  rw [← place_sum, Fintype.sum_prod_type]
  have hlocal : (∑ a : α, ∑ b : β, M.effect a * N.effect b) = 1 := by
    calc
    _ =
        ∑ a : α, M.effect a * ∑ b : β, N.effect b := by
          congr 1 with a
          rw [Finset.mul_sum]
    _ = (∑ a : α, M.effect a) * ∑ b : β, N.effect b := by rw [Finset.sum_mul]
    _ = 1 := by simp [M.sum_eq_one, N.sum_eq_one]
  rw [hlocal, place_one]

end

end MIPStarRE.QPBT
