module

public import QPBT.Games.Sandwich.Pasting.PinchedReduction

/-! # Moving a second codeword effect across the tensor factors

This module records the estimate of step 5 of the proof of the adopted
statement of `lem:pasting`: in the cross term of the commutator mass of a first
codeword family against a second codeword family, the rightmost second codeword
effect is moved to the opposite tensor factor at the cost of the square root of
the summed cross distance of that family.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

variable {R₁ Γ₂ ι : Type*} [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι] (P : Measurement R₁ ι)

theorem sum_rightPlacement_adjoint_mul_le_one {R : Type*} [Fintype R] (P : Measurement R ι) :
    ∑ a, (heteroKron (1 : Op ι) (P.effect a))ᴴ * heteroKron 1 (P.effect a) ≤ 1 := by
  simpa using measurement_sum_adjoint_mul_le_one (Measurement.rightPlacement (ιA := ι) P)

/-- The total mass of the ordered products of two measurements placed on the
second tensor factor is at most one. Blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem sum_norm_ordered_product_le_one (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1) :
    (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
      (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) ≤ 1 := by
  rw [Finset.sum_comm]
  calc _ ≤ ∑ g, ‖applyOperatorToState (heteroKron 1 (G.effect g)) ψ‖ ^ 2 :=
        Finset.sum_le_sum fun g _ => by
          simpa [heteroKron_mul] using sum_norm_mul_apply_le _
            (heteroKron 1 (G.effect g)) ψ (sum_rightPlacement_adjoint_mul_le_one P)
    _ ≤ 1 := by
      simpa [applyOperatorToState, hψ] using sum_norm_mul_apply_le _ 1 ψ
        (sum_rightPlacement_adjoint_mul_le_one G)

/-- The cross move with independently chosen opposite-register and Bob families.
The error is their actual cross distance; no identical-copy or symmetry
assumption is used. -/
theorem abs_cross_move_gap_le_sqrt_distinct_families (G opposite : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1) :
    |(∑ a : R₁, ∑ g : Γ₂, stateQForm ψ (heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a))) -
        ∑ g : Γ₂, stateQForm ψ (heteroKron (opposite.effect g)
          (∑ a : R₁, P.effect a * G.effect g * P.effect a))| ≤
      Real.sqrt (∑ g : Γ₂, ‖applyOperatorToState
        (heteroKron 1 (G.effect g) - heteroKron (opposite.effect g) 1) ψ‖ ^ 2) := by
  have key := abs_sum_re_inner_le
    (fun p : R₁ × Γ₂ => applyOperatorToState ((heteroKron 1 (G.effect p.2) -
      heteroKron (opposite.effect p.2) 1) * heteroKron 1 (P.effect p.1))ᴴ ψ)
    (fun p => applyOperatorToState (heteroKron 1 (G.effect p.2 * P.effect p.1)) ψ) le_rfl
    ((Fintype.sum_prod_type _).trans_le (Finset.sum_comm.trans_le
      (sum_norm_ordered_product_le_one G P ψ hψ)))
  rw [Real.sqrt_one, mul_one] at key
  calc _ = _ := ?_
    _ ≤ _ := key
    _ ≤ _ := Real.sqrt_le_sqrt ?_
  · simp only [← stateQForm_mul_eq_inner, Fintype.sum_prod_type, sub_mul, heteroKron_mul,
      stateQForm_sub, Finset.sum_sub_distrib, heteroKron_finset_sum_right, stateQForm_finset_sum,
      one_mul, mul_one, mul_assoc]
    rw [Finset.sum_comm (s := (Finset.univ : Finset Γ₂))]
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, heteroKron_conjTranspose,
      measurement_effect_hermitian, Matrix.conjTranspose_one, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun g _ => sum_norm_mul_apply_le _ _ ψ
      (sum_rightPlacement_adjoint_mul_le_one P)

/-- The expansion of the commutator mass of `lem:pasting` at a fixed question.
For a measurement and a projective measurement placed on the second tensor
factor, the summed squared norm of the commutators is the summed squared norm
of the ordered products, plus the expectation of the squares of the effects of
the first family, minus twice the cross term. This is the term-by-term
expansion of step 5 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem commutator_mass_eq_expansion (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι))
    (hG : MIPStarRE.QPBT.Measurement.IsProjective G) :
    (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1
        (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
      (∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
          (heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
        (∑ a : R₁, stateQForm ψ (heteroKron 1 (P.effect a * P.effect a))) -
        2 * ∑ a : R₁, ∑ g : Γ₂, stateQForm ψ (heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a)) := by
  have hG' : ∀ g, G.effect g * G.effect g = G.effect g := fun g => (hG g).isIdempotentElem.eq
  have h1 : ∀ a g, stateQForm ψ (heteroKron 1 (P.effect a * (G.effect g * (P.effect a * G.effect g)))) =
      stateQForm ψ (heteroKron 1 (G.effect g * (P.effect a * (G.effect g * P.effect a)))) := by
    intro a g
    rw [← stateQForm_conjTranspose, heteroKron_conjTranspose]
    simp [Matrix.conjTranspose_mul, measurement_effect_hermitian, mul_assoc]
  have h2 : ∀ a, ∑ g, stateQForm ψ (heteroKron 1 (P.effect a * (G.effect g * (G.effect g * P.effect a)))) =
      stateQForm ψ (heteroKron 1 (P.effect a * P.effect a)) := by
    intro a
    simp [← mul_assoc, hG', ← stateQForm_finset_sum, ← heteroKron_finset_sum_right, ← Finset.sum_mul,
      ← Finset.mul_sum, G.sum_eq_one]
  simp only [norm_applyOperatorToState_sq_eq_stateQForm, heteroKron_conjTranspose, heteroKron_mul,
    Matrix.conjTranspose_one, one_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    measurement_effect_hermitian, sub_mul, mul_sub, heteroKron_sub_right, stateQForm_sub,
    Finset.sum_sub_distrib, mul_assoc, h1, h2]
  ring

end MIPStarRE.QPBT
