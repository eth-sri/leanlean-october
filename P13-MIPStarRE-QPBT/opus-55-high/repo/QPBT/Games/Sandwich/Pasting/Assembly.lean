module

public import QPBT.Games.Sandwich.Pasting.CrossMove

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

theorem sum_norm_sq_proj {γ ι : Type*} [Fintype γ] [Fintype ι] [DecidableEq ι]
    (M : Measurement γ ι) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (ψ : EuclideanSpace ℂ ι) : ∑ c, ‖applyOperatorToState (M.effect c) ψ‖ ^ 2 = ‖ψ‖ ^ 2 :=
  sum_norm_sq_eq_of_sum_adjoint_mul_eq_one _ ψ (by
    simp_rw [measurement_effect_hermitian, (hM _).isIdempotentElem.eq, M.sum_eq_one])

theorem sum_norm_sq_le_of_mass_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (u v : α → EuclideanSpace ℂ ι) (hu : (∑ a : α, ‖u a‖ ^ 2) ≤ 1) :
    (∑ a : α, ‖v a‖ ^ 2) ≤ (∑ a : α, ‖u a‖ ^ 2) +
      2 * Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) + ∑ a : α, ‖u a - v a‖ ^ 2 := by
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => show ‖v a‖ ^ 2 ≤
      ‖u a‖ ^ 2 + 2 * (‖u a‖ * ‖u a - v a‖) + ‖u a - v a‖ ^ 2 by
    nlinarith [norm_nonneg (v a), norm_nonneg (u a - v a), norm_le_norm_add_norm_sub' (v a) (u a), norm_sub_rev (u a) (v a)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  nlinarith [Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖u a‖) (fun a => ‖u a - v a‖),
    Real.sqrt_le_one.mpr hu, Real.sqrt_nonneg (∑ a, ‖u a - v a‖ ^ 2), Real.sqrt_nonneg (∑ a, ‖u a‖ ^ 2)]

theorem avgOver_two_step {X : Type*} (D : Distribution X) (hD : D.IsProbability)
    (S C e₁ e₂ : X → ℝ) {E₁ E₂ : ℝ} (h₁ : avgOver D e₁ ≤ E₁) (h₂ : avgOver D e₂ ≤ E₂)
    (he₁ : ∀ q, 0 ≤ e₁ q) (he₂ : ∀ q, 0 ≤ e₂ q)
    (hS : ∀ q, 1 ≤ S q + 2 * √(e₁ q) + e₁ q) (hC : ∀ q, S q ≤ C q + 2 * √(e₂ q) + e₂ q) :
    1 - (2 * √E₁ + E₁ + 2 * √E₂ + E₂) ≤ avgOver D C := by
  have m1 := avgOver_mono D (fun _ => 1) _ hS
  have m2 := avgOver_mono D S _ hC
  simp only [avgOver_add, avgOver_const_mul, avgOver_const_of_isProbability D hD] at m1 m2
  linarith [avgOver_sqrt_le D hD h₁ he₁, avgOver_sqrt_le D hD h₂ he₂]

theorem mass_ordered_product_ge {X R₁ R₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution X) (Ac P : X → Measurement R₁ ι) (Q : X → Measurement R₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (d K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAc : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (Ac q))
    (hQ : ∀ q, MIPStarRE.QPBT.Measurement.IsProjective (Q q))
    (hd : opFamilyDistSq D (fun q a => heteroKron ((Ac q).effect a) 1)
      (fun q a => heteroKron 1 ((P q).effect a)) ψ ≤ d)
    (hK : opFamilyDistSq D (fun q (ab : R₁ × R₂) => heteroKron 1
      ((P q).effect ab.1 * (Q q).effect ab.2 -
        (Q q).effect ab.2 * (P q).effect ab.1)) (fun _ _ => 0) ψ ≤ K) :
    1 - (2 * √d + d + 2 * √K + K) ≤
      avgOver D (fun q => ∑ ab : R₁ × R₂, ‖applyOperatorToState
        (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ‖ ^ 2) := by
  refine avgOver_two_step D hD
    (fun q => ∑ a, ‖applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ‖ ^ 2) _ _ _ hd hK
    (fun q => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (fun q => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun q => ?_) (fun q => ?_)
  · have := sum_norm_sq_le_of_mass_le_one _
      (fun a => applyOperatorToState (heteroKron ((Ac q).effect a) 1) ψ) (by
        simpa [hψ, applyOperatorToState] using sum_norm_mul_apply_le _ 1 ψ
          (measurement_sum_adjoint_mul_le_one (Measurement.rightPlacement (ιA := ι) (P q))))
    have hA := sum_norm_sq_proj _ (Measurement.isProjective_leftPlacement (ιB := ι) _ (hAc q)) ψ
    simp only [Measurement.leftPlacement_effect, hψ, one_pow] at hA
    rw [hA] at this
    simpa [norm_sub_rev, applyOperatorToState] using this
  · have := sum_norm_sq_le_of_mass_le_one (fun ab : R₁ × R₂ => applyOperatorToState
        (heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ)
      (fun ab => applyOperatorToState (heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ)
      (by simpa [Fintype.sum_prod_type] using sum_norm_ordered_product_le_one (P q) (Q q) ψ hψ)
    have hR : ∀ a, ∑ b, ‖applyOperatorToState (heteroKron 1 ((Q q).effect b * (P q).effect a)) ψ‖ ^ 2 =
        ‖applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ‖ ^ 2 := fun a => by
      simpa [← applyOperatorToState_mul, heteroKron_mul] using sum_norm_sq_proj _
        (Measurement.isProjective_rightPlacement (ιA := ι) _ (hQ q))
        (applyOperatorToState (heteroKron 1 ((P q).effect a)) ψ)
    simp only [Fintype.sum_prod_type, hR] at this
    simpa [heteroKron_sub_right, applyOperatorToState, Fintype.sum_prod_type] using this

/-- The coarse pinched cross term exceeds the fine one by the colliding pairs of
second codewords. Grouping the fine effects into the fibers of the evaluation
map splits the coarse expectation into its diagonal, which is the fine
expectation, and the pairs of distinct codewords agreeing at the sampled second
question. This is the term comparison of step 5 of the proof of the adopted
statement in `docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem pinched_coarse_sub_fine_eq_distinct_families {R₁ R₂ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (P : Measurement R₁ ι) (G opposite : Measurement Γ₂ ι) (eval : Γ₂ → R₂)
    (ψ : EuclideanSpace ℂ (ι × ι)) :
    (∑ b : R₂, stateQForm ψ (heteroKron ((opposite.postprocess eval).effect b)
        (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a))) -
      (∑ g : Γ₂, stateQForm ψ (heteroKron (opposite.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
    ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
      if eval g = eval g' then
        ∑ a : R₁, stateQForm ψ (heteroKron (opposite.effect g')
          (P.effect a * G.effect g * P.effect a)) else 0 := by
  have h0 : stateQForm ψ 0 = 0 ∧ ∀ (A : Op ι), heteroKron A (0 : Op ι) = 0 ∧ heteroKron (0 : Op ι) A = 0 := by
    simp [heteroKron, stateQForm, applyOperatorToState]
  have h1 : ∀ p [Decidable p] (A B : Op ι), heteroKron (if p then A else 0) B = if p then heteroKron A B else 0 := by
    intros; split_ifs <;> simp [h0]
  simp only [Measurement.postprocess_effect, Finset.mul_sum, Finset.sum_mul,
    heteroKron_finset_sum_left, heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter,
    mul_ite, ite_mul, mul_zero, zero_mul, apply_ite (heteroKron _), h0, h1, apply_ite (stateQForm ψ)]
  simp [Finset.sum_comm (s := (Finset.univ : Finset R₂)), Finset.sum_ite_irrel,
    Finset.sum_comm (s := (Finset.univ : Finset R₁))]
  rw [sub_eq_iff_eq_add', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ g), ← Finset.add_sum_erase _ _ (Finset.mem_univ g)]
  simp only [ite_true, zero_add, add_right_inj]
  exact Finset.sum_congr rfl fun x hx => by simp [(Finset.ne_of_mem_erase hx).symm, eq_comm]

/-- The defect of two placed measurement families never exceeds one. The
diagonal overlaps of the two placements are nonnegative and the total overlap
equals the squared norm of the state, so the off-diagonal sum of
`def:consistency` is at most one. Formalization-only auxiliary of the trivial
regime of `lem:pasting`, blueprint `ch12_qpbt_games.tex:195-208,960-990`. -/
theorem consistencyDefect_placed_le_one {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 1 := by
  rw [SandwichProduct.consistencyDefect_placed_eq_avg_point]
  refine avgOver_le_of_weight_sum_le_one μ _ 1 (le_of_eq hμ.weight_sum_eq_one)
    zero_le_one ?_
  intro x
  have hpoint := point_defect_eq (leftPlacedMeasurement (ιB := ιB) (A x))
    (rightPlacedMeasurement (ιA := ιA) (B x)) ψ
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hpoint
  simp_rw [placed_product_stateQForm_eq] at hpoint
  have hdiag : 0 ≤ ∑ a : α, stateQForm ψ
      (heteroKron ((A x).effect a) ((B x).effect a)) :=
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _
      (MIPStarRE.Quantum.kronecker_nonneg ((A x).pos a) ((B x).pos a))
  rw [hpoint, hψ]
  norm_num
  exact hdiag

/-- On the unit square the assembled error of the pasting estimate is at most
`(3 * C + 19) * (η ^ (1/4) + δ ^ (1/8))`. Substituting `δ = u ^ 8` and
`η = v ^ 4` turns every summand of the radicand into a polynomial in the two
roots. Formalization-only arithmetic auxiliary of `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem pasting_error_sqrt_le_rpow (C δ η : ℝ) (hC : 1 ≤ C) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    2 * δ + Real.sqrt (C * δ +
      (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
      2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
      2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ)))) ≤
      (3 * C + 19) * (η ^ (1/4 : ℝ) + δ ^ (1/8 : ℝ)) := by
  have hu := Real.rpow_nonneg hδ0 (1/8)
  have hv := Real.rpow_nonneg hη0 (1/4)
  have hδ : δ = (δ ^ (1/8 : ℝ)) ^ 8 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0]; norm_num
  have hη : η = (η ^ (1/4 : ℝ)) ^ 4 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hη0]; norm_num
  generalize δ ^ (1/8 : ℝ) = u at hu hδ ⊢
  generalize η ^ (1/4 : ℝ) = v at hv hη ⊢
  subst hδ hη
  have hu1 : u ≤ 1 := (pow_le_one_iff_of_nonneg hu (by norm_num)).mp hδ1
  have hv1 : v ≤ 1 := (pow_le_one_iff_of_nonneg hv (by norm_num)).mp hη1
  have h1 : √(2 * u ^ 8) ≤ 2 * u ^ 4 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [pow_nonneg hu 8]⟩
  have h2 : √(C * u ^ 8) ≤ C * u ^ 4 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [pow_nonneg hu 8]⟩
  have h3 : √(2 * (u ^ 8 + 2 * √(2 * u ^ 8))) ≤ 4 * u ^ 2 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [pow_le_pow_of_le_one hu hu1 (show 4 ≤ 8 by norm_num), pow_nonneg hu 4]⟩
  have h4 : √(2 * (u ^ 8 + 2 * √(2 * u ^ 8) + v ^ 4)) ≤ 4 * u ^ 2 + 2 * v ^ 2 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [pow_le_pow_of_le_one hu hu1 (show 4 ≤ 8 by norm_num), pow_nonneg hu 4, pow_nonneg hv 4, mul_nonneg (sq_nonneg u) (sq_nonneg v)]⟩
  have h82 := pow_le_pow_of_le_one hu hu1 (show 2 ≤ 8 by norm_num)
  have h42 := pow_le_pow_of_le_one hu hu1 (show 2 ≤ 4 by norm_num)
  have h81 := pow_le_pow_of_le_one hu hu1 (show 1 ≤ 8 by norm_num)
  have v42 := pow_le_pow_of_le_one hv hv1 (show 2 ≤ 4 by norm_num)
  calc _ ≤ 2 * u ^ 8 + ((C + 5) * u + 3 * v) := by
        gcongr
        exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_le_mul_of_nonneg_left h82 (show 0 ≤ C by linarith), mul_le_mul_of_nonneg_left h42 (show 0 ≤ C by linarith), mul_nonneg hu hv, sq_nonneg (C * u), mul_nonneg (show 0 ≤ C by linarith) (sq_nonneg u)]⟩
    _ ≤ _ := by nlinarith

end MIPStarRE.QPBT
