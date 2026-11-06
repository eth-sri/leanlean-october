module

public import QPBT.Games.Sandwich.Pasting.CodewordConsistency

/-! # The pinched reduction of the pasting estimate

This module records step 1 of the proof of the adopted statement of
`lem:pasting`: the defect of the pasted family is at most the defect of the
second marginal comparison plus the pinched defect.

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

/-- Conjugating a positive operator by an effect of a measurement is positive.
Formalization-only auxiliary step for `lem:pasting`; the effects of a
measurement are self-adjoint, so the conjugation is a congruence. -/
theorem conj_effect_nonneg {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (M : Measurement α ι) (a : α) {N : Op ι} (hN : 0 ≤ N) :
    0 ≤ M.effect a * N * M.effect a := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  have hpos : ((M.effect a)ᴴ * N * M.effect a).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp hN).conjTranspose_mul_mul_same (M.effect a)
  simp_all [measurement_effect_hermitian]

/-- The pinched first codeword family of `lem:pasting`: the coarse first
codeword effects conjugated by the fine second codeword effects. -/
theorem pinched_sum_eq_one {Γ₂ R₁ ι : Type*} [Fintype Γ₂]
    [DecidableEq Γ₂] [Fintype R₁] [DecidableEq R₁] [Fintype ι] [DecidableEq ι]
    (G : Measurement Γ₂ ι) (P : Measurement R₁ ι)
    (hG : MIPStarRE.QPBT.Measurement.IsProjective G) :
    (∑ a : R₁, ∑ g : Γ₂, G.effect g * P.effect a * G.effect g) = 1 := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, P.sum_eq_one, mul_one, (hG _).isIdempotentElem.eq,
    G.sum_eq_one]

theorem abs_sum_re_inner_le {α E : Type*} [Fintype α] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : α → E) {U V : ℝ} (hu : ∑ p, ‖u p‖ ^ 2 ≤ U) (hv : ∑ p, ‖v p‖ ^ 2 ≤ V) :
    |∑ p, (inner ℂ (u p) (v p)).re| ≤ √U * √V :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun p _ =>
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans <|
    (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans <| mul_le_mul (Real.sqrt_le_sqrt hu)
      (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem sum_norm_sq_eq_of_sum_adjoint_mul_eq_one {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → Op ι) (ψ : EuclideanSpace ℂ ι)
    (hC : (∑ c : γ, (C c)ᴴ * C c) = 1) :
    (∑ c : γ, ‖applyOperatorToState (C c) ψ‖ ^ 2) = ‖ψ‖ ^ 2 := by
  simp_rw [norm_applyOperatorToState_sq_eq]
  have := stateQForm_finset_sum ψ Finset.univ fun c => (C c)ᴴ * C c
  simp_all [stateQForm, applyOperatorToState, @norm_sq_eq_re_inner ℂ]

theorem avgOver_sqrt_le {X : Type*} (D : Distribution X) (hD : D.IsProbability) {e : X → ℝ}
    {E : ℝ} (h : avgOver D e ≤ E) (he : ∀ q, 0 ≤ e q) : avgOver D (fun q => √(e q)) ≤ √E :=
  ((le_abs_self _).trans (MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ e
    (fun q => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) he
      (by rw [hD.weight_sum_eq_one]))).trans (Real.sqrt_le_sqrt h)

/-- The pinched reduction of `lem:pasting`. The defect of the pasted family is
at most the defect of the second marginal comparison plus the pinched defect,
the defect of the first marginal comparison against the first codeword family
conjugated by the fine second codeword effects. This is step 1 of the proof of
the adopted statement in `docs/paper-gaps/qpbt_pasting-product-error.tex`;
blueprint `ch12_qpbt_games.tex:960-990`. -/
theorem consistencyDefect_pasted_le_marginal_add_pinched
    {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hG₂ : ∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) :
    consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
        (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
      consistencyDefect D
        (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
        (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂)) ψ +
      consistencyDefect D
        (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g *
          ((G₁ q.1.1).postprocess (fun g' => eval₁ g' q.1.2)).effect a₁ *
          (G₂ q.1.1).effect g)) ψ := by
  have hpaste : ∀ (q : (X × Y₁) × Y₂) (a : R₁ × R₂), (∑ g₁ : Γ₁, ∑ g₂ : Γ₂, if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
      pastedMeasurement (fun g => (G₁ q.1.1).effect g) (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) =
      ∑ g, if eval₂ g q.2 = a.2 then (G₂ q.1.1).effect g *
        ((G₁ q.1.1).postprocess fun g' => eval₁ g' q.1.2).effect a.1 * (G₂ q.1.1).effect g else 0 := by
    intro q a
    simp only [Measurement.postprocess_effect, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul,
      pastedMeasurement, mul_ite, ite_mul, mul_zero, zero_mul, Prod.ext_iff, ite_and]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => by split_ifs <;> simp
  simp only [hpaste]
  rw [consistencyDefect_placed_eq_one_sub D _ _ ψ hψ fun q => pinched_sum_eq_one (G₂ q.1.1)
      ((G₁ q.1.1).postprocess fun g' => eval₁ g' q.1.2) (hG₂ q.1.1),
    consistencyDefect_placed_eq_one_sub D _ _ ψ hψ fun q => Measurement.sum_eq_one _,
    consistencyDefect_placed_eq_one_sub D _ _ ψ hψ ?_, ← avgOver_add]
  · refine avgOver_mono D _ _ fun q => ?_
    have hG := hG₂ q.1.1
    generalize (G₁ q.1.1).postprocess (fun g' => eval₁ g' q.1.2) = P
    generalize G₂ q.1.1 = G at hG
    generalize A q = M
    have h0 : stateQForm ψ 0 = 0 ∧ ∀ (A : Op ι), heteroKron A (0 : Op ι) = 0 ∧ heteroKron (0 : Op ι) A = 0 := by
      simp [heteroKron, stateQForm, applyOperatorToState]
    have h1 : ∀ p [Decidable p] (A B : Op ι), heteroKron (if p then A else 0) B = if p then heteroKron A B else 0 := by
      intros; split_ifs <;> simp [h0]
    have h2 : ∀ p [Decidable p] (A B : Op ι), heteroKron A (if p then B else 0) = if p then heteroKron A B else 0 := by
      intros; split_ifs <;> simp [h0]
    have hW : ∑ a, ∑ g, stateQForm ψ (heteroKron (M.effect a) (G.effect g)) = 1 := by
      simp only [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, ← heteroKron_finset_sum_left,
        Measurement.sum_eq_one, heteroKron_one_one, stateQForm_one, hψ, one_pow]
    simp only [Measurement.postprocess_effect, Finset.sum_filter, heteroKron_finset_sum_left,
      heteroKron_finset_sum_right, stateQForm_finset_sum, h0, h1, h2, apply_ite (stateQForm ψ)]
    simp only [Finset.sum_comm (s := (Finset.univ : Finset R₂)), Finset.sum_comm (s := (Finset.univ : Finset R₁)),
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (s := (Finset.univ : Finset Γ₂)), Finset.sum_comm (s := (Finset.univ : Finset Γ₂)), ← hW]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun g _ => ?_
    by_cases h : eval₂ g q.2 = a.2 <;> simp [h, eq_comm (a := a.2)]
    refine quadratic_form_mono (sub_nonneg.mp ?_) ψ
    rw [← heteroKron_sub_right]
    refine kronecker_nonneg (M.pos a) ?_
    have := conj_effect_nonneg G g (sub_nonneg.mpr (measurement_effect_le_one P a.1))
    rwa [mul_sub, sub_mul, mul_one, (hG g).isIdempotentElem.eq] at this
  · intro q
    rw [← pinched_sum_eq_one (G₂ q.1.1) ((G₁ q.1.1).postprocess fun g' => eval₁ g' q.1.2) (hG₂ q.1.1),
      Fintype.sum_prod_type]
    simp [Finset.sum_comm (s := (Finset.univ : Finset R₂))]

/-- The Cauchy--Schwarz step of `lem:pasting` at a fixed question: the gap
between the overlap of a projective measurement with a first codeword family
and its overlap with the pinching of that family by a projective family on the
same factor is at most the square root of the summed commutator mass of the two
families. This is step 2 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem abs_pinch_overlap_gap_le_sqrt {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (A P : Measurement R₁ ι) (G : Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hA : MIPStarRE.QPBT.Measurement.IsProjective A)
    (hG : MIPStarRE.QPBT.Measurement.IsProjective G) :
    |∑ a : R₁, (stateQForm ψ (heteroKron (A.effect a) (P.effect a)) -
        stateQForm ψ (heteroKron (A.effect a)
          (∑ g : Γ₂, G.effect g * P.effect a * G.effect g)))| ≤
      Real.sqrt (∑ a : R₁, ∑ g : Γ₂,
        ‖applyOperatorToState (heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) := by
  have hA' : ∀ a, A.effect a * A.effect a = A.effect a := fun a => (hA a).isIdempotentElem.eq
  have hG' : ∀ g, G.effect g * G.effect g = G.effect g := fun g => (hG g).isIdempotentElem.eq
  have key := abs_sum_re_inner_le
    (fun p : R₁ × Γ₂ => applyOperatorToState (heteroKron (A.effect p.1)
      (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1))ᴴ ψ)
    (fun p => applyOperatorToState (heteroKron (A.effect p.1) (G.effect p.2)) ψ) le_rfl
    (sum_norm_sq_eq_of_sum_adjoint_mul_eq_one _ ψ ?_).le
  · simp only [hψ, one_pow, Real.sqrt_one, mul_one, Fintype.sum_prod_type] at key
    calc _ = _ := ?_
      _ ≤ _ := key
      _ ≤ _ := Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun g _ => ?_)
    · congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [← stateQForm_mul_eq_inner, heteroKron_mul, hA', ← stateQForm_finset_sum,
        ← heteroKron_finset_sum_right, ← stateQForm_sub, ← heteroKron_sub_right]
      simp [sub_mul, mul_assoc, hG', ← Finset.mul_sum, G.sum_eq_one]
    · have := sum_norm_mul_apply_le (fun _ : Unit => heteroKron (A.effect a) (1 : Op ι))
        (heteroKron 1 (P.effect a * G.effect g - G.effect g * P.effect a)) ψ (by
          simpa [heteroKron_conjTranspose, measurement_effect_hermitian, heteroKron_mul, hA'] using
            measurement_effect_le_one (Measurement.leftPlacement (ιB := ι) A) a)
      simp only [heteroKron_mul, one_mul, mul_one, Finset.univ_unique, Finset.sum_singleton] at this
      rw [heteroKron_conjTranspose, measurement_effect_hermitian]
      rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, measurement_effect_hermitian, measurement_effect_hermitian, ← neg_sub, heteroKron_neg_right, applyOperatorToState, map_neg, LinearMap.neg_apply, norm_neg]
  · simp [heteroKron_conjTranspose, measurement_effect_hermitian, heteroKron_mul, hA', hG',
      Fintype.sum_prod_type, ← heteroKron_finset_sum_right, ← heteroKron_finset_sum_left, A.sum_eq_one,
      G.sum_eq_one, heteroKron_one_one]

end MIPStarRE.QPBT
