module

public import QPBT.Games.Sandwich.Support
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror

/-! # Consistency and commutation of the pasting codeword families

This module records the cross consistency of the coarse second codeword family,
the commutator estimate for the two coarse families, the collision average of
the distinct second codewords, and the comparison of the fine second codeword
family with its coarse-graining.  These are the codeword-family steps of the
proof of `lem:pasting` recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

theorem placed_left_contraction {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    (M : Measurement R ι) :
    (1 - ∑ b, (heteroKron (M.effect b) (1 : Op ι))ᴴ * heteroKron (M.effect b) 1).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (by
    simpa using measurement_sum_adjoint_mul_le_one (Measurement.leftPlacement (ιB := ι) M)))

theorem placed_right_contraction {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    (M : Measurement R ι) :
    (1 - ∑ b, (heteroKron (1 : Op ι) (M.effect b))ᴴ * heteroKron 1 (M.effect b)).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (by
    simpa using measurement_sum_adjoint_mul_le_one (Measurement.rightPlacement (ιA := ι) M)))

/-- Averaging a collision term against the conditional collision bound. A
family of nonnegative weights indexed by pairs of distinct second codewords,
of total mass at most one for every question of the first marginal, has
average at most `η` once each pair is restricted to the second questions at
which the two codewords agree. This is the averaging step used twice in the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`, the hypothesis being the
conditional collision assumption of `lem:pasting` written out; in step 4 to pass from the
coarse to the fine second codeword family and in step 5 to discard the
colliding part of the coarse cross term; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem avgOver_collision_le {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (c : (X × Y₁) → Γ₂ → Γ₂ → ℝ) (η : ℝ)
    (hD : D.IsProbability) (hη : 0 ≤ η)
    (hc : ∀ p g g', 0 ≤ c p g g')
    (hmass : ∀ p, (∑ g : Γ₂, ∑ g' : Γ₂, c p g g') ≤ 1)
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁)) :
    avgOver D (fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
      if g = g' then 0 else
        if eval₂ g q.2 = eval₂ g' q.2 then c q.1 g g' else 0) ≤ η := by
  have hmarg : ∀ p, (D.map Prod.fst).weight p = ∑ y₂, D.weight (p, y₂) := fun p => by
    rw [Distribution.map_weight, Finset.sum_filter, ← D.sum_univ_eq_sum_support _ fun a ha => by
      simp [D.outsideSupport a ha], Fintype.sum_prod_type]
    simp
  have hS : ∀ p g g', g ≠ g' → ∑ y₂, D.weight (p, y₂) * (if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0)
      ≤ η * ∑ y₂, D.weight (p, y₂) := by
    intro p g g' hg
    rcases (Finset.sum_nonneg fun y₂ _ => D.nonnegative (p, y₂)).lt_or_eq with h | h
    · rw [← hmarg] at h ⊢
      exact hcoll p.1 p.2 h g g' hg
    · rw [← h, mul_zero]
      exact (Finset.sum_le_sum fun y _ => by split_ifs <;> simp [D.nonnegative]).trans h.ge
  rw [avgOver, ← D.sum_univ_eq_sum_support _ fun q hq => by simp [D.outsideSupport q hq],
    Fintype.sum_prod_type]
  calc _ ≤ ∑ p, η * ∑ y₂, D.weight (p, y₂) := Finset.sum_le_sum fun p _ => ?_
    _ = η := by rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := D.weight),
      hD.weight_sum_univ_eq_one, mul_one]
  have hw : 0 ≤ η * ∑ y₂, D.weight (p, y₂) := mul_nonneg hη (Finset.sum_nonneg fun y₂ _ => D.nonnegative _)
  calc _ = ∑ g, ∑ g', if g = g' then 0 else
        c p g g' * ∑ y₂, D.weight (p, y₂) * (if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) := by
        simp only [Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset Y₂))]
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => ?_
        split_ifs <;> simp [mul_comm, mul_ite]
    _ ≤ ∑ g, ∑ g', c p g g' * (η * ∑ y₂, D.weight (p, y₂)) :=
        Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun g' _ => by
          split_ifs with h
          · exact mul_nonneg (hc p g g') hw
          · exact mul_le_mul_of_nonneg_left (hS p g g' h) (hc p g g')
    _ ≤ _ := by
        simp only [← Finset.sum_mul]
        exact mul_le_of_le_one_left hw (hmass p)

/-- The fixed Schmidt mirror of a projective Bob measurement has averaged
consistency defect at most twice that of any Alice predictor. This is the
coarse mirror estimate in the one-sided proof of `lem:pasting`, issue
Dengnifer/MIPStarRE-QPBT-bak#201;
the mirror depends on the state, not on the sampled question. -/
theorem consistencyDefect_schmidtMirror_le {Q α ι : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (D : Distribution Q) (A B : Q → Measurement α ι)
    (ψ : EuclideanSpace ℂ (ι × ι))
    (hB : ∀ question, MIPStarRE.QPBT.Measurement.IsProjective (B question)) :
    consistencyDefect D
      (fun question answer => heteroKron
        ((schmidtMirrorMeasurement ψ (B question)).effect answer) 1)
      (fun question answer => heteroKron 1 ((B question).effect answer)) ψ ≤
    2 * consistencyDefect D
      (fun question answer => heteroKron ((A question).effect answer) 1)
      (fun question answer => heteroKron 1 ((B question).effect answer)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm]
  rw [← avgOver_const_mul]
  refine avgOver_mono D _ _ fun question => ?_
  have hmirror := point_distance_eq_two_defect_of_projective
    (Measurement.leftPlacement (ιB := ι) (schmidtMirrorMeasurement ψ (B question)))
    (Measurement.rightPlacement (ιA := ι) (B question)) ψ
    (Measurement.isProjective_leftPlacement _
      (schmidtMirrorMeasurement_isProjective ψ _ (hB question)))
    (Measurement.isProjective_rightPlacement _ (hB question))
  have hpredict := point_distance_le_two_defect
    (Measurement.leftPlacement (ιB := ι) (A question))
    (Measurement.rightPlacement (ιA := ι) (B question)) ψ
  have hnorm : (∑ answer : α, ‖applyOperatorToState
      (heteroKron ((schmidtMirrorMeasurement ψ (B question)).effect answer) 1 -
        heteroKron 1 ((B question).effect answer)) ψ‖ ^ 2) ≤
      2 * ∑ answer : α, ‖applyOperatorToState
        (heteroKron ((A question).effect answer) 1 -
          heteroKron 1 ((B question).effect answer)) ψ‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun answer _ => ?_
    simpa only [schmidtMirrorMeasurement, Measurement.ofSumEqOne,
      applyOperatorToState, map_sub, LinearMap.sub_apply] using
      schmidtMirror_norm_sq_le ψ ((A question).effect answer) ((B question).effect answer)
        (measurement_effect_hermitian _ _) (measurement_effect_hermitian _ _)
  simp
    at hmirror hpredict
  linarith

end MIPStarRE.QPBT
