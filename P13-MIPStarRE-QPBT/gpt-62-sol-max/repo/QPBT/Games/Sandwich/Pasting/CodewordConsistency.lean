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
    [Fintype Y₂] [DecidableEq Y₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (c : (X × Y₁) → Γ₂ → Γ₂ → ℝ) (η : ℝ)
    (hD : D.IsProbability) (hη : 0 ≤ η)
    (hc : ∀ p g g', 0 ≤ c p g g')
    (hmass : ∀ p, (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else c p g g') ≤ 1)
    (hcoll : HasConditionalCollisionBound D eval₂ η) :
    avgOver D (fun q => ∑ g : Γ₂, ∑ g' : Γ₂,
      if g = g' then 0 else
        if eval₂ g q.2 = eval₂ g' q.2 then c q.1 g g' else 0) ≤ η := by
  classical
  have hterm (p : X × Y₁) (g g' : Γ₂) :
      (∑ y : Y₂, D.weight (p, y) *
        (if g = g' then 0 else if eval₂ g y = eval₂ g' y then c p g g' else 0)) ≤
      (if g = g' then 0 else c p g g') * (η * (D.map Prod.fst).weight p) := by
    by_cases hgg : g = g'
    · simp [hgg]
    simp only [if_neg hgg]
    calc
      _ = c p g g' * ∑ y : Y₂, D.weight (p, y) *
            (if eval₂ g y = eval₂ g' y then 1 else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by split <;> simp_all [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoll p g g' hgg) (hc p g g')
  have hm : (D.map Prod.fst).IsProbability := by
    simpa only [Distribution.IsProbability, Distribution.map_totalWeight] using hD
  calc
    _ = ∑ p : X × Y₁, ∑ g : Γ₂, ∑ g' : Γ₂, ∑ y : Y₂,
          D.weight (p, y) * (if g = g' then 0 else
            if eval₂ g y = eval₂ g' y then c p g g' else 0) := by
      rw [avgOver_eq_sum_univ, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun g _ => Finset.sum_comm
    _ ≤ _ := by
      rw [← mul_one η, ← hm.weight_sum_univ_eq_one, Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => (Finset.sum_le_sum fun g _ =>
        Finset.sum_le_sum fun g' _ => hterm p g g').trans ?_
      simp_rw [← Finset.sum_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hmass p) (mul_nonneg hη ((D.map Prod.fst).nonnegative p))

/-- Off-diagonal pairs in a common fiber are the excess over the diagonal. -/
theorem sum_colliding_sub_diagonal {Γ R : Type*} [Fintype Γ] [DecidableEq Γ]
    [DecidableEq R] (f : Γ → R) (w : Γ → Γ → ℝ) :
    (∑ g, ∑ g', if f g = f g' then w g g' else 0) - ∑ g, w g g =
      ∑ g, ∑ g', if g = g' then 0 else if f g = f g' then w g g' else 0 := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [show w g g = ∑ g', if g = g' then w g g' else 0 by simp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun g' _ => by by_cases h : g = g' <;> simp_all

/-- Averaging over the off-diagonal of a nonnegative kernel cannot increase its total mass. -/
theorem sum_offDiag_le_total {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (w : Γ → Γ → ℝ) (hw : ∀ g g', 0 ≤ w g g') :
    (∑ g, ∑ g', if g = g' then 0 else w g g') ≤ ∑ g, ∑ g', w g g' :=
  Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun g' _ => by
    split_ifs <;> simp [hw]

/-- Coarse evaluation hides only those pairs of distinct codewords that collide. -/
theorem consistencyDefect_codeword_fine_le_coarse_add_distinct_families
    {X Y₁ Y₂ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → Measurement Γ₂ ι) (ψ : EuclideanSpace ℂ (ι × ι)) (η : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : HasConditionalCollisionBound D eval₂ η) :
    bipartiteDefect D
        (fun q => opposite q.1.1)
        (fun q => G₂ q.1.1) ψ ≤
      bipartiteDefect D
        (fun q => (opposite q.1.1).postprocess
          (fun g => eval₂ g q.2))
        (fun q => (G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)) ψ + η := by
  classical
  let f : ((X × Y₁) × Y₂) → Γ₂ → R₂ := fun q g => eval₂ g q.2
  let w (p : X × Y₁) g g' := stateQForm ψ
    (heteroKron ((opposite p.1).effect g) ((G₂ p.1).effect g'))
  have hw p g g' : 0 ≤ w p g g' := stateQForm_nonneg ψ
    (kronecker_nonneg ((opposite p.1).pos g) ((G₂ p.1).pos g'))
  have havg := avgOver_collision_le D eval₂ w η hD hη hw (fun p =>
    (sum_offDiag_le_total _ (hw p)).trans_eq (by rw [sum_tensor_effect_stateQForm, hψ, one_pow])) hcoll
  rw [consistencyDefect_placed_eq_one_sub_overlap D (fun q => opposite q.1.1)
    (fun q => G₂ q.1.1) ψ hD hψ,
    consistencyDefect_placed_eq_one_sub_overlap D (fun q => (opposite q.1.1).postprocess (f q))
    (fun q => (G₂ q.1.1).postprocess (f q)) ψ hD hψ]
  suffices (avgOver D (fun q => ∑ r, stateQForm ψ (heteroKron
      (((opposite q.1.1).postprocess (f q)).effect r)
      (((G₂ q.1.1).postprocess (f q)).effect r)))) -
      avgOver D (fun q => ∑ g, w q.1 g g) ≤ η by linarith
  rw [← avgOver_sub]
  refine (avgOver_congr D _ _ fun q => ?_).le.trans havg
  rw [diagonal_postprocess_stateQForm_eq_pair_sum]
  exact sum_colliding_sub_diagonal (f q) (w q.1)

section Pinch

variable {R Γ ι : Type*} [Fintype R] [Fintype Γ] [Fintype ι] [DecidableEq ι]

/-- Sum of congruences by the effects of a single measurement. -/
noncomputable def pinchOp (P : Measurement R ι) (T : Op ι) : Op ι :=
  ∑ a, P.effect a * T * P.effect a

theorem pinchOp_sum {Y : Type*} (P : Measurement R ι) (s : Finset Y) (T : Y → Op ι) :
    pinchOp P (∑ y ∈ s, T y) = ∑ y ∈ s, pinchOp P (T y) := by
  simp only [pinchOp, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

section

variable (P : Measurement R ι)
include P

theorem pinchOp_nonneg {T : Op ι} (hT : 0 ≤ T) : 0 ≤ pinchOp P T :=
  Finset.sum_nonneg fun a _ => by
    simpa only [measurement_effect_hermitian] using
      (Matrix.nonneg_iff_posSemidef.mp hT).conjTranspose_mul_mul_same (P.effect a) |>.nonneg

theorem pinchOp_one_le : pinchOp P 1 ≤ 1 := by
  simpa only [pinchOp, mul_one, measurement_effect_hermitian] using
    measurement_sum_adjoint_mul_le_one P

theorem pinchOp_one_of_projective (hP : QPBT.Measurement.IsProjective P) :
    pinchOp P 1 = 1 := by
  simp only [pinchOp, mul_one, fun a => (hP a).isIdempotentElem.eq, P.sum_eq_one]

/-- The pinched overlap kernel remains nonnegative and has mass at most one. -/
private theorem pinched_pair_mass (G H : Measurement Γ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1) :
    (∑ g, ∑ g', stateQForm ψ (heteroKron (H.effect g) (pinchOp P (G.effect g')))) ≤ 1 := by
  simp_rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right,
    ← pinchOp_sum, G.sum_eq_one, ← heteroKron_finset_sum_left, H.sum_eq_one]
  calc
    _ ≤ stateQForm ψ (1 : Op (ι × ι)) := quadratic_form_mono (by
      change rightTensor (ι₁ := ι) (pinchOp P 1) ≤ 1
      rw [← rightTensor_one]
      exact rightTensor_mono (pinchOp_one_le P)) ψ
    _ = 1 := by rw [stateQForm_one, hψ, one_pow]

end

end Pinch

/-- The collision bound also controls a pinched overlap, since its weights have mass at most one. -/
theorem avgOver_pinched_collision_le_distinct_families
    {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [DecidableEq R₂]
    [Fintype R₁] [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → Measurement Γ₂ ι) (P : X × Y₁ → Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : HasConditionalCollisionBound D eval₂ η) :
    avgOver D (fun q => ∑ g, ∑ g', if g = g' then 0 else
      if eval₂ g q.2 = eval₂ g' q.2 then stateQForm ψ
        (heteroKron ((opposite q.1.1).effect g) (pinchOp (P q.1) ((G₂ q.1.1).effect g')))
      else 0) ≤ η := by
  classical
  let w (p : X × Y₁) g g' := stateQForm ψ
    (heteroKron ((opposite p.1).effect g) (pinchOp (P p) ((G₂ p.1).effect g')))
  have hw p g g' : 0 ≤ w p g g' := stateQForm_nonneg _
    (kronecker_nonneg ((opposite p.1).pos g) (pinchOp_nonneg _ ((G₂ p.1).pos g')))
  exact avgOver_collision_le D eval₂ w η hD hη hw (fun p =>
    (sum_offDiag_le_total _ (hw p)).trans (pinched_pair_mass _ _ _ ψ hψ)) hcoll

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
    bipartiteDefect D
      (fun question => schmidtMirrorMeasurement ψ (B question))
      B ψ ≤
    2 * bipartiteDefect D
      A
      B ψ := by
  classical
  unfold bipartiteDefect consistencyDefect
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
    have hm : (schmidtMirrorMeasurement ψ (B question)).effect answer =
        schmidtMirror ψ ((B question).effect answer) := rfl
    rw [hm]
    simpa only [applyOperatorToState, map_sub, LinearMap.sub_apply] using
      schmidtMirror_norm_sq_le ψ ((A question).effect answer) ((B question).effect answer)
        (measurement_effect_hermitian _ _) (measurement_effect_hermitian _ _)
  simp only [Measurement.leftPlacement_effect, Measurement.rightPlacement_effect]
    at hmirror hpredict
  linarith

end MIPStarRE.QPBT
