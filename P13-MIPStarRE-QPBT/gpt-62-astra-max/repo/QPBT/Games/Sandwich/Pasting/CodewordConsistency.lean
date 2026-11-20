module

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
open DistanceCalculus SandwichProduct

/-- The coarse one-sided commutator estimate of `lem:pasting`. The two
comparisons `eq:pasting-1` move the coarse codeword families of the two
generators onto the joint projective answer measurement placed on the opposite
factor, so the two coarse families approximately commute on the state, with one
universal constant. This is step 3 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem coarse_commutator_bound_explicit :
    ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
        [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
        (ψ : EuclideanSpace ℂ (ι × ι)) (δ : ℝ),
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        bipartiteDefect D
          (fun q => (A q).postprocess Prod.fst)
          (fun q => (G₁ q.1.1).postprocess
          (fun g => eval₁ g q.1.2)) ψ ≤ δ →
        bipartiteDefect D
          (fun q => (A q).postprocess Prod.snd)
          (fun q => (G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)) ψ ≤ δ →
        opFamilyDistSq D
          (fun q (a : R₁ × R₂) => heteroKron 1
            (((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1 *
                ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 -
              ((G₂ q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 *
                ((G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1))
          (fun _ _ => 0) ψ ≤ 32 * δ := by
  classical
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ δ hA h₁ h₂
  set P : ((X × Y₁) × Y₂) → Measurement R₁ ι :=
    fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2) with hPdef
  set Q : ((X × Y₁) × Y₂) → Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQdef
  let f₁ : R₁ ≃ _ :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let f₂ : R₂ ≃ _ :=
    ⟨fun a => ((), a), fun p => p.2, fun _ => rfl, by rintro ⟨⟨⟩, a⟩; rfl⟩
  let eB : ((Unit × R₁) × R₂) ≃ _ :=
    ⟨fun p => (p.1.2, p.2), fun a => (((), a.1), a.2),
      by rintro ⟨⟨⟨⟩, a⟩, b⟩; rfl, fun _ => rfl⟩
  let AR : _ → _ :=
    fun q => Measurement.congrAlphabet f₁.symm (P q)
  let DR : _ → _ :=
    fun q => Measurement.congrAlphabet f₂.symm (Q q)
  let BJ : _ → _ :=
    fun q => Measurement.congrAlphabet eB (A q)
  have hd₁ : opFamilyDistSq D
      (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 ((P q).effect a₁)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement ((A q).postprocess Prod.fst))
      (fun q => Measurement.rightPlacement (P q)) ψ) ?_
    simp only [Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect]
    linarith
  have hd₂ : opFamilyDistSq D
      (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 ((Q q).effect a₂)) ψ ≤ 2 * δ := by
    refine le_trans (opFamilyDistSq_le_two_mul_consistencyDefect D
      (fun q => Measurement.leftPlacement ((A q).postprocess Prod.snd))
      (fun q => Measurement.rightPlacement (Q q)) ψ) ?_
    simp only [Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect]
    linarith
  have hconc := op_dist_sq_commutator_right_le_explicit
    D AR BJ DR ψ _ (fun q => (fun b => (hA q) (eB b))) (by
      refine le_trans (le_of_eq ?_) hd₁
      rw [opFamilyDistSq_reindex D f₁
        (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => heteroKron 1 ((P q).effect a₁)) ψ]
      refine opFamilyDistSq_congr D _ _ _ _ ψ (fun q ab => ?_) (fun q ab => rfl)
      congr 1
      rw [Measurement.postprocess_congrAlphabet]
      simp only [Measurement.postprocess_effect]
      congr
      simp [eB, f₁, Prod.ext_iff]) (by
      refine le_trans (le_of_eq ?_) hd₂
      rw [opFamilyDistSq_reindex D f₂
        (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
        (fun q a₂ => heteroKron 1 ((Q q).effect a₂)) ψ]
      refine opFamilyDistSq_congr D _ _ _ _ ψ (fun q ac => ?_) (fun q ac => rfl)
      congr 1
      rw [Measurement.postprocess_congrAlphabet]
      simp only [Measurement.postprocess_effect]
      congr
      simp [eB, f₂, Prod.ext_iff])
  rw [opFamilyDistSq_reindex D eB _ _ ψ] at hconc
  refine le_trans (le_of_eq ?_) (le_trans hconc (le_of_eq (by ring)))
  rfl

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
    (hmass : ∀ p, (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else c p g g') ≤ 1)
    (hcoll : HasConditionalCollisionBound D eval₂ η) :
    avgOver D (fun q => collisionPart (fun g => eval₂ g q.2) (c q.1)) ≤ η := by
  have hk (p : X × Y₁) (g g' : Γ₂) (hne : g ≠ g') :
      (∑ y, D.weight (p, y) * if eval₂ g y = eval₂ g' y then 1 else 0) ≤ η * (D.map Prod.fst).weight p := by
    by_cases hp : 0 < (D.map Prod.fst).weight p
    · exact hcoll p.1 p.2 hp g g' hne
    · have hz := le_antisymm (not_lt.mp hp) ((D.map Prod.fst).nonnegative p)
      calc
        _ ≤ ∑ y, D.weight (p, y) := Finset.sum_le_sum fun y _ =>
          mul_le_of_le_one_right (D.nonnegative _) (by split <;> norm_num)
        _ = _ := by rw [← Distribution.map_fst_weight, hz, mul_zero]
  rw [avgOver_eq_sum_univ, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ p, η * (D.map Prod.fst).weight p := Finset.sum_le_sum fun p _ =>
      (weighted_collision_le _ _ _ (hc p) (hk p)).trans
        (mul_le_of_le_one_left (mul_nonneg hη ((D.map Prod.fst).nonnegative p)) (hmass p))
    _ = η := by rw [← Finset.mul_sum, (hD.map Prod.fst).weight_sum_univ_eq_one, mul_one]

/-- Fine/coarse collision control for independently chosen families on the two
registers. Positivity and completeness give probability weights, and the
conditional codeword collision bound controls their agreeing off-diagonal part.
This supplies the mirror-family version of step 4 in the one-sided proof,
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. -/
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
  have hc := avgOver_collision_le D eval₂
    (fun p g g' => stateQForm ψ (heteroKron ((opposite p.1).effect g) ((G₂ p.1).effect g'))) η hD hη
    (fun p g g' => stateQForm_nonneg _ (kronecker_nonneg ((opposite p.1).pos g) ((G₂ p.1).pos g')))
    (fun p => placed_offdiag_le_one _ _ hψ) hcoll
  simp only [bipartiteDefect_eq_one_sub ψ _ _ hD hψ, diagonalOverlap,
    diagonal_postprocess_stateQForm_eq_pair_sum, readout_agreement_eq, avgOver_add]
  linarith

/-- The pinched collision bound with an independent opposite-register family.
The opposite effects are used only as positive weights summing to the identity;
this permits the constructed Schmidt mirror without an identical-copy premise.
See the one-sided argument in `docs/paper-gaps/qpbt_pasting-product-error.tex`,
issue Dengnifer/MIPStarRE-QPBT-bak#201. -/
theorem avgOver_pinched_collision_le_distinct_families
    {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → Measurement Γ₂ ι) (P : (X × Y₁) → Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : HasConditionalCollisionBound D eval₂ η) :
    avgOver D (fun q => ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
      if eval₂ g q.2 = eval₂ g' q.2 then
        ∑ a : R₁, stateQForm ψ (heteroKron ((opposite q.1.1).effect g')
          ((P q.1).effect a * (G₂ q.1.1).effect g * (P q.1).effect a))
      else 0) ≤ η := by
  let w (p : X × Y₁) (g g' : Γ₂) := ∑ a, stateQForm ψ (heteroKron ((opposite p.1).effect g')
    ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))
  have hw p g g' : 0 ≤ w p g g' := Finset.sum_nonneg fun a _ => stateQForm_nonneg ψ
    (kronecker_nonneg ((opposite p.1).pos g') (effect_sandwich_nonneg (P p) a ((G₂ p.1).pos g)))
  refine avgOver_collision_le D eval₂ w η hD hη hw (fun p => ?_) hcoll
  calc
    _ ≤ ∑ g, ∑ g', w p g g' := Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun g' _ =>
      by split <;> first | exact hw _ _ _ | rfl
    _ = ∑ a, ‖applyOperatorToState ((Measurement.rightPlacement (ιA := ι) (P p)).effect a) ψ‖ ^ 2 := by
      dsimp only [w]
      conv_lhs => arg 2; intro g; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      congr 1 with a
      simp only [← stateQForm_finset_sum, ← heteroKron_finset_sum_left, (opposite p.1).sum_eq_one,
        ← heteroKron_finset_sum_right, ← Finset.sum_mul, ← Finset.mul_sum, (G₂ p.1).sum_eq_one,
        mul_one, norm_image_sq, Measurement.rightPlacement_effect, heteroKron_conjTranspose,
        Matrix.conjTranspose_one, measurement_effect_hermitian, heteroKron_mul]
    _ ≤ 1 := by simpa [hψ] using measurement_mass_le ψ (Measurement.rightPlacement (P p))

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
  simp only [bipartiteDefect, consistencyDefect]
  simp_rw [consistency_term_eq_stateQForm]
  rw [← avgOver_const_mul]
  refine avgOver_mono D _ _ fun question => ?_
  have hmirror := point_distance_eq_two_defect_of_projective
    _
    _ ψ
    (Measurement.isProjective_leftPlacement _
      (schmidtMirrorMeasurement_isProjective ψ _ (hB question)))
    (Measurement.isProjective_rightPlacement (hB question))
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
    gcongr
    simpa only [schmidtMirrorMeasurement, Measurement.ofSumEqOne,
      applyOperatorToState, map_sub, LinearMap.sub_apply] using
      schmidtMirror_norm_sq_le ψ ((A question).effect answer) ((B question).effect answer)
        (measurement_effect_hermitian _ _) (measurement_effect_hermitian _ _)
  simp
    at hmirror hpredict
  linarith

end MIPStarRE.QPBT
