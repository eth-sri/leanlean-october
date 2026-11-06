module

public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.ErrorFunctions

/-! # Pasting on independent local spaces

The two local spaces are realized in a common product space by adjoining fixed
basis vectors. Tensor placement supplies the corresponding
measurements, with projectivity and postprocessing preserved.

## References

Paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, and its use in
`lem:qld-xz-lines`, `14_analysis_of_the_pauli_basis_test.tex:882-963`.
The common-space realization is a formalization-only auxiliary; see issue
Dengnifer/MIPStarRE-QPBT-bak#495.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open DistanceCalculus

/-- The effects obtained by sandwiching one measurement with a projective
measurement form a POVM. This is `lem:pasting-measurement`, the measurement
assertion for `eq:pasting-2a`; blueprint `lem:pasting-measurement`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:514-524`. -/
theorem pastedMeasurement_isMeasurement {Γ₁ Γ₂ ι : Type*}
    [Fintype Γ₁] [Fintype Γ₂] [Fintype ι] [DecidableEq ι]
    (G₁ : Measurement Γ₁ ι) (G₂ : Measurement Γ₂ ι)
    (hG₂ : MIPStarRE.QPBT.Measurement.IsProjective G₂) :
    (∀ g : Γ₁ × Γ₂,
      0 ≤ pastedMeasurement G₁.effect G₂.effect g.1 g.2) ∧
      (∑ g : Γ₁ × Γ₂,
        pastedMeasurement G₁.effect G₂.effect g.1 g.2) = 1 := by
  constructor
  · intro g
    unfold pastedMeasurement
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hpos : ((G₂.effect g.2)ᴴ * G₁.effect g.1 * G₂.effect g.2).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp (G₁.pos g.1)).conjTranspose_mul_mul_same
        (G₂.effect g.2)
    simp_all [MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
  · classical
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ g₂ : Γ₂, ∑ g₁ : Γ₁,
          G₂.effect g₂ * G₁.effect g₁ * G₂.effect g₂) =
          ∑ g₂ : Γ₂,
            G₂.effect g₂ * (∑ g₁ : Γ₁, G₁.effect g₁) * G₂.effect g₂ := by
        simp [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ g₂ : Γ₂, G₂.effect g₂ := by
        apply Finset.sum_congr rfl
        intro g₂ _
        rw [G₁.sum_eq_one, mul_one, (hG₂ g₂).isIdempotentElem.eq]
      _ = 1 := G₂.sum_eq_one

namespace Pasting

variable {ιA ιB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Adjoin a fixed basis vector to each local register. Alice's original
coordinate is first and Bob's original coordinate is last. This is the
common-carrier realization used for the heterogeneous pasting estimate;
blueprint `def:pasting-product-state`. -/
noncomputable def productPaddedState (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    EuclideanSpace ℂ ((ιA × ιB) × (ιA × ιB)) :=
  WithLp.toLp 2 (fun p => if p.1.2 = b₀ then
    if p.2.1 = a₀ then ψ (p.1.1, p.2.2) else 0 else 0)

variable (a₀ : ιA) (b₀ : ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- Adjoining unit basis vectors preserves the state norm. Formalization-only
auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem productPaddedState_norm :
    ‖productPaddedState a₀ b₀ ψ‖ = ‖ψ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, productPaddedState, Fintype.sum_prod_type, apply_ite]

/-- Local tensor padding preserves every bipartite quadratic form. This exact
identity is independent of positivity and of normalization of the state.
Formalization-only auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem stateQForm_productPaddedState (A : Op ιA) (B : Op ιB) :
    stateQForm (productPaddedState a₀ b₀ ψ)
        (heteroKron (heteroKron A (1 : Op ιB)) (heteroKron (1 : Op ιA) B)) =
      stateQForm ψ (heteroKron A B) := by
  unfold stateQForm applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp [productPaddedState, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
    heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, apply_ite]

/-- Tensor padding preserves the off-diagonal consistency defect for arbitrary
operator families. No measurement or probability assumption is required.
Formalization-only auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem consistencyDefect_productPaddedState {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (D : Distribution X) (A : X → α → Op ιA) (B : X → α → Op ιB)
    (a₀ : ιA) (b₀ : ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect D
        (fun x a => heteroKron (heteroKron (A x a) (1 : Op ιB)) (1 : Op (ιA × ιB)))
        (fun x a => heteroKron (1 : Op (ιA × ιB)) (heteroKron (1 : Op ιA) (B x a)))
        (productPaddedState a₀ b₀ ψ) =
      consistencyDefect D (fun x a => heteroKron (A x a) (1 : Op ιB))
        (fun x a => heteroKron (1 : Op ιA) (B x a)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm, heteroKron_mul, mul_one, one_mul,
    stateQForm_productPaddedState]

end Pasting

/-- The one-sided pasting estimate on independent Alice and Bob spaces.
This is a stronger formalization-only auxiliary for paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`: only its two
forward marginal comparisons are required. The paper-facing
`exists_pasting_error` continues to retain all three printed hypotheses.

The two spaces embed isometrically into a common product carrier by adjoining
fixed unit basis vectors. Tensor placement preserves the measurements and their
projectivity; `Pasting.consistencyDefect_productPaddedState` preserves the input
and output defects. The unit state internally excludes empty local carriers;
no nonemptiness assumption on outcomes is needed. See issue Dengnifer/MIPStarRE-QPBT-bak#495 and
blueprint
`lem:pasting-heterogeneous`.

**Local fix:** the additive interpretation of `IsPolyErr₂` is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. -/
theorem pasting_error_heterogeneous_explicit :
    ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂]
        [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
        [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
        (D : Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → Measurement Γ₁ ιB) (G₂ : X → Measurement Γ₂ ιB)
        (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ιA)
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (η δ : ℝ),
        D.IsProbability → ‖ψ‖ = 1 → 0 ≤ η → 0 ≤ δ →
        (∀ x, MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) →
        (∀ q, MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        HasConditionalCollisionBound D eval₂ η →
        consistencyDefect D
          (fun q a₁ => heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        consistencyDefect D
          (fun q a₂ => heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        consistencyDefect D (fun q a => heteroKron ((A q).effect a) 1)
          (fun q a => heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
          115 * (η ^ (1 / 4 : ℝ) + δ ^ (1 / 8 : ℝ)) := by
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ η δ hD hψ hη hδ hG₂ hA hcoll h₁ h₂
  obtain ⟨⟨a₀, b₀⟩⟩ : Nonempty (ιA × ιB) :=
    not_isEmpty_iff.1 fun _ => by simp [Subsingleton.elim ψ 0] at hψ
  let A' := fun q => Measurement.leftPlacement (ιB := ιB) (A q)
  let G₁' := fun x => Measurement.rightPlacement (ιA := ιA) (G₁ x)
  let G₂' := fun x => Measurement.rightPlacement (ιA := ιA) (G₂ x)
  let ψ' := Pasting.productPaddedState a₀ b₀ ψ
  have hψ' : ‖ψ'‖ = 1 := (Pasting.productPaddedState_norm a₀ b₀ ψ).trans hψ
  have h₁' : consistencyDefect D
      (fun q a₁ => heteroKron (((A' q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => heteroKron 1 (((G₁' q.1.1).postprocess
        (fun g => eval₁ g q.1.2)).effect a₁)) ψ' ≤ δ := by
    simpa only [A', G₁', ψ', ← Measurement.leftPlacement_postprocess,
      ← Measurement.rightPlacement_postprocess, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, Pasting.consistencyDefect_productPaddedState] using h₁
  have h₂' : consistencyDefect D
      (fun q a₂ => heteroKron (((A' q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => heteroKron 1 (((G₂' q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ' ≤ δ := by
    simpa only [A', G₂', ψ', ← Measurement.leftPlacement_postprocess,
      ← Measurement.rightPlacement_postprocess, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, Pasting.consistencyDefect_productPaddedState] using h₂
  have hpaste (q : (X × Y₁) × Y₂) (a : R₁ × R₂) :
      (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
        if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
          pastedMeasurement (fun g => (G₁' q.1.1).effect g)
            (fun g => (G₂' q.1.1).effect g) g₁ g₂ else 0) =
        heteroKron (1 : Op ιA) (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) := by
    simp only [G₁', G₂', Measurement.rightPlacement_effect, pastedMeasurement,
      heteroKron_mul, one_mul]
    simp_rw [heteroKron_finset_sum_right]
    apply Finset.sum_congr rfl
    intro g₁ _
    apply Finset.sum_congr rfl
    intro g₂ _
    split_ifs <;> simp [heteroKron, Matrix.kronecker]
  rw [← Pasting.consistencyDefect_productPaddedState D _ _ a₀ b₀ ψ]
  simp_rw [← hpaste]
  change consistencyDefect D (fun q a => heteroKron ((A' q).effect a) 1) _ ψ' ≤ _
  have hG₂' := fun x : X =>
    Measurement.isProjective_rightPlacement (ιA := ιA) (G₂ x) (hG₂ x)
  have hA' := fun q : (X × Y₁) × Y₂ =>
    Measurement.isProjective_leftPlacement (ιB := ιB) (A q) (hA q)
  have hpm : ∀ q : (X × Y₁) × Y₂,
      (∀ g : Γ₁ × Γ₂, 0 ≤ pastedMeasurement (fun g => (G₁' q.1.1).effect g)
          (fun g => (G₂' q.1.1).effect g) g.1 g.2) ∧
        (∑ g : Γ₁ × Γ₂, pastedMeasurement (fun g => (G₁' q.1.1).effect g)
          (fun g => (G₂' q.1.1).effect g) g.1 g.2) = 1 :=
    fun q => pastedMeasurement_isMeasurement (G₁' q.1.1) (G₂' q.1.1) (hG₂' q.1.1)
  set Bp : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) (ιA × ιB) := fun q =>
    (Measurement.ofSumEqOne
      (fun g : Γ₁ × Γ₂ => pastedMeasurement (fun g => (G₁' q.1.1).effect g)
        (fun g => (G₂' q.1.1).effect g) g.1 g.2) (hpm q).1 (hpm q).2).postprocess
      (fun g => (eval₁ g.1 q.1.2, eval₂ g.2 q.2)) with hBpdef
  have hle1 := consistencyDefect_placed_le_one D A' Bp ψ' hD hψ'
  have hfam : (fun (q : (X × Y₁) × Y₂) (a : R₁ × R₂) =>
        heteroKron (1 : Op (ιA × ιB)) ((Bp q).effect a)) =
      fun (q : (X × Y₁) × Y₂) (a : R₁ × R₂) => heteroKron (1 : Op (ιA × ιB))
        (∑ g₁ : Γ₁, ∑ g₂ : Γ₂, if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
          pastedMeasurement (fun g => (G₁' q.1.1).effect g)
            (fun g => (G₂' q.1.1).effect g) g₁ g₂ else 0) := by
    funext q a
    rw [hBpdef]
    simp only [Measurement.postprocess_effect, Measurement.ofSumEqOne]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hfam] at hle1
  rcases le_or_gt δ 1 with hδ1 | hδgt
  · rcases le_or_gt η 1 with hη1 | hηgt
    · let opposite := fun x => schmidtMirrorMeasurement ψ' (G₂' x)
      have hQ := fun q : (X × Y₁) × Y₂ =>
        SandwichProduct.postprocess_isProjective (G₂' q.1.1) (hG₂' q.1.1) fun g => eval₂ g q.2
      have hεc : consistencyDefect D
          (fun q a => heteroKron (((opposite q.1.1).postprocess fun g => eval₂ g q.2).effect a) 1)
          (fun q a => heteroKron 1 (((G₂' q.1.1).postprocess fun g => eval₂ g q.2).effect a)) ψ' ≤
          δ + 2 * √(2 * δ) := by
        have := consistencyDefect_schmidtMirror_le D (fun q => (A' q).postprocess Prod.snd) _ ψ' hQ
        simp only [schmidtMirrorMeasurement, Measurement.ofSumEqOne] at this
        simp only [opposite, schmidtMirrorMeasurement_postprocess]
        nlinarith [Real.sq_sqrt (show 0 ≤ 2 * δ by positivity), Real.sqrt_nonneg (2 * δ)]
      have hεf : consistencyDefect D (fun q g => heteroKron ((opposite q.1.1).effect g) 1)
          (fun q g => heteroKron 1 ((G₂' q.1.1).effect g)) ψ' ≤ δ + 2 * √(2 * δ) + η := by
        refine le_trans ?_ (add_le_add_left hεc η)
        have hcnn : ∀ x g g', 0 ≤ stateQForm ψ' (heteroKron ((opposite x).effect g) ((G₂' x).effect g')) :=
          fun x g g' => stateQForm_nonneg ψ' (kronecker_nonneg ((opposite x).pos g) ((G₂' x).pos g'))
        have hall : ∀ x, ∑ g, ∑ g', stateQForm ψ'
            (heteroKron ((opposite x).effect g) ((G₂' x).effect g')) = 1 := fun x => by
          simp [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, ← heteroKron_finset_sum_left,
            Measurement.sum_eq_one, heteroKron_one_one, stateQForm_one, hψ']
        have havg := avgOver_collision_le D eval₂ (fun p g g' => stateQForm ψ'
          (heteroKron ((opposite p.1).effect g) ((G₂' p.1).effect g'))) η hD hη
          (fun p g g' => hcnn p.1 g g') (fun p => (hall p.1).le) hcoll
        rw [consistencyDefect_placed_eq_one_sub D _ _ ψ' hψ' fun q => (G₂' q.1.1).sum_eq_one,
          consistencyDefect_placed_eq_one_sub D _ _ ψ' hψ' fun q => Measurement.sum_eq_one _]
        refine (le_of_eq ?_).trans (add_le_add_right havg _)
        rw [← avgOver_add]
        refine avgOver_congr D _ _ fun q => ?_
        rw [SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum]
        have : ∀ g g', (if eval₂ g q.2 = eval₂ g' q.2 then stateQForm ψ'
            (heteroKron ((opposite q.1.1).effect g) ((G₂' q.1.1).effect g')) else 0) =
            (if g = g' then stateQForm ψ' (heteroKron ((opposite q.1.1).effect g) ((G₂' q.1.1).effect g'))
              else 0) + (if g = g' then 0 else if eval₂ g q.2 = eval₂ g' q.2 then stateQForm ψ'
                (heteroKron ((opposite q.1.1).effect g) ((G₂' q.1.1).effect g')) else 0) := by
          intro g g'
          split_ifs <;> simp_all
        rw [Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => this g g']
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
      have hglf := (opFamilyDistSq_symm ..).trans_le <|
        opFamilyDistSq_placed_le_of_consistencyDefect_le D (fun q => opposite q.1.1) _ ψ' hεf
      have hglc := (opFamilyDistSq_symm ..).trans_le <|
        opFamilyDistSq_placed_le_of_consistencyDefect_le D _ _ ψ' hεc
      have hAc := fun q => SandwichProduct.postprocess_isProjective (A' q) (hA' q) Prod.fst
      have hd := opFamilyDistSq_placed_le_of_consistencyDefect_le D _ _ ψ' h₁'
      have hK₀ : opFamilyDistSq D (fun q (a : R₁ × R₂) => heteroKron 1
          (((G₁' q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1 *
              ((G₂' q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 -
            ((G₂' q.1.1).postprocess (fun g => eval₂ g q.2)).effect a.2 *
              ((G₁' q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect a.1))
          (fun _ _ => 0) ψ' ≤ 32 * δ := by
        have key := opFamilyDistSq_commutator_le_of_close D (α := Unit)
          (fun q p => heteroKron 1 (((G₁' q.1.1).postprocess (fun g => eval₁ g q.1.2)).effect p.2))
          (fun q p => heteroKron (((A' q).postprocess Prod.fst).effect p.2) 1)
          (fun q p => heteroKron 1 (((G₂' q.1.1).postprocess (fun g => eval₂ g q.2)).effect p.2))
          (fun q p => heteroKron (((A' q).postprocess Prod.snd).effect p.2) 1) ψ' (2 * δ)
          (fun q _ => placed_right_contraction _) (fun q _ => placed_right_contraction _)
          (fun q _ => placed_left_contraction _) (fun q _ => placed_left_contraction _)
          (fun q abc => by simp [heteroKron_mul]) (fun q abc => by simp [heteroKron_mul])
          (fun q abc => by rw [heteroKron_mul, heteroKron_mul,
            (postprocess_effect_commute (A' q) (hA' q) _ _ _ _).eq]) ?_ ?_
        · rw [opFamilyDistSq_reindex D (Equiv.prodCongr (Equiv.uniqueProd R₁ Unit).symm (Equiv.refl R₂))]
          refine le_of_eq_of_le (opFamilyDistSq_congr_sub D _ _ _ _ ψ' fun q abc => ?_) (key.trans_eq (by ring))
          simp [heteroKron_mul, heteroKron_sub_right]
        all_goals rw [opFamilyDistSq_symm, opFamilyDistSq_reindex D (Equiv.uniqueProd _ Unit)]
        · exact opFamilyDistSq_placed_le_of_consistencyDefect_le D _ _ ψ' h₁'
        · exact opFamilyDistSq_placed_le_of_consistencyDefect_le D _ _ ψ' h₂'
      have hm := mass_ordered_product_ge D _ _ _ ψ' _ _ hD hψ' hAc hQ hd hK₀
      have hf : avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂, ‖applyOperatorToState
          (heteroKron 1 (((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect a * (G₂' q.1.1).effect g -
            (G₂' q.1.1).effect g * ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect a)) ψ'‖ ^ 2) ≤
          32 * δ + (2 * √(2 * δ) + 2 * δ + 2 * √(32 * δ) + 32 * δ) + 2 * η +
            2 * √(2 * ((δ + 2 * √(2 * δ)) + η)) + 2 * √(2 * (δ + 2 * √(2 * δ))) := by
        refine (avgOver_mono D _ (fun q => (∑ ab : R₁ × R₂, ‖applyOperatorToState (heteroKron 1
            (((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect ab.1 * ((G₂' q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 -
              ((G₂' q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2 * ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect ab.1) - 0) ψ'‖ ^ 2) +
            (1 - ∑ ab : R₁ × R₂, ‖applyOperatorToState (heteroKron 1 (((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect ab.1 *
              ((G₂' q.1.1).postprocess (fun g => eval₂ g q.2)).effect ab.2)) ψ'‖ ^ 2) +
            2 * (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else if eval₂ g q.2 = eval₂ g' q.2 then
              ∑ a : R₁, stateQForm ψ' (heteroKron ((opposite q.1.1).effect g')
                (((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect a * (G₂' q.1.1).effect g * ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).effect a)) else 0) +
            2 * √(∑ g : Γ₂, ‖applyOperatorToState (heteroKron 1 ((G₂' q.1.1).effect g) -
              heteroKron ((opposite q.1.1).effect g) 1) ψ'‖ ^ 2) +
            2 * √(∑ b : R₂, ‖applyOperatorToState (heteroKron 1 (((G₂' q.1.1).postprocess
              (fun g => eval₂ g q.2)).effect b) - heteroKron (((opposite q.1.1).postprocess
                (fun g => eval₂ g q.2)).effect b) 1) ψ'‖ ^ 2)) fun q => ?_).trans ?_
        · have hQ := SandwichProduct.postprocess_isProjective (G₂' q.1.1) (hG₂' q.1.1) fun g => eval₂ g q.2
          have := abs_le.mp (abs_cross_move_gap_le_sqrt_distinct_families ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2) (G₂' q.1.1)
            (opposite q.1.1) ψ' hψ')
          have := abs_le.mp (abs_cross_move_gap_le_sqrt_distinct_families ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2)
            ((G₂' q.1.1).postprocess fun g => eval₂ g q.2) ((opposite q.1.1).postprocess fun g => eval₂ g q.2) ψ' hψ')
          have := pinched_coarse_sub_fine_eq_distinct_families ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2) (G₂' q.1.1) (opposite q.1.1)
            (fun g => eval₂ g q.2) ψ'
          have := sum_norm_ordered_product_le_one ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2) (G₂' q.1.1) ψ' hψ'
          simp only [Fintype.sum_prod_type, sub_zero, commutator_mass_eq_expansion _ (G₂' q.1.1) ψ' (hG₂' q.1.1),
            commutator_mass_eq_expansion _ _ ψ' hQ]
          linarith
        simp only [avgOver_add, avgOver_sub, avgOver_const_mul, avgOver_const_of_isProbability D hD]
        gcongr ?_ + ?_ + 2 * ?_ + 2 * ?_ + 2 * ?_
        · exact hK₀
        · linarith
        · have hcnn : ∀ (p : X × Y₁) (g g' : Γ₂), 0 ≤ ∑ a, stateQForm ψ' (heteroKron
              ((opposite p.1).effect g') (((G₁' p.1).postprocess fun g => eval₁ g p.2).effect a * (G₂' p.1).effect g * ((G₁' p.1).postprocess fun g => eval₁ g p.2).effect a)) :=
            fun p g g' => Finset.sum_nonneg fun a _ => stateQForm_nonneg ψ' (kronecker_nonneg
              ((opposite p.1).pos g') (by simpa only [measurement_effect_hermitian] using
                ((Matrix.nonneg_iff_posSemidef.mp ((G₂' p.1).pos g)).conjTranspose_mul_mul_same
                  (((G₁' p.1).postprocess fun g => eval₁ g p.2).effect a)).nonneg))
          refine avgOver_collision_le D eval₂ (fun p g g' => ∑ a, stateQForm ψ' (heteroKron
              ((opposite p.1).effect g') (((G₁' p.1).postprocess fun g => eval₁ g p.2).effect a * (G₂' p.1).effect g * ((G₁' p.1).postprocess fun g => eval₁ g p.2).effect a)))
            η hD hη hcnn (fun p => ?_) hcoll
          have : stateQForm ψ' _ ≤ stateQForm ψ' 1 := quadratic_form_mono
            (measurement_sum_adjoint_mul_le_one (Measurement.rightPlacement (ιA := ιA × ιB) ((G₁' p.1).postprocess fun g => eval₁ g p.2))) ψ'
          simp only [← stateQForm_finset_sum, ← heteroKron_finset_sum_right,
            ← heteroKron_finset_sum_left, (opposite p.1).sum_eq_one]
          rw [Finset.sum_comm]
          simp only [← Finset.sum_mul, ← Finset.mul_sum, Measurement.sum_eq_one, mul_one]
          simp only [Measurement.rightPlacement, rightPlacedMeasurement, Measurement.ofSumEqOne, heteroKron_conjTranspose, heteroKron_mul] at this
          rw [Finset.sum_congr rfl fun b _ => by rw [measurement_effect_hermitian]] at this
          simpa [← heteroKron_finset_sum_right, stateQForm_one, hψ'] using this
        · exact avgOver_sqrt_le D hD hglf fun q => Finset.sum_nonneg fun g _ => sq_nonneg _
        · exact avgOver_sqrt_le D hD hglc fun q => Finset.sum_nonneg fun g _ => sq_nonneg _
      have h := avgOver_mono D _ _ fun q => (le_abs_self _).trans (abs_pinch_overlap_gap_le_sqrt
        ((A' q).postprocess Prod.fst) ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2) (G₂' q.1.1) ψ' hψ' (hAc q) (hG₂' q.1.1))
      have e1 := consistencyDefect_placed_eq_one_sub D (fun q => (A' q).postprocess Prod.fst) _ ψ' hψ'
        fun q => pinched_sum_eq_one (G₂' q.1.1) ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2) (hG₂' q.1.1)
      have e2 := consistencyDefect_placed_eq_one_sub D (fun q => (A' q).postprocess Prod.fst) _ ψ' hψ'
        fun q => ((G₁' q.1.1).postprocess fun g => eval₁ g q.1.2).sum_eq_one
      simp only [Finset.sum_sub_distrib, avgOver_sub] at h e1 e2
      linarith [avgOver_sqrt_le D hD hf fun q => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => sq_nonneg _,
        consistencyDefect_pasted_le_marginal_add_pinched D eval₁ eval₂ G₁' G₂' A' ψ' hψ' hG₂',
        pasting_error_sqrt_le_rpow 32 δ η (by norm_num) hδ hδ1 hη hη1]
    · nlinarith [Real.rpow_nonneg hδ (1 / 8 : ℝ),
        Real.one_le_rpow hηgt.le (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  · nlinarith [Real.rpow_nonneg hη (1 / 4 : ℝ),
      Real.one_le_rpow hδgt.le (by norm_num : (0 : ℝ) ≤ 1 / 8)]

/-- The fixed heterogeneous pasting error used by the current QPBT proof. -/
noncomputable def heterogeneousPastingError (η δ : ℝ) : ℝ :=
  115 * (η ^ (1 / 4 : ℝ) + δ ^ (1 / 8 : ℝ))

/-- The fixed heterogeneous pasting error is polynomial in its two inputs. -/
theorem heterogeneous_pasting_error_is_poly_err₂ : IsPolyErr₂ heterogeneousPastingError :=
  ⟨115, 1 / 4, 1 / 8, by norm_num, by norm_num, by norm_num,
    fun η δ hη hδ =>
      ⟨mul_nonneg (by norm_num)
        (add_nonneg (Real.rpow_nonneg hη _) (Real.rpow_nonneg hδ _)), le_rfl⟩⟩

end MIPStarRE.QPBT
