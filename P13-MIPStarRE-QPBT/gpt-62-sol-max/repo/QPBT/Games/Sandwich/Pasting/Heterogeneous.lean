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

private theorem pastedPOVM_rightPlacement {Γ₁ Γ₂ I J : Type*}
    [Fintype Γ₁] [Fintype Γ₂] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (G₁ : Measurement Γ₁ J) (G₂ : Measurement Γ₂ J) (hG₂ : QPBT.Measurement.IsProjective G₂) :
    pastedPOVM (Measurement.rightPlacement (ιA := I) G₁) (Measurement.rightPlacement G₂)
      (Measurement.isProjective_rightPlacement _ hG₂) =
        Measurement.rightPlacement (pastedPOVM G₁ G₂ hG₂) := by
  apply Quantum.Measurement.ext
  intro a
  simp only [pastedPOVM, Measurement.ofSumEqOne, Measurement.rightPlacement_effect,
    pastedMeasurement, heteroKron_mul, one_mul]

namespace Pasting

variable {ιA ιB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

section

variable (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
include a₀ b₀ ψ

/-- Adjoin a fixed basis vector to each local register. Alice's original
coordinate is first and Bob's original coordinate is last. This is the
common-carrier realization used for the heterogeneous pasting estimate;
blueprint `def:pasting-product-state`. -/
noncomputable def productPaddedState :
    EuclideanSpace ℂ ((ιA × ιB) × (ιA × ιB)) :=
  WithLp.toLp 2 (fun p => if p.1.2 = b₀ then
    if p.2.1 = a₀ then ψ (p.1.1, p.2.2) else 0 else 0)

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
  apply congrArg Complex.re
  simp [productPaddedState, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
    heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, apply_ite]

end

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
  simp_rw [heteroKron_mul, mul_one, one_mul,
    stateQForm_productPaddedState]

end Pasting

/-- The fixed heterogeneous pasting error used by the current QPBT proof. -/
noncomputable def heterogeneousPastingError (η δ : ℝ) : ℝ :=
  115 * (η ^ (1 / 4 : ℝ) + δ ^ (1 / 8 : ℝ))

/-- A stronger homogeneous auxiliary for paper `lem:pasting`: the two forward
marginal comparisons already imply the pasted conclusion. The paper-facing
`exists_pasting_error` retains the printed self-consistency hypothesis.
This auxiliary isolates its existing Schmidt-mirror proof, which does not use
that hypothesis. See issue Dengnifer/MIPStarRE-QPBT-bak#495 and paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`;
blueprint `lem:pasting-forward-comparisons`.

**Local fix:** the additive interpretation of `IsPolyErr₂` is documented in
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. -/
private theorem pasting_error_of_marginal_consistency_explicit
    {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ι) (G₂ : X → Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η δ : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hG₂ : ∀ x, QPBT.Measurement.IsProjective (G₂ x))
    (hA : ∀ q, QPBT.Measurement.IsProjective (A q))
    (hcoll : HasConditionalCollisionBound D eval₂ η)
    (h₁ : bipartiteDefect D (fun q => (A q).postprocess Prod.fst)
      (fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)) ψ ≤ δ)
    (h₂ : bipartiteDefect D (fun q => (A q).postprocess Prod.snd)
      (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ ≤ δ) :
    bipartiteDefect D A (pastedEvaluation eval₁ eval₂ G₁ G₂ hG₂) ψ ≤
      heterogeneousPastingError η δ := by
  by_cases h : δ ≤ 1 ∧ η ≤ 1
  · exact (consistencyDefect_pasted_le_sqrt_one_sided D eval₁ eval₂ G₁ G₂ A ψ
      η δ hD hψ hη hG₂ hA hcoll h₁ h₂).trans (pasting_error_sqrt_le_rpow δ η hδ h.1 hη h.2)
  refine (consistencyDefect_placed_le_one D A _ ψ hD hψ).trans ?_
  unfold heterogeneousPastingError
  simp only [not_and_or, not_le] at h
  rcases h with h | h
  · nlinarith [Real.one_le_rpow h.le (by norm_num : (0 : ℝ) ≤ 1 / 8),
      Real.rpow_nonneg hη (1 / 4)]
  · nlinarith [Real.one_le_rpow h.le (by norm_num : (0 : ℝ) ≤ 1 / 4),
      Real.rpow_nonneg hδ (1 / 8)]

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
theorem pasting_error_heterogeneous_explicit
    {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → Measurement Γ₁ ιB) (G₂ : X → Measurement Γ₂ ιB)
    (A : ((X × Y₁) × Y₂) → Measurement (R₁ × R₂) ιA)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (η δ : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hG₂ : ∀ x, QPBT.Measurement.IsProjective (G₂ x))
    (hA : ∀ q, QPBT.Measurement.IsProjective (A q))
    (hcoll : HasConditionalCollisionBound D eval₂ η)
    (h₁ : bipartiteDefect D (fun q => (A q).postprocess Prod.fst)
      (fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2)) ψ ≤ δ)
    (h₂ : bipartiteDefect D (fun q => (A q).postprocess Prod.snd)
      (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ ≤ δ) :
    bipartiteDefect D A (pastedEvaluation eval₁ eval₂ G₁ G₂ hG₂) ψ ≤
      heterogeneousPastingError η δ := by
  classical
  have hnonempty : Nonempty (ιA × ιB) := by
    rcases isEmpty_or_nonempty (ιA × ιB) with h | h
    · letI := h
      have hz : ψ = 0 := Subsingleton.elim _ _
      simp [hz] at hψ
    · exact h
  obtain ⟨⟨a₀, b₀⟩⟩ := hnonempty
  let A' := fun q => Measurement.leftPlacement (ιB := ιB) (A q)
  let G₁' := fun x => Measurement.rightPlacement (ιA := ιA) (G₁ x)
  let G₂' := fun x => Measurement.rightPlacement (ιA := ιA) (G₂ x)
  let ψ' := Pasting.productPaddedState a₀ b₀ ψ
  have hψ' := (Pasting.productPaddedState_norm a₀ b₀ ψ).trans hψ
  have h₁' : bipartiteDefect D
      (fun q => (A' q).postprocess Prod.fst)
      (fun q => (G₁' q.1.1).postprocess
        (fun g => eval₁ g q.1.2)) ψ' ≤ δ := by
    simpa only [bipartiteDefect, A', G₁', ψ', ← Measurement.leftPlacement_postprocess,
      ← Measurement.rightPlacement_postprocess, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, Pasting.consistencyDefect_productPaddedState] using h₁
  have h₂' : bipartiteDefect D
      (fun q => (A' q).postprocess Prod.snd)
      (fun q => (G₂' q.1.1).postprocess
        (fun g => eval₂ g q.2)) ψ' ≤ δ := by
    simpa only [bipartiteDefect, A', G₂', ψ', ← Measurement.leftPlacement_postprocess,
      ← Measurement.rightPlacement_postprocess, Measurement.leftPlacement_effect,
      Measurement.rightPlacement_effect, Pasting.consistencyDefect_productPaddedState] using h₂
  let hG₂' x := Measurement.isProjective_rightPlacement (ιA := ιA) (G₂ x) (hG₂ x)
  have hE x : pastedPOVM (G₁' x) (G₂' x) (hG₂' x) =
      Measurement.rightPlacement (pastedPOVM (G₁ x) (G₂ x) (hG₂ x)) :=
    pastedPOVM_rightPlacement _ _ _
  have hpadded := pasting_error_of_marginal_consistency_explicit
    D eval₁ eval₂ G₁' G₂' A' ψ' η δ hD hψ' hη hδ
    hG₂' (fun q => Measurement.isProjective_leftPlacement (A q) (hA q)) hcoll h₁' h₂'
  simpa only [bipartiteDefect, A', ψ', pastedEvaluation, hE, ← Measurement.rightPlacement_postprocess,
    Measurement.leftPlacement_effect, Measurement.rightPlacement_effect,
    Pasting.consistencyDefect_productPaddedState] using hpadded

/-- The fixed heterogeneous pasting error is polynomial in its two inputs. -/
theorem heterogeneous_pasting_error_is_poly_err₂ : IsPolyErr₂ heterogeneousPastingError := by
  exact ⟨115, 1 / 4, 1 / 8, by norm_num, by norm_num, by norm_num,
    fun η δ hη hδ =>
      ⟨mul_nonneg (by norm_num)
        (add_nonneg (Real.rpow_nonneg hη _) (Real.rpow_nonneg hδ _)), le_rfl⟩⟩

end MIPStarRE.QPBT
