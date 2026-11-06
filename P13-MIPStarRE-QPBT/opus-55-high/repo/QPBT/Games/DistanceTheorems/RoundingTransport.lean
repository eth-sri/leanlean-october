module

public import QPBT.Games.DistanceTheorems.ProjectiveRounding
public import QPBT.Games.DistanceTheorems.Calculus

/-!
# Projective rounding through outcome postprocessing

Consistent complete POVMs on two possibly different local spaces have projective
roundings on those same spaces. Their consistency with an opposite-player POVM
survives every question-dependent outcome map, with error
`δ + sqrt (220 * δ^(1/4)) + 2 * sqrt (δ + η)` when the original consistency errors
are at most `δ` and `η`. The estimate is independent of both local dimensions and
the number of outcomes.

These are formalization-only auxiliary results for the compression and rounding
argument preceding the polynomial-support argument in `lem:qld-4-7`. They do not
construct the global polynomial-pair measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`, `lem:ortho`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  in the proof of `lem:qld-4-7`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`,
  `fact:triangle-for-simeq` and `fact:data-processing`
- Issue Dengnifer/MIPStarRE-QPBT-bak#278
- `audits/2026-09-06_rounding_transport.md`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Formalization-only question-dependent form of `fact:data-processing`.
Applying the same outcome map to both players at each question cannot increase
their consistency defect. No normalization of the distribution or state is needed. -/
theorem consistencyDefect_postprocess_question_le {X α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA)
    (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (f : X → α → β) :
    consistencyDefect μ
        (fun x b => heteroKron (((A x).postprocess (f x)).effect b) 1)
        (fun x b => heteroKron 1 (((B x).postprocess (f x)).effect b)) ψ ≤
      consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ := by
  unfold consistencyDefect
  apply avgOver_mono
  intro x
  simpa only [consistencyDefect,
    avgOver_const_of_isProbability _ (uniformDistribution_isProbability Unit)] using
    consistencyDefect_postprocess_le (uniformDistribution Unit)
      (fun _ => A x) (fun _ => B x) ψ (f x)

theorem consistencyDefect_const_eq {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A B : α → Op ι) (ψ : EuclideanSpace ℂ ι) :
    consistencyDefect μ (fun _ => A) (fun _ => B) ψ =
      consistencyDefect (uniformDistribution Unit) (fun _ => A) (fun _ => B) ψ := by
  unfold consistencyDefect
  rw [avgOver_const_of_isProbability μ hμ,
    avgOver_const_of_isProbability _ (uniformDistribution_isProbability Unit)]

theorem consistencyDefect_placed_eq_one_sub_overlap {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ
        (heteroKron ((A x).effect a) ((B x).effect a))) := by
  simpa only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, placed_product_stateQForm_eq] using
    consistencyDefect_eq_one_sub_overlap μ
      (fun x => leftPlacedMeasurement (A x)) (fun x => rightPlacedMeasurement (B x))
      ψ hμ hψ

variable {ιA ιB α : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype α] [DecidableEq α] (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- The overlap estimate converts a same-space squared-distance bound into a
square-root loss in consistency with the unchanged opposite-player POVM. -/
theorem rounding_consistency_le (hψ : ‖ψ‖ = 1)
    (P A : Measurement α ιA) (B : Measurement α ιB) (δ r : ℝ)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (A.effect a) 1)
      (fun _ a => heteroKron 1 (B.effect a)) ψ ≤ δ)
    (hdist : opFamilyDistSq (uniformDistribution Unit)
      (fun _ a => heteroKron (P.effect a) 1)
      (fun _ a => heteroKron (A.effect a) 1) ψ ≤ r) :
    consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (P.effect a) 1)
      (fun _ a => heteroKron 1 (B.effect a)) ψ ≤ δ + Real.sqrt r := by
  letI : Nonempty (ιA × ιB) := by
    by_contra hι
    letI : IsEmpty (ιA × ιB) := not_nonempty_iff.mp hι
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  have hgap := overlap_gap_le_of_opFamilyDistSq (uniformDistribution Unit)
    (fun _ => rightPlacedMeasurement B) (fun _ => leftPlacedMeasurement A)
    (fun _ => leftPlacedMeasurement P) ψ (uniformDistribution_isProbability Unit)
    hψ r (by
      simpa only [leftPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne,
        opFamilyDistSq_symm] using hdist)
  rw [consistencyDefect_placed_eq_one_sub_overlap (uniformDistribution Unit)
    (fun _ => A) (fun _ => B)
    ψ (uniformDistribution_isProbability Unit) hψ] at hcons
  rw [consistencyDefect_placed_eq_one_sub_overlap (uniformDistribution Unit)
    (fun _ => P) (fun _ => B)
    ψ (uniformDistribution_isProbability Unit) hψ]
  simp only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] at hgap
  change |avgOver (uniformDistribution Unit) (fun _ => ∑ a,
      stateQForm ψ (rightTensor (B.effect a) * leftTensor (A.effect a))) -
    avgOver (uniformDistribution Unit) (fun _ => ∑ a,
      stateQForm ψ (rightTensor (B.effect a) * leftTensor (P.effect a)))| ≤ _ at hgap
  simp only [rightTensor_mul_leftTensor_eq_opTensor] at hgap
  dsimp only [opTensor, heteroKron] at hgap hcons ⊢
  have hdiff := (le_abs_self _).trans hgap
  linarith

/-- Formalization-only transport of the rounding supplied by `lem:ortho`.
The projective measurement is chosen before the question distribution, outcome
maps, comparison measurements, and comparison error. The unit-state and
probability hypotheses give total mass one; only `δ ≥ 0` is required of the
rounding error, and no upper range bound on either error is used. This supports
the compression step in `lem:qld-4-7`, not its global-witness conclusion. -/
theorem projective_rounding_preserves_postprocessed_consistency_left
    (hψ : ‖ψ‖ = 1)
    (A : Measurement α ιA) (B : Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (A.effect a) 1)
      (fun _ a => heteroKron 1 (B.effect a)) ψ ≤ δ) :
    ∃ P : Measurement α ιA, Measurement.IsProjective P ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : Distribution X), μ.IsProbability → ∀ (f : X → α → β)
        (N : X → Measurement β ιB) (η : ℝ),
        consistencyDefect μ
          (fun x b => heteroKron ((A.postprocess (f x)).effect b) 1)
          (fun x b => heteroKron 1 ((N x).effect b)) ψ ≤ η →
        consistencyDefect μ
          (fun x b => heteroKron ((P.postprocess (f x)).effect b) 1)
          (fun x b => heteroKron 1 ((N x).effect b)) ψ ≤
            δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
              2 * Real.sqrt (δ + η) := by
  obtain ⟨P, hP, hdist⟩ :=
    projective_rounding_with_explicit_constant ψ hψ A B δ hδ hcons
  refine ⟨P, hP, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hAN
  have hPB := rounding_consistency_le ψ hψ P A B δ _ hcons hdist
  have hABf : consistencyDefect μ
      (fun x b => heteroKron ((A.postprocess (f x)).effect b) 1)
      (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤ δ := by
    refine (consistencyDefect_postprocess_question_le μ
      (fun _ => A) (fun _ => B) ψ f).trans ?_
    rw [consistencyDefect_const_eq μ hμ]
    exact hcons
  have hPBf : consistencyDefect μ
      (fun x b => heteroKron ((P.postprocess (f x)).effect b) 1)
      (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
        δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) := by
    refine (consistencyDefect_postprocess_question_le μ
      (fun _ => P) (fun _ => B) ψ f).trans ?_
    rw [consistencyDefect_const_eq μ hμ]
    exact hPB
  simpa only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] using consistencyDefect_trans_le μ
    (fun x => leftPlacedMeasurement (P.postprocess (f x)))
    (fun x => rightPlacedMeasurement (B.postprocess (f x)))
    (fun x => leftPlacedMeasurement (A.postprocess (f x)))
    (fun x => rightPlacedMeasurement (N x)) ψ _ δ η hμ hψ hPBf hABf hAN

/-- Tensor-factor exchange intertwines the two Kronecker-product actions. -/
theorem applyOperatorToState_heteroKron_prodComm {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Op ιA) (B : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron B A) (reindexState (Equiv.prodComm ιA ιB) ψ) =
      reindexState (Equiv.prodComm ιA ιB) (applyOperatorToState (heteroKron A B) ψ) := by
  have hop : heteroKron B A =
      (heteroKron A B).submatrix (Equiv.prodComm ιB ιA) (Equiv.prodComm ιB ιA) := by
    ext i j
    exact mul_comm _ _
  apply (EuclideanSpace.equiv (ιB × ιA) ℂ).injective
  change heteroKron B A *ᵥ (ψ.ofLp ∘ (Equiv.prodComm ιB ιA)) =
    (heteroKron A B *ᵥ ψ.ofLp) ∘ (Equiv.prodComm ιB ιA)
  rw [hop, Matrix.submatrix_mulVec_equiv _ _ _ (Equiv.prodComm ιB ιA)]
  rfl

theorem stateQForm_heteroKron_prodComm {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    stateQForm (reindexState (Equiv.prodComm ιA ιB) ψ) (heteroKron B A) =
      stateQForm ψ (heteroKron A B) := by
  unfold stateQForm
  rw [applyOperatorToState_heteroKron_prodComm]
  exact congrArg Complex.re
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm ιA ιB)).inner_map_map
      ψ (applyOperatorToState (heteroKron A B) ψ))

/-- Formalization-only factor-exchange identity for `lem:ortho` and its
transport through postprocessing. The state is explicitly reindexed; neither
equal local spaces nor invariance of the state under exchange is assumed. -/
theorem consistencyDefect_prodComm {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → α → Op ιA) (B : X → α → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ (fun x a => heteroKron (B x a) 1)
        (fun x a => heteroKron 1 (A x a)) (reindexState (Equiv.prodComm ιA ιB) ψ) =
      consistencyDefect μ (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (B x a)) ψ := by
  unfold consistencyDefect
  simp_rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq,
    stateQForm_heteroKron_prodComm]
  apply avgOver_congr
  intro x
  rw [Finset.sum_comm]
  simp only [eq_comm]

/-- Formalization-only Bob-side form of projective rounding and consistency
transport for `lem:qld-4-7`. It follows by explicitly exchanging the tensor
factors and applying the Alice-side theorem to the exchanged state. The error
and normalization hypotheses are exactly those of the Alice-side form. -/
theorem projective_rounding_preserves_postprocessed_consistency_right
    (hψ : ‖ψ‖ = 1)
    (A : Measurement α ιA) (B : Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (A.effect a) 1)
      (fun _ a => heteroKron 1 (B.effect a)) ψ ≤ δ) :
    ∃ P : Measurement α ιB, Measurement.IsProjective P ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : Distribution X), μ.IsProbability → ∀ (f : X → α → β)
        (N : X → Measurement β ιA) (η : ℝ),
        consistencyDefect μ
          (fun x b => heteroKron ((N x).effect b) 1)
          (fun x b => heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤ η →
        consistencyDefect μ
          (fun x b => heteroKron ((N x).effect b) 1)
          (fun x b => heteroKron 1 ((P.postprocess (f x)).effect b)) ψ ≤
            δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
              2 * Real.sqrt (δ + η) := by
  have hψ' : ‖reindexState (Equiv.prodComm ιA ιB) ψ‖ = 1 := by
    rw [reindexState_norm_eq, hψ]
  have hcons' : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (B.effect a) 1)
      (fun _ a => heteroKron 1 (A.effect a))
      (reindexState (Equiv.prodComm ιA ιB) ψ) ≤ δ := by
    rwa [consistencyDefect_prodComm]
  obtain ⟨P, hP, htransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency_left
      (reindexState (Equiv.prodComm ιA ιB) ψ) hψ' B A δ hδ hcons'
  refine ⟨P, hP, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hNB
  have hNB' : consistencyDefect μ
      (fun x b => heteroKron ((B.postprocess (f x)).effect b) 1)
      (fun x b => heteroKron 1 ((N x).effect b))
      (reindexState (Equiv.prodComm ιA ιB) ψ) ≤ η := by
    rwa [consistencyDefect_prodComm]
  have hout := htransport μ hμ f N η hNB'
  rwa [consistencyDefect_prodComm] at hout

end

end MIPStarRE.QPBT
