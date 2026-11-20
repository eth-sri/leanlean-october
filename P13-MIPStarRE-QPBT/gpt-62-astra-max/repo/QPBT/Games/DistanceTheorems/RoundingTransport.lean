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

section

variable {X α β ι ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] [Fintype ιA] [DecidableEq ιA]
  [Fintype ιB] [DecidableEq ιB] (μ : Distribution X) (A : X → Measurement α ιA)
  (B : X → Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability)

/-- Formalization-only question-dependent form of `fact:data-processing`.
Applying the same outcome map to both players at each question cannot increase
their consistency defect. No normalization of the distribution or state is needed. -/
theorem consistencyDefect_postprocess_question_le
    (f : X → α → β) :
    bipartiteDefect μ
        (fun x => (A x).postprocess (f x))
        (fun x => (B x).postprocess (f x)) ψ ≤
      bipartiteDefect μ A
        B ψ := by
  simp only [bipartiteDefect, consistencyDefect]
  apply avgOver_mono
  intro x
  simpa only [consistencyDefect,
    avgOver_const_of_isProbability _ (uniformDistribution_isProbability Unit)] using
    consistencyDefect_postprocess_le (uniformDistribution Unit)
      (fun _ => A x) (fun _ => B x) ψ (f x)

include hμ in
private theorem consistencyDefect_const_eq
    (A B : α → Op ι) (ψ : EuclideanSpace ℂ ι) :
    consistencyDefect μ (fun _ => A) (fun _ => B) ψ =
      consistencyDefect (uniformDistribution Unit) (fun _ => A) (fun _ => B) ψ := by
  simp [consistencyDefect]
  rw [avgOver_const_of_isProbability μ hμ,
    avgOver_const_of_isProbability _ (uniformDistribution_isProbability Unit)]


end

variable {ιA ιB α : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype α] [DecidableEq α] (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
  (P A : Measurement α ιA) (B : Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ) (r : ℝ)

include hψ in
/-- The overlap estimate converts a same-space squared-distance bound into a
square-root loss in consistency with the unchanged opposite-player POVM. -/
private theorem rounding_consistency_le
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => A)
      (fun _ => B) ψ ≤ δ)
    (hdist : opFamilyDistSq (uniformDistribution Unit)
      (fun _ a => heteroKron (P.effect a) 1)
      (fun _ a => heteroKron (A.effect a) 1) ψ ≤ r) :
    bipartiteDefect (uniformDistribution Unit)
      (fun _ => P)
      (fun _ => B) ψ ≤ δ + Real.sqrt r := by
  have hgap := abs_overlap_gap_le_sqrt_of_opFamilyDistSq (uniformDistribution Unit)
    (fun _ => rightPlacedMeasurement B) (fun _ a => heteroKron (A.effect a) 1)
    (fun _ a => heteroKron (P.effect a) 1) ψ (uniformDistribution_isProbability Unit)
    hψ (ζ := r) (by rwa [opFamilyDistSq_symm])
  rw [bipartiteDefect_eq_one_sub ψ _ _ (uniformDistribution_isProbability Unit) hψ] at hcons ⊢
  change |avgOver (uniformDistribution Unit) (fun _ => ∑ a,
      stateQForm ψ (rightTensor (B.effect a) * leftTensor (A.effect a))) -
    avgOver (uniformDistribution Unit) (fun _ => ∑ a,
      stateQForm ψ (rightTensor (B.effect a) * leftTensor (P.effect a)))| ≤ _ at hgap
  simp only [rightTensor_mul_leftTensor_eq_opTensor] at hgap
  dsimp only [diagonalOverlap, opTensor, heteroKron] at hgap hcons ⊢
  have hdiff := (le_abs_self _).trans hgap
  linarith

include hδ hψ in
/-- Formalization-only transport of the rounding supplied by `lem:ortho`.
The projective measurement is chosen before the question distribution, outcome
maps, comparison measurements, and comparison error. The unit-state and
probability hypotheses give total mass one; only `δ ≥ 0` is required of the
rounding error, and no upper range bound on either error is used. This supports
the compression step in `lem:qld-4-7`, not its global-witness conclusion. -/
theorem projective_rounding_preserves_postprocessed_consistency_left
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => A)
      (fun _ => B) ψ ≤ δ) :
    ∃ P : Measurement α ιA, Measurement.IsProjective P ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (P.effect a) 1)
        (fun _ a => heteroKron (A.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : Distribution X), μ.IsProbability → ∀ (f : X → α → β)
        (N : X → Measurement β ιB) (η : ℝ),
        bipartiteDefect μ
          (fun x => A.postprocess (f x))
          N ψ ≤ η →
        bipartiteDefect μ
          (fun x => P.postprocess (f x))
          N ψ ≤
            δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
              2 * Real.sqrt (δ + η) := by
  obtain ⟨P, hP, hdist⟩ :=
    projective_rounding_with_explicit_constant ψ hψ A B δ hδ hcons
  refine ⟨P, hP, hdist, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hAN
  have hPB := rounding_consistency_le ψ hψ P A B δ _ hcons hdist
  simpa only [leftPlacedMeasurement, rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne] using consistencyDefect_trans_le μ
    (fun x => leftPlacedMeasurement (P.postprocess (f x)))
    (fun x => rightPlacedMeasurement (B.postprocess (f x)))
    (fun x => leftPlacedMeasurement (A.postprocess (f x)))
    (fun x => rightPlacedMeasurement (N x)) ψ _ δ η hμ hψ (by
      refine (consistencyDefect_postprocess_question_le μ
        (fun _ => P) (fun _ => B) ψ f).trans ?_
      rw [bipartiteDefect, consistencyDefect_const_eq μ hμ]
      exact hPB) (by
      refine (consistencyDefect_postprocess_question_le μ
        (fun _ => A) (fun _ => B) ψ f).trans ?_
      simp [consistencyDefect_const_eq μ hμ]
      exact hcons) hAN

/-- Tensor-factor exchange intertwines the two Kronecker-product actions. -/
private theorem applyOperatorToState_heteroKron_prodComm
    (A : Op ιA) (B : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState (heteroKron B A) (reindexState (Equiv.prodComm ιA ιB) ψ) =
      reindexState (Equiv.prodComm ιA ιB) (applyOperatorToState (heteroKron A B) ψ) := by
  have hop : heteroKron B A =
      (heteroKron A B).submatrix (Equiv.prodComm ιB ιA) (Equiv.prodComm ιB ιA) := by
    ext i j
    apply mul_comm
  apply (EuclideanSpace.equiv (ιB × ιA) ℂ).injective
  change heteroKron B A *ᵥ (ψ.ofLp ∘ (Equiv.prodComm ιB ιA)) =
    _
  rw [hop, Matrix.submatrix_mulVec_equiv]
  rfl

private theorem stateQForm_heteroKron_prodComm (A : Op ιA) (B : Op ιB) :
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
  simp only [bipartiteDefect, consistencyDefect]
  simp_rw [consistency_term_eq_stateQForm, placed_product_stateQForm_eq,
    stateQForm_heteroKron_prodComm]
  apply avgOver_congr
  intro x
  rw [Finset.sum_comm]
  simp only [eq_comm]

/-- Consistency of local POVMs is invariant under exchanging the players. -/
theorem bipartiteDefect_prodComm
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    bipartiteDefect μ B A (reindexState (Equiv.prodComm ιA ιB) ψ) = bipartiteDefect μ A B ψ :=
  consistencyDefect_prodComm μ _ _ ψ

/-- Formalization-only distance identity for the Bob-side rounding in
`lem:ortho`: left placement on the exchanged state is right placement on the
original state. The two local coordinate types may be different. -/
theorem opFamilyDistSq_left_prodComm {X α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A B : X → α → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron (B x a) 1) (reindexState (Equiv.prodComm ιA ιB) ψ) =
      opFamilyDistSq μ (fun x a => heteroKron 1 (A x a))
        (fun x a => heteroKron 1 (B x a)) ψ := by
  unfold opFamilyDistSq
  simp_rw [← heteroKron_sub_left, applyOperatorToState_heteroKron_prodComm,
    reindexState_norm_eq, heteroKron_sub_right]

include hδ hψ in
/-- Formalization-only Bob-side form of projective rounding and consistency
transport for `lem:qld-4-7`. It follows by explicitly exchanging the tensor
factors and applying the Alice-side theorem to the exchanged state. The error
and normalization hypotheses are exactly those of the Alice-side form. -/
theorem projective_rounding_preserves_postprocessed_consistency_right
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => A)
      (fun _ => B) ψ ≤ δ) :
    ∃ P : Measurement α ιB, Measurement.IsProjective P ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron 1 (P.effect a))
        (fun _ a => heteroKron 1 (B.effect a)) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : Distribution X), μ.IsProbability → ∀ (f : X → α → β)
        (N : X → Measurement β ιA) (η : ℝ),
        bipartiteDefect μ
          N
          (fun x => B.postprocess (f x)) ψ ≤ η →
        bipartiteDefect μ
          N
          (fun x => P.postprocess (f x)) ψ ≤
            δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
              2 * Real.sqrt (δ + η) := by
  obtain ⟨P, hP, hdist, htransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency_left
      (reindexState (Equiv.prodComm ιA ιB) ψ) (by rw [reindexState_norm_eq, hψ]) B A δ hδ (by rwa [bipartiteDefect_prodComm])
  rw [opFamilyDistSq_left_prodComm] at hdist
  refine ⟨P, hP, hdist, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hNB
  have hout := htransport μ hμ f N η (by rwa [bipartiteDefect_prodComm])
  rwa [bipartiteDefect_prodComm] at hout

include hδ hψ in
/-- Formalization-only simultaneous rounding and transport for the compression
step of `lem:qld-4-7`. A single pair of complete projective measurements on the
original heterogeneous spaces satisfies the distance bounds and both consistency
estimates for every finite question type, probability distribution, and
question-dependent outcome map. Each comparison family requires only its own
consistency bound against the corresponding unrounded POVM. The hypotheses are
`‖ψ‖ = 1`, `δ ≥ 0`, and the original cross-player consistency bound; no range
restriction on the comparison error or outcome-cardinality factor is imposed. -/
theorem projective_rounding_preserves_postprocessed_consistency
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => A)
      (fun _ => B) ψ ≤ δ) :
    ∃ PA : Measurement α ιA, ∃ PB : Measurement α ιB,
      Measurement.IsProjective PA ∧ Measurement.IsProjective PB ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (PA.effect a) 1)
        (fun _ a => heteroKron (A.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron 1 (PB.effect a))
        (fun _ a => heteroKron 1 (B.effect a)) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : Distribution X), μ.IsProbability → ∀ (f : X → α → β),
        (∀ (N : X → Measurement β ιB) (η : ℝ),
          bipartiteDefect μ
            (fun x => A.postprocess (f x))
            N ψ ≤ η →
          bipartiteDefect μ
            (fun x => PA.postprocess (f x))
            N ψ ≤
              δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
                2 * Real.sqrt (δ + η)) ∧
        (∀ (N : X → Measurement β ιA) (η : ℝ),
          bipartiteDefect μ
            N
            (fun x => B.postprocess (f x)) ψ ≤ η →
          bipartiteDefect μ
            N
            (fun x => PB.postprocess (f x)) ψ ≤
              δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
                2 * Real.sqrt (δ + η)) := by
  obtain ⟨PA, hPA, hAdist, hAtransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency_left ψ hψ A B δ hδ hcons
  obtain ⟨PB, hPB, hBdist, hBtransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency_right ψ hψ A B δ hδ hcons
  refine ⟨PA, PB, hPA, hPB, hAdist, hBdist, ?_⟩
  intro X β _ _ _ _ μ hμ f
  exact ⟨hAtransport μ hμ f, hBtransport μ hμ f⟩

end

end MIPStarRE.QPBT
