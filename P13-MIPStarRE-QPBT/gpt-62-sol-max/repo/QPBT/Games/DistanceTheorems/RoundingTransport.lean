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

private theorem consistencyDefect_const_eq {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (hμ : μ.IsProbability)
    (A B : α → Op ι) (ψ : EuclideanSpace ℂ ι) :
    consistencyDefect μ (fun _ => A) (fun _ => B) ψ =
      consistencyDefect (uniformDistribution Unit) (fun _ => A) (fun _ => B) ψ := by
  unfold consistencyDefect
  rw [avgOver_const_of_isProbability μ hμ,
    avgOver_const_of_isProbability _ (uniformDistribution_isProbability Unit)]

set_option maxHeartbeats 400000 in
-- The lifted effects introduce two instances of finite-dimensional overlap.
/-- The overlap estimate converts a same-space squared-distance bound into a
square-root loss in consistency with the unchanged opposite-player POVM. -/
private theorem rounding_consistency_le {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (P A : Measurement α ιA) (B : Measurement α ιB) (δ r : ℝ)
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
    hψ r ((opFamilyDistSq_symm _ _ _ _).ge.trans hdist)
  rw [consistencyDefect_placed_eq_one_sub_overlap (uniformDistribution Unit)
    (fun _ => A) (fun _ => B)
    ψ (uniformDistribution_isProbability Unit) hψ] at hcons
  rw [consistencyDefect_placed_eq_one_sub_overlap (uniformDistribution Unit)
    (fun _ => P) (fun _ => B)
    ψ (uniformDistribution_isProbability Unit) hψ]
  simp only [rightPlacedMeasurement_effect, heteroKron_mul, one_mul, mul_one] at hgap
  linarith only [hcons, le_of_abs_le hgap]

section

variable {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (A : Measurement α ιA) (B : Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => A)
      (fun _ => B) ψ ≤ δ)
include ιA ιB α ψ hψ A B δ hδ hcons

/-- Formalization-only transport of the rounding supplied by `lem:ortho`.
The projective measurement is chosen before the question distribution, outcome
maps, comparison measurements, and comparison error. The unit-state and
probability hypotheses give total mass one; only `δ ≥ 0` is required of the
rounding error, and no upper range bound on either error is used. This supports
the compression step in `lem:qld-4-7`, not its global-witness conclusion. -/
theorem projective_rounding_preserves_postprocessed_consistency_left :
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
  have hABf : bipartiteDefect μ
      (fun x => A.postprocess (f x))
      (fun x => B.postprocess (f x)) ψ ≤ δ := by
    refine (consistencyDefect_postprocess_question_le μ
      (fun _ => A) (fun _ => B) ψ f).trans ?_
    rw [bipartiteDefect, consistencyDefect_const_eq μ hμ]
    exact hcons
  have hPBf : bipartiteDefect μ
      (fun x => P.postprocess (f x))
      (fun x => B.postprocess (f x)) ψ ≤
        δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) := by
    refine (consistencyDefect_postprocess_question_le μ
      (fun _ => P) (fun _ => B) ψ f).trans ?_
    rw [bipartiteDefect, consistencyDefect_const_eq μ hμ]
    exact hPB
  simpa only [measurementDefect, bipartiteDefect, leftPlacedMeasurement_effect, rightPlacedMeasurement_effect] using consistencyDefect_trans_le μ
    (fun x => leftPlacedMeasurement (P.postprocess (f x)))
    (fun x => rightPlacedMeasurement (B.postprocess (f x)))
    (fun x => leftPlacedMeasurement (A.postprocess (f x)))
    (fun x => rightPlacedMeasurement (N x)) ψ _ δ η hμ hψ hPBf hABf hAN

/-- Formalization-only Bob-side form of projective rounding and consistency
transport for `lem:qld-4-7`. It follows by explicitly exchanging the tensor
factors and applying the Alice-side theorem to the exchanged state. The error
and normalization hypotheses are exactly those of the Alice-side form. -/
theorem projective_rounding_preserves_postprocessed_consistency_right :
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
  have hψ' : ‖reindexState (Equiv.prodComm ιA ιB) ψ‖ = 1 := by
    rw [reindexState_norm_eq, hψ]
  have hcons' : bipartiteDefect (uniformDistribution Unit)
      (fun _ => B)
      (fun _ => A)
      (reindexState (Equiv.prodComm ιA ιB) ψ) ≤ δ := by
    rwa [bipartiteDefect, consistencyDefect_prodComm]
  obtain ⟨P, hP, hdist, htransport⟩ :=
    projective_rounding_preserves_postprocessed_consistency_left
      (reindexState (Equiv.prodComm ιA ιB) ψ) hψ' B A δ hδ hcons'
  simp only [opFamilyDistSq_reindexState, reindexOp_prodComm_heteroKron] at hdist
  refine ⟨P, hP, hdist, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hNB
  have hNB' : bipartiteDefect μ
      (fun x => B.postprocess (f x))
      N
      (reindexState (Equiv.prodComm ιA ιB) ψ) ≤ η := by
    rwa [bipartiteDefect, consistencyDefect_prodComm]
  have hout := htransport μ hμ f N η hNB'
  rwa [bipartiteDefect, consistencyDefect_prodComm] at hout

/-- Formalization-only simultaneous rounding and transport for the compression
step of `lem:qld-4-7`. A single pair of complete projective measurements on the
original heterogeneous spaces satisfies the distance bounds and both consistency
estimates for every finite question type, probability distribution, and
question-dependent outcome map. Each comparison family requires only its own
consistency bound against the corresponding unrounded POVM. The hypotheses are
`‖ψ‖ = 1`, `δ ≥ 0`, and the original cross-player consistency bound; no range
restriction on the comparison error or outcome-cardinality factor is imposed. -/
theorem projective_rounding_preserves_postprocessed_consistency :
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

end

end MIPStarRE.QPBT
