module

public import QPBT.Extraction.EPRProjection
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The auxiliary vector from the EPR projection

Taking the partial inner product with the EPR vector constructs the
unnormalized auxiliary vector. Tensoring it with EPR gives exactly the
orthogonal projection of the original vector onto the EPR subspace.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1769-1783`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum

noncomputable section

namespace Extraction

/-- Partial inner product with the EPR vector, leaving the auxiliary index.
This is the coordinate form of the vector defined at paper line 1769. -/
def eprPartialInner {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (ψ : EuclideanSpace ℂ (R × (V × V))) : EuclideanSpace ℂ R :=
  (EuclideanSpace.equiv R ℂ).symm
    (fun r => ∑ p : V × V, star (eprState V p) * ψ (r, p))

/-- Tensoring the EPR partial inner product with EPR gives the rank-one
projection on the second tensor factor. This is the projection equality in
paper lines 1776-1779; no normalization of the auxiliary vector is assumed. -/
theorem vecTensor_eprPartialInner {R V : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (ψ : EuclideanSpace ℂ (R × (V × V))) :
    vecTensor (eprPartialInner ψ) (eprState V) =
      applyOperatorToState
        (heteroKron (1 : Op R) (Matrix.vecMulVec (fun x => eprState V x)
          (fun y => star (eprState V y)))) ψ := by
  ext x
  change (∑ p : V × V, star (eprState V p) * ψ (x.1, p)) * eprState V x.2 =
    ∑ j : R × (V × V),
      ((1 : Op R) x.1 j.1 * (eprState V x.2 * star (eprState V j.2))) * ψ j
  conv_rhs => rw [Fintype.sum_prod_type]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

end Extraction

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)

open scoped Classical

/-- Tensoring an auxiliary vector with EPR preserves its norm. -/
theorem idealExpState_norm
    (aux : EuclideanSpace ℂ
      (S.ExtractionAux)) :
    ‖S.idealExpState aux‖ = ‖aux‖ := by
  rw [idealExpState, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm, mul_one]

/-- A normalized reference vector on `AA'BB'`, formed from the original state
and one EPR pair. It is used when the EPR projection of the given state vanishes. -/
def extractionAuxReference : EuclideanSpace ℂ
    (S.ExtractionAux) :=
  reindexState prodShuffle (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))

/-- The reference auxiliary vector has norm one. -/
theorem extractionAuxReference_norm : ‖S.extractionAuxReference‖ = 1 := by
  rw [extractionAuxReference, reindexState_norm_eq, vecTensor_norm_eq, eprState_norm,
    S.toStrategy.ψ_norm, one_mul]

/-- The EPR projection on registers `A''B''`, with identity on `AA'BB'`.
Paper lines 1766-1769 use this projection to select the auxiliary vector. -/
def extractionEprProjection : Op (S.ExpandedSpace) :=
  reindexOp S.extractionShuffle.symm
    (heteroKron (1 : Op (S.ExtractionAux))
      (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
        (fun y => star (eprState (PauliRegister P) y))))

/-- The auxiliary vector before normalization, obtained by contracting the
extracted registers against EPR. This is `aux_0` at paper line 1769. -/
def extractionAux0
    (θ : EuclideanSpace ℂ (S.ExpandedSpace)) :
    EuclideanSpace ℂ (S.ExtractionAux) :=
  Extraction.eprPartialInner
    (reindexState S.extractionShuffle.symm θ)

/-- The unnormalized ideal extraction state is the EPR projection of the
given six-register state. This identifies the actual auxiliary construction
with the projection in paper lines 1776-1779, retaining the heterogeneous
player spaces of blueprint `lem:qld-unitary`. -/
theorem idealExpState_extractionAux0
    (θ : EuclideanSpace ℂ (S.ExpandedSpace)) :
    S.idealExpState (S.extractionAux0 θ) =
      applyOperatorToState S.extractionEprProjection θ := by
  unfold idealExpState extractionAux0
  rw [Extraction.vecTensor_eprPartialInner]
  ext x
  let e := S.extractionShuffle.symm
  let T := heteroKron
    (1 : Op (S.ExtractionAux))
    (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
      (fun y => star (eprState (PauliRegister P) y)))
  change (T *ᵥ (fun j => θ (e.symm j))) (e x) =
    ((T.submatrix e e) *ᵥ (fun j => θ j)) x
  exact (congrFun (Matrix.submatrix_mulVec_equiv T (fun j => θ j) e e) x).symm

/-- Normalize the projected auxiliary vector at twice the projection error,
using the reference vector when the projection vanishes. -/
theorem exists_unit_aux_near_eprProjection
    (θ : EuclideanSpace ℂ (S.ExpandedSpace)) (hθ : ‖θ‖ = 1) :
    ∃ aux : EuclideanSpace ℂ (S.ExtractionAux),
      ‖aux‖ = 1 ∧ ‖θ - S.idealExpState aux‖ ≤
        2 * ‖θ - applyOperatorToState S.extractionEprProjection θ‖ := by
  rw [← S.idealExpState_extractionAux0]
  let a := S.extractionAux0 θ
  change ∃ b, ‖b‖ = 1 ∧ ‖θ - S.idealExpState b‖ ≤ 2 * ‖θ - S.idealExpState a‖
  have hgap := abs_norm_sub_norm_le θ (S.idealExpState a)
  rw [hθ, S.idealExpState_norm] at hgap
  by_cases hz : a = 0
  · refine ⟨S.extractionAuxReference, S.extractionAuxReference_norm, ?_⟩
    have ha : ‖a‖ = 0 := by simp [hz]
    rw [ha, sub_zero, abs_one] at hgap
    have ht := norm_sub_le θ (S.idealExpState S.extractionAuxReference)
    rw [hθ, S.idealExpState_norm, S.extractionAuxReference_norm] at ht
    linarith
  · let b := NormedSpace.normalize a
    have hb : ‖b‖ = 1 := NormedSpace.norm_normalize hz
    have hf (r : ℝ) (v : EuclideanSpace ℂ S.ExtractionAux) :
        S.idealExpState (r • v) = r • S.idealExpState v := by
      ext x
      simp [idealExpState, reindexState, vecTensor, EuclideanSpace.equiv, Algebra.smul_def, mul_assoc]
    have hs : ‖a‖ • S.idealExpState b = S.idealExpState a := by
      rw [← hf]
      exact congrArg S.idealExpState (NormedSpace.norm_smul_normalize a)
    have hd : ‖S.idealExpState a - S.idealExpState b‖ = |1 - ‖a‖| := calc
      _ = ‖(‖a‖ - 1) • S.idealExpState b‖ := by rw [← hs, sub_smul, one_smul]
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, S.idealExpState_norm, hb, mul_one, abs_sub_comm]
    refine ⟨b, hb, ?_⟩
    have ht := norm_sub_le_norm_sub_add_norm_sub θ (S.idealExpState a) (S.idealExpState b)
    rw [hd] at ht
    linarith

end ProjectiveSetting

end

end MIPStarRE.QPBT
