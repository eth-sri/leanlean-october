module

public import QPBT.Games.DistanceTheorems.LdtBridge
public import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
public import MIPStarRE.LDT.Preliminaries.Completion
public import MIPStarRE.LDT.Preliminaries.Triangles.Core

/-!
# Projective rounding for consistent POVMs

This module proves the orthonormalization lemma `lem:ortho` with an explicit
error constant: if a POVM `Q` on Alice's space and a POVM `R` on Bob's space are
`δ`-consistent on a unit bipartite state `ψ`, then Alice has a projective
measurement `P` on her original space with `P_a ⊗ 1` within `220 · δ^(1/4)` of
`Q_a ⊗ 1` on `ψ`.

The LDT orthonormalization theorem supplies a projective submeasurement. To
bound the cost of completing it, compare to the other party's almost-projective
measurement: the completion increases the matching mass, and missing mass is
bounded by the squared distance to the other party plus its projectivity defect.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`
- Blueprint `lem:ortho`
- Blueprint `lem:ortho-explicit-constant`, the statement proved in this module
- `references/ldt-paper/orthonormalization.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-- Regard a nonempty finite coordinate set as an LDT finite Hilbert space. -/
@[reducible] private def roundFiniteHilbertSpace (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : FiniteHilbertSpace :=
  { carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := inferInstance }

/-- A complete measurement on a nonzero finite space has a nonempty outcome type. -/
private theorem round_measurement_outcome_nonempty {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : MIPStarRE.Quantum.Measurement α ι) : Nonempty α := by
  classical
  by_contra hα
  haveI := not_nonempty_iff.mp hα
  let i : ι := Classical.choice inferInstance
  have heq := congrArg (fun X : Op ι => X i i) M.sum_eq_one
  simp [Matrix.sum_apply] at heq

open MIPStarRE.LDT.Preliminaries

/-- A weighted squared triangle inequality, giving more weight to the smaller error. -/
private theorem qSDD_weighted_triangle {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (ψ : QuantumState ι) (A B C : SubMeas α ι) :
    qSDD ψ A C ≤ 9 / 8 * qSDD ψ A B + 9 * qSDD ψ B C := by
  unfold qSDD qSDDCore
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  let X := A.outcome a - B.outcome a
  let Y := B.outcome a - C.outcome a
  rw [show A.outcome a - C.outcome a = X + Y by dsimp [X, Y]; abel]
  have h := ev_adjoint_self_nonneg ψ (X - (8 : ℝ) • Y)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, ev_sub, ev_real_smul] at h
  simp only [Matrix.conjTranspose_add, add_mul, mul_add, ev_add]
  change _ ≤ 9 / 8 * ev ψ (Xᴴ * X) + 9 * ev ψ (Yᴴ * Y)
  linarith

variable {ιA ιB α : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype α]

/-- When the left family is projective, its squared diagonal mass is its ordinary mass. -/
private theorem qSDD_left_projective_eq (ψ : QuantumState (ιA × ιB))
    (P : SubMeas α ιA) (B : SubMeas α ιB) (hP : ∀ a, P.outcome a * P.outcome a = P.outcome a) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) P) (rightPlacedSubMeas (ιA := ιA) B) =
      ev ψ (leftTensor (ι₂ := ιB) P.total) +
        (∑ a, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) -
        2 * qBipartiteMatchMass ψ P B := by
  simp only [qSDD, qSDDCore, qBipartiteMatchMass, Matrix.conjTranspose_sub,
    SubMeas.outcome_hermitian, leftPlacedSubMeas_outcome, rightPlacedSubMeas_outcome,
    leftTensor_conjTranspose, rightTensor_conjTranspose,
    sub_mul, mul_sub, leftTensor_mul_leftTensor, rightTensor_mul_rightTensor, hP,
    leftTensor_mul_rightTensor_eq_opTensor, rightTensor_mul_leftTensor_eq_opTensor,
    ev_sub, Finset.sum_sub_distrib]
  have hsum : (∑ a, ev ψ (leftTensor (ι₂ := ιB) (P.outcome a))) =
      ev ψ (leftTensor (ι₂ := ιB) P.total) := by
    rw [← ev_sum, leftTensor_finset_sum, P.sum_eq_total]
  rw [hsum]
  ring

/-- Completing on Alice's side improves the overlap with the right family.
Its squared distance grows by at most the old squared distance plus the
right measurement's projectivity defect. -/
private theorem qSDD_complete_left_le (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (P : ProjSubMeas α ιA) (B : SubMeas α ιB) (a₀ : α) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) (completeAtOutcomeProj P a₀).toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B) ≤
      2 * qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) (rightPlacedSubMeas (ιA := ιA) B) +
        (1 - ∑ a, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) := by
  let C := completeAtOutcomeProj P a₀
  have hmono : qBipartiteMatchMass ψ P.toSubMeas B ≤ qBipartiteMatchMass ψ C.toSubMeas B := by
    classical
    unfold qBipartiteMatchMass
    refine Finset.sum_le_sum fun a _ => ev_mono ψ _ _ (opTensor_mono_left ?_ (B.outcome_pos a))
    by_cases h : a = a₀
    · simpa [C, completeAtOutcome, h] using P.toSubMeas.total_le_one
    · simp [C, completeAtOutcome, h]
  have htotal : qBipartiteMatchMass ψ P.toSubMeas B ≤ ev ψ (leftTensor (ι₂ := ιB) P.total) := by
    unfold qBipartiteMatchMass
    rw [← P.toSubMeas.sum_eq_total,
      ← leftTensor_finset_sum (ι₂ := ιB) Finset.univ P.toSubMeas.outcome, ev_sum]
    exact Finset.sum_le_sum fun a _ => ev_mono ψ _ _
      (opTensor_mono_right (P.outcome_pos a) (B.outcome_le_one a))
  change qSDD ψ (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) _ ≤ _
  rw [qSDD_left_projective_eq ψ _ _ C.proj, qSDD_left_projective_eq ψ _ _ P.proj,
    C.toMeasurement.total_eq_one, leftTensor_one, ev_one_of_isNormalized _ hψ]
  linarith

/-- Complete the LDT submeasurement without changing the `220 δ^(1/4)` bound. -/
private lemma round_projective_ldt
    [DecidableEq α] (Ψ : QuantumState (ιA × ιB)) (hΨ : Ψ.IsNormalized)
    (A : MIPStarRE.LDT.Measurement α ιA) (B : MIPStarRE.LDT.Measurement α ιB)
    (a₀ : α) (δ : Error) (hδ : 0 ≤ δ)
    (hCons : ConsRel Ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ) :
    ∃ C : ProjMeas α ιA,
      qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤ 220 * zetaQuarterRoot δ := by
  let t := zetaQuarterRoot δ
  let AL := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
  let BR := rightPlacedSubMeas (ιA := ιA) B.toSubMeas
  have ht : 0 ≤ t := zetaQuarterRoot_nonneg hδ
  by_cases hs : t ≤ 1 / 8
  · have hδt : δ ≤ t / 512 := by
      have hpow : t ^ 4 = δ := by
        dsimp [t, zetaQuarterRoot]
        rw [← Real.rpow_natCast (δ ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hδ]
        norm_num
      have hc := pow_le_pow_left₀ ht hs 3
      rw [← hpow, show t ^ 4 = t ^ 3 * t by ring]
      convert mul_le_mul_of_nonneg_right hc ht using 1 <;> ring
    obtain ⟨P, hP⟩ := orthonormalizationMainLemma Ψ hΨ A B δ hδ hCons
    let PL := leftPlacedSubMeas (ιB := ιB) P.toSubMeas
    let C := completeAtOutcomeProj P a₀
    let CL := leftPlacedSubMeas (ιB := ιB) C.toSubMeas
    have hPA : qSDD Ψ PL AL ≤ 84 * t := by
      rw [qSDD_symm]
      simpa only [AL, PL, t, zetaQuarterRoot, constFamily_sdd_unit, orthonormalizationMainLemmaError] using hP.squaredDistanceBound
    have hAB : qSDD Ψ AL BR ≤ 2 * δ := by
      have h := simeqToApprox_heterogeneous Ψ (uniformDistribution Unit) (fun _ => A) (fun _ => B)
        δ hCons
      exact (constFamily_sdd_unit Ψ AL BR).symm ▸ h.squaredDistanceBound
    have hB : 1 - (∑ a, ev Ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) ≤ 4 * δ := by
      have h := (consistencyToAlmostProjective_right Ψ A B δ hCons).sourceAlmostProjective
      have hsum : (∑ a, ev Ψ (BR.outcome a)) = 1 := by
        rw [← ev_sum, BR.sum_eq_total]
        change ev Ψ (rightTensor (ι₁ := ιA) B.total) = _
        rw [B.total_eq_one, rightTensor_one, ev_one_of_isNormalized _ hΨ]
      change (∑ a, ev Ψ (BR.outcome a - BR.outcome a * BR.outcome a)) ≤ 2 * δ at h
      simp only [ev_sub, Finset.sum_sub_distrib, hsum] at h
      simpa only [BR, rightPlacedSubMeas_outcome, rightTensor_mul_rightTensor] using
        h.trans (show 2 * δ ≤ 4 * δ by linarith)
    have hPB := qSDD_weighted_triangle Ψ PL AL BR
    have hCB := qSDD_complete_left_le Ψ hΨ P B.toSubMeas a₀
    change qSDD Ψ CL BR ≤ 2 * qSDD Ψ PL BR + _ at hCB
    have hCA := qSDD_weighted_triangle Ψ CL BR AL
    rw [qSDD_symm Ψ BR AL, qSDD_symm Ψ CL AL] at hCA
    exact ⟨C, by linarith⟩
  · let Z : ProjSubMeas α ιA := zeroProjSubMeas
    let C := completeAtOutcomeProj Z a₀
    let ZL := leftPlacedSubMeas (ιB := ιB) Z.toSubMeas
    let CL := leftPlacedSubMeas (ιB := ιB) C.toSubMeas
    have hAZ : qSDD Ψ AL ZL ≤ 1 := qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ A.toSubMeas
    have hCZ : qSDD Ψ CL ZL ≤ 1 := qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ C.toSubMeas
    have h := questionSDD_triangle Ψ AL ZL CL
    rw [qSDD_symm Ψ ZL CL] at h
    exact ⟨C, by linarith⟩

/-- A consistent pair of POVMs admits an Alice-side projective rounding with
the explicit dimension-independent error `220 * δ^(1/4)`. -/
theorem projective_rounding_with_explicit_constant {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error) (hδ : 0 ≤ δ)
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => Q)
      (fun _ => R) ψ ≤ δ) :
    ∃ Pm : MIPStarRE.Quantum.Measurement α ιA,
      MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (Pm.effect a) 1)
        (fun _ a => heteroKron (Q.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : Error) := by
  have hι : Nonempty (ιA × ιB) := by
    by_contra hempty
    letI : IsEmpty (ιA × ιB) := not_nonempty_iff.mp hempty
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  haveI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
  haveI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
  have hα := round_measurement_outcome_nonempty Q
  letI := hα
  let a₀ : α := Classical.choice hα
  let Ψ : PureState (ιA × ιB) := pureStateOfUnitVector ψ hψ
  let HA : FiniteHilbertSpace := roundFiniteHilbertSpace ιA
  let HB : FiniteHilbertSpace := roundFiniteHilbertSpace ιB
  let A : MIPStarRE.LDT.Measurement α ιA :=
    MatrixMeasurement.toMeasurement (H := HA) Q
  let B : MIPStarRE.LDT.Measurement α ιB :=
    MatrixMeasurement.toMeasurement (H := HB) R
  have hCons : ConsRel (Ψ : QuantumState (ιA × ιB)) (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ := by
    exact (ldt_consRel_iff_consistencyDefect Ψ (uniformDistribution Unit) (fun _ => A)
      (fun _ => B) δ).mpr hcons
  obtain ⟨C, hC⟩ := round_projective_ldt (Ψ : QuantumState (ιA × ιB))
    Ψ.toQuantumState_isNormalized A B a₀ δ hδ hCons
  let Pm := ldtMeasurementToMatrixMeasurement C.toMeasurement
  refine ⟨Pm, fun a => ⟨C.proj a, (Matrix.nonneg_iff_posSemidef.mp (C.outcome_pos a)).isHermitian.eq⟩, ?_⟩
  have hdist :
      opFamilyDistSq (uniformDistribution Unit)
          (fun _ a => heteroKron (Pm.effect a) 1)
          (fun _ a => heteroKron (Q.effect a) 1) ψ =
        qSDD (Ψ : QuantumState (ιA × ιB))
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) := by
    rw [opFamilyDistSq, avgOver_uniform_const]
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_applyOperatorToState_sq]
    exact pureState_stateQForm_eq_ev Ψ _
  rw [hdist]
  rw [MIPStarRE.LDT.Preliminaries.qSDD_symm]
  simpa [zetaQuarterRoot] using hC

end

end MIPStarRE.QPBT
