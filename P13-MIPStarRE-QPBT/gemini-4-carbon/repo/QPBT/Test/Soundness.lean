module

public import QPBT.Test.SoundnessDefs
public import QPBT.Test.Completeness
public import QPBT.Extraction
public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.DirectLowDegreeCore
public import QPBT.Observables.WinImplications.Interchange
public import QPBT.Observables.WinImplications.LowDegree
public import QPBT.Games.MeasurementCompression
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-! # Pauli basis test soundness -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus MagicSquareRigidity

noncomputable section

/-! ### Ancilla isometries and range projection -/

def ancillaBlockIsometry {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((ι × κ) × ν) where
  toFun psi := reindexState (Equiv.prodAssoc ι κ ν).symm (vecTensor psi eta)
  map_add' _ _ := by ext; simp [reindexState, vecTensor, add_mul]
  map_smul' _ _ := by ext; simp [reindexState, vecTensor, mul_assoc]
  norm_map' psi := by
    change ‖reindexState _ (vecTensor psi eta)‖ = _
    rw [reindexState_norm_eq, vecTensor_norm_eq, heta, mul_one]

theorem ancillaBlockIsometry_matrix_apply {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1) (p : (ι × κ) × ν) (i : ι) :
    isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) p i =
      if p.1.1 = i then eta (p.1.2, p.2) else 0 := by
  rw [isometryMatrix_apply]; simp [ancillaBlockIsometry, reindexState, vecTensor, eq_comm]

def unitaryAncillaIsometry {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ((ι × κ) × ν) where
  toLinearMap := (Matrix.toEuclideanLin U).comp (ancillaBlockIsometry eta heta).toLinearMap
  norm_map' psi := by
    change ‖Matrix.toEuclideanLin U (ancillaBlockIsometry eta heta psi)‖ = _
    rw [norm_toEuclideanLin_of_conjTranspose_mul_eq_one hU, LinearIsometry.norm_map]

theorem unitaryAncillaIsometry_matrix {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) :
    isometryMatrix (unitaryAncillaIsometry eta heta U hU) =
      U * isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) := by
  apply Matrix.toEuclideanLin.injective; ext psi
  rw [toEuclideanLin_mul_apply]
  simp only [isometryMatrix, Matrix.toEuclideanLin.apply_symm_apply]; rfl

theorem unitaryAncillaIsometry_intertwines {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (eta : EuclideanSpace ℂ (κ × ν)) (heta : ‖eta‖ = 1)
    (U : Op ((ι × κ) × ν)) (hU : Uᴴ * U = 1) (M : Op ι) :
    (U * heteroKron (heteroKron M (1 : Op κ)) (1 : Op ν) * Uᴴ) *
        isometryMatrix (unitaryAncillaIsometry eta heta U hU) =
      isometryMatrix (unitaryAncillaIsometry eta heta U hU) * M := by
  have hanc : heteroKron (heteroKron M (1 : Op κ)) (1 : Op ν) *
      isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) =
      isometryMatrix (ancillaBlockIsometry (ι := ι) eta heta) * M := by
    ext p i
    simp [Matrix.mul_apply, ancillaBlockIsometry_matrix_apply, heteroKron,
      Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type, mul_comm]
  rw [unitaryAncillaIsometry_matrix]; simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, hanc]

private theorem conjIsometry_isProj {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {Q : Op ι} (hQ : IsProj Q) : IsProj (conjIsometry phi Q) :=
  ⟨by change _ * _ = _; rw [conjIsometry_mul, hQ.isIdempotentElem.eq],
    by change star _ = _; simp [conjIsometry_eq, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]⟩

theorem sum_norm_mul_projection_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N : Measurement α ι) (T : α → Op ι) (Q : Op ι) (hQ : IsProj Q)
    (theta delta : EuclideanSpace ℂ ι) (htheta : applyOperatorToState Q theta = theta) :
    ∑ a : α, ‖applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2) +
        2 * ‖delta - theta‖ ^ 2 := by
  have hvanish : applyOperatorToState (1 - Q) theta = 0 := by
    simp [applyOperatorToState, show Matrix.toEuclideanLin Q theta = theta from htheta]
  have hcomp : ‖applyOperatorToState (1 - Q) delta‖ ^ 2 ≤ ‖delta - theta‖ ^ 2 := by
    have h := norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    rw [applyOperatorToState_sub, hvanish, sub_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hsum := (sum_norm_mul_apply_le N.effect (1 - Q) delta
    (measurement_sum_adjoint_mul_le_one N)).trans hcomp
  have hpt (a : α) : ‖applyOperatorToState (N.effect a * Q - T a) delta‖ ^ 2 ≤
      2 * ‖applyOperatorToState (N.effect a - T a) delta‖ ^ 2 +
        2 * ‖applyOperatorToState (N.effect a * (1 - Q)) delta‖ ^ 2 := by
    have hsp : applyOperatorToState (N.effect a * Q - T a) delta =
        applyOperatorToState (N.effect a - T a) delta -
          applyOperatorToState (N.effect a * (1 - Q)) delta := by
      rw [show N.effect a * Q - T a = (N.effect a - T a) - N.effect a * (1 - Q) by noncomm_ring]
      simp [applyOperatorToState]
    rw [hsp]
    have hp := parallelogram_law_with_norm ℂ (applyOperatorToState (N.effect a - T a) delta)
      (applyOperatorToState (N.effect a * (1 - Q)) delta)
    nlinarith [sq_nonneg ‖applyOperatorToState (N.effect a - T a) delta +
      applyOperatorToState (N.effect a * (1 - Q)) delta‖]
  have hs := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpt a
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linarith

theorem sum_norm_leftTensor_conjIsometry_sub_sq_le {α ιA ιB κA κB : Type}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : α → Op ιA) (N : Measurement α κA) (T : α → Op (κA × κB))
    (hint : ∀ a, N.effect a * isometryMatrix phiA = isometryMatrix phiA * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a, ‖applyOperatorToState (heteroKron (conjIsometry phiA (M a)) 1 - T a) delta‖ ^ 2 ≤
      2 * (∑ a, ‖applyOperatorToState (heteroKron (N.effect a) 1 - T a) delta‖ ^ 2) +
        2 * ‖delta - isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : Op (κA × κB) := heteroKron (conjIsometry phiA 1) 1
  have hQ : IsProj Q :=
    MakingMeasurementsProjective.isProj_kronecker (conjIsometry_isProj phiA (.one _)) (.one _)
  have hfix : applyOperatorToState Q (isometryTensor phiA phiB psi) = isometryTensor phiA phiB psi := by
    dsimp [Q]; rw [applyOperatorToState_leftTensor_conjIsometry, heteroKron_one_one, applyOperatorToState_one]
  have hc (a) : (leftPlacedMeasurement N).effect a * Q = heteroKron (conjIsometry phiA (M a)) 1 := by
    change heteroKron (N.effect a) 1 * heteroKron (conjIsometry phiA 1) 1 = _
    rw [heteroKron_mul, Matrix.one_mul, conjIsometry_eq, Matrix.mul_one, ← Matrix.mul_assoc, hint a]
    rfl
  have hb := sum_norm_mul_projection_sub_sq_le (leftPlacedMeasurement N) T Q hQ _ delta hfix
  simp only [hc] at hb
  simpa only [leftPlacedMeasurement, Measurement.ofSumEqOne] using hb

theorem sum_norm_rightTensor_conjIsometry_sub_sq_le {α ιA ιB κA κB : Type}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : α → Op ιB) (N : Measurement α κB) (T : α → Op (κA × κB))
    (hint : ∀ a, N.effect a * isometryMatrix phiB = isometryMatrix phiB * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a, ‖applyOperatorToState (heteroKron 1 (conjIsometry phiB (M a)) - T a) delta‖ ^ 2 ≤
      2 * (∑ a, ‖applyOperatorToState (heteroKron 1 (N.effect a) - T a) delta‖ ^ 2) +
        2 * ‖delta - isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : Op (κA × κB) := heteroKron 1 (conjIsometry phiB 1)
  have hQ : IsProj Q :=
    MakingMeasurementsProjective.isProj_kronecker (.one _) (conjIsometry_isProj phiB (.one _))
  have hfix : applyOperatorToState Q (isometryTensor phiA phiB psi) = isometryTensor phiA phiB psi := by
    dsimp [Q]; rw [applyOperatorToState_rightTensor_conjIsometry, heteroKron_one_one, applyOperatorToState_one]
  have hc (a) : (rightPlacedMeasurement N).effect a * Q = heteroKron 1 (conjIsometry phiB (M a)) := by
    change heteroKron 1 (N.effect a) * heteroKron 1 (conjIsometry phiB 1) = _
    rw [heteroKron_mul, Matrix.one_mul, conjIsometry_eq, Matrix.mul_one, ← Matrix.mul_assoc, hint a]
    rfl
  have hb := sum_norm_mul_projection_sub_sq_le (rightPlacedMeasurement N) T Q hQ _ delta hfix
  simp only [hc] at hb
  simpa only [rightPlacedMeasurement, Measurement.ofSumEqOne] using hb

/-! ### Lifted effect & projector tensor identities -/

private theorem liftedAEffect_eq_tensor {P : AdmissibleParams} {G : Game} (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φ M = heteroKron (conjIsometry φ M) 1 := by
  ext i j; simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem liftedBEffect_eq_tensor {P : AdmissibleParams} {G : Game} (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ] EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φ M = heteroKron 1 (conjIsometry φ M) := by
  ext i j; simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem pauliProjOnA_eq_tensor (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron (heteroKron 1 (pauliProj W h)) 1 := by
  ext i j; simp [pauliProjOnA'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem pauliProjOnB_eq_tensor (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron 1 (heteroKron 1 (pauliProj W h)) := by
  ext i j; simp [pauliProjOnB'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

/-! ### Projective setting soundness -/

def ExtractionWitness.toPauliSoundnessWitness {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
    {S : ProjectiveSetting P epsilon} {w : GlobalPairWitness S deltaG}
    (v : ExtractionWitness S w delta) : PauliSoundnessWitness P S.toStrategy where
  ιA' := S.toStrategy.ιA × PauliRegister P
  ιB' := S.toStrategy.ιB × PauliRegister P
  φA := unitaryAncillaIsometry (eprState (PauliRegister P)) (eprState_norm _)
    (swapUnitary w .alice) (v.swap_left_unitary .alice)
  φB := unitaryAncillaIsometry (eprState (PauliRegister P)) (eprState_norm _)
    (swapUnitary w .bob) (v.swap_left_unitary .bob)
  aux := v.aux
  aux_norm := v.aux_norm

theorem ExtractionWitness.state_error_eq {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
    {S : ProjectiveSetting P epsilon} {w : GlobalPairWitness S deltaG}
    (v : ExtractionWitness S w delta) :
    ‖isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
        S.toStrategy.ψ - idealState P v.toPauliSoundnessWitness.aux‖ ^ 2 =
      ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  classical
  let e6 := sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB
  have hanc : isometryTensor
      (ancillaBlockIsometry (ι := S.toStrategy.ιA) (eprState (PauliRegister P)) (eprState_norm _))
      (ancillaBlockIsometry (ι := S.toStrategy.ιB) (eprState (PauliRegister P)) (eprState_norm _))
      S.toStrategy.ψ = reindexState e6 S.psiHat := by
    ext p; simp [isometryTensor_apply_eq, ancillaBlockIsometry_matrix_apply, Matrix.kronecker,
      Fintype.sum_prod_type, ProjectiveSetting.psiHat, reindexState, vecTensor,
      e6, sixRegExtractionEquiv, sixRegShuffle, mul_comm, mul_left_comm]
  have hten : isometryTensor v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
      S.toStrategy.ψ = reindexState e6
        (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat) := by
    change isometryTensor
      (unitaryAncillaIsometry _ _ _ (v.swap_left_unitary .alice))
      (unitaryAncillaIsometry _ _ _ (v.swap_left_unitary .bob)) _ = _
    rw [isometryTensor_eq_toEuclideanLin, unitaryAncillaIsometry_matrix,
      unitaryAncillaIsometry_matrix, Matrix.kronecker, Matrix.mul_kronecker_mul,
      toEuclideanLin_mul_apply]
    rw [isometryTensor_eq_toEuclideanLin] at hanc
    erw [hanc]; ext p; symm
    change ((Matrix.kronecker (swapUnitary w .alice) (swapUnitary w .bob)).submatrix e6 e6 *ᵥ
      fun i => S.psiHat i) (e6.symm p) = _
    erw [Matrix.submatrix_mulVec_equiv]; rfl
  have hid : idealState P v.toPauliSoundnessWitness.aux = reindexState e6 (S.idealExpState v.aux) :=
    by ext; rfl
  rw [hten, hid]
  dsimp +instances only [ExtractionWitness.toPauliSoundnessWitness, ProjectiveSetting.LocalSpace,
    ProjectiveSetting.localSpaceFintype, ProjectiveSetting.localSpaceDecidableEq]
  rw [show reindexState e6 _ - reindexState e6 _ = reindexState e6 (_ - _) from rfl,
    reindexState_norm_eq]

private theorem two_mul_add_two_mul_le {a b d : ℝ} (ha : a ≤ d) (hb : b ≤ d) :
    2 * a + 2 * b ≤ 4 * d := by linarith

theorem exists_projective_setting_isometry_bounds :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ),
        0 ≤ epsilon → epsilon ≤ 1 → ∀ S : ProjectiveSetting P epsilon,
          ∃ t : PauliSoundnessWitness P S.toStrategy,
            ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
              deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
              deltaQld a b epsilon P.m P.d P.q) ∧
            (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
              deltaQld a b epsilon P.m P.d P.q) := by
  classical
  obtain ⟨a, b, C, ha, hb, hb1, hC, hextract⟩ := exists_extractionWitness
  obtain ⟨A, B, hA, hB, hB1, herror⟩ := deltaExtract_le_deltaQld C a b hC ha hb hb1
  refine ⟨4 * A, B / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon heps0 heps1 S
  obtain ⟨w, ⟨v⟩⟩ := hextract P epsilon heps0 heps1 S
  have hst_sq := (v.state_error_eq).trans_le v.state_close
  have hfour := scale_deltaQld_le (P := P) (b := B / 2) hA heps0 (by norm_num : (1 : ℝ) ≤ 4)
  have hmono := deltaQld_mono (P := P) hA le_rfl (show B / 2 ≤ B by linarith)
    (by positivity) heps0 heps1
  have hnn : 0 ≤ deltaQld A (B / 2) epsilon P.m P.d P.q := by
    have := zero_le_one.trans hA; simp only [deltaQld, Real.rpow_eq_pow]; positivity
  have herr := herror P epsilon heps0 heps1
  have hid : reindexState (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
      (S.idealExpState v.aux) = idealState P v.toPauliSoundnessWitness.aux := by ext; rfl
  refine ⟨v.toPauliSoundnessWitness, ?_, fun W => ?_, fun W => ?_⟩
  · exact (((Real.le_sqrt_of_sq_le hst_sq).trans (Real.sqrt_le_sqrt herr)).trans
      (sqrt_deltaQld_le hA heps0)).trans
      ((le_mul_of_one_le_left hnn (by norm_num : (1 : ℝ) ≤ 4)).trans hfour)
  · have h1 := sum_norm_leftTensor_conjIsometry_sub_sq_le v.toPauliSoundnessWitness.φA
      v.toPauliSoundnessWitness.φB
      (S.pauliMeas .alice W).effect (S.swappedPauliMeas w .alice W) (pauliProjOnA'' P W)
      (fun h => unitaryAncillaIsometry_intertwines _ (eprState_norm _) _
        (v.swap_left_unitary .alice) _) S.toStrategy.ψ (idealState P v.toPauliSoundnessWitness.aux)
    have hextr (h) : S.placeExtractedRegister .alice (pauliProj W h) =
        reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (pauliProjOnA'' P (ιA' := S.toStrategy.ιA × PauliRegister P)
            (ιB' := S.toStrategy.ιB × PauliRegister P) W h) := by
      ext i j
      change (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 * (1 : Op _) i.1.2.1 j.1.2.1 *
        ((1 : Op S.toStrategy.ιB) i.2.1 j.2.1 * pauliProj W h i.1.2.2 j.1.2.2) *
        (1 : Op _) i.2.2.1 j.2.2.1 * (1 : Op _) i.2.2.2 j.2.2.2 = _
      simp [sixRegExtractionEquiv, pauliProjOnA'', Matrix.one_apply, mul_ite, ite_mul]
      split_ifs <;> simp_all
    have hcl := v.pauli_close .alice W
    rw [opFamilyDistSq_uniform_unit] at hcl
    simp_rw [← S.placeSide_swappedPauliMeas w .alice W, ProjectiveSetting.placeSide,
      hextr, ← WinImplications.reindexOp_sub,
      ← WinImplications.norm_applyOperatorToState_reindexState] at hcl
    rw [hid] at hcl
    have heq : pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W = _ :=
      Finset.sum_congr rfl fun u _ =>
        congrArg (fun O => ‖applyOperatorToState (O - _) _‖ ^ 2) (liftedAEffect_eq_tensor _ _ _)
    rw [heq]; rw [norm_sub_rev] at h1
    exact ((h1.trans (two_mul_add_two_mul_le hcl hst_sq)).trans
      (mul_le_mul_of_nonneg_left (herr.trans hmono) (by norm_num))).trans hfour
  · have h1 := sum_norm_rightTensor_conjIsometry_sub_sq_le v.toPauliSoundnessWitness.φA
      v.toPauliSoundnessWitness.φB
      (S.pauliMeas .bob W).effect (S.swappedPauliMeas w .bob W) (pauliProjOnB'' P W)
      (fun h => unitaryAncillaIsometry_intertwines _ (eprState_norm _) _
        (v.swap_left_unitary .bob) _) S.toStrategy.ψ (idealState P v.toPauliSoundnessWitness.aux)
    have hextr (h) : S.placeExtractedRegister .bob (pauliProj W h) =
        reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (pauliProjOnB'' P (ιA' := S.toStrategy.ιA × PauliRegister P)
            (ιB' := S.toStrategy.ιB × PauliRegister P) W h) := by
      ext i j
      change ((1 : Op S.toStrategy.ιA) i.1.1 j.1.1 * pauliProj W h i.2.2.2 j.2.2.2) *
        (1 : Op _) i.1.2.1 j.1.2.1 * (1 : Op _) i.1.2.2 j.1.2.2 *
        (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 * (1 : Op _) i.2.2.1 j.2.2.1 = _
      simp [sixRegExtractionEquiv, pauliProjOnB'', Matrix.one_apply, mul_ite, ite_mul]
      split_ifs <;> simp_all
    have hcl := v.pauli_close .bob W
    rw [opFamilyDistSq_uniform_unit] at hcl
    simp_rw [← S.placeSide_swappedPauliMeas w .bob W, ProjectiveSetting.placeSide,
      hextr, ← WinImplications.reindexOp_sub,
      ← WinImplications.norm_applyOperatorToState_reindexState] at hcl
    rw [hid] at hcl
    have heq : pauliOperatorDistanceB P S.toStrategy v.toPauliSoundnessWitness W = _ :=
      Finset.sum_congr rfl fun u _ =>
        congrArg (fun O => ‖applyOperatorToState (O - _) _‖ ^ 2) (liftedBEffect_eq_tensor _ _ _)
    rw [heq]; rw [norm_sub_rev] at h1
    exact ((h1.trans (two_mul_add_two_mul_le hcl hst_sq)).trans
      (mul_le_mul_of_nonneg_left (herr.trans hmono) (by norm_num))).trans hfour

/-! ### Player-swap symmetry and Naimark dilation -/

@[reducible] def pauliStrategySwap (P : AdmissibleParams) (S : Strategy (pauliBasisTest P)) :
    Strategy (pauliBasisTest P) where
  ιA := S.ιB
  ιB := S.ιA
  ψ := reindexState (Equiv.prodComm S.ιA S.ιB) S.ψ
  ψ_norm := (reindexState_norm_eq _ S.ψ).trans S.ψ_norm
  A := S.B
  B := S.A

theorem pauliStrategySwap_value (P : AdmissibleParams) (S : Strategy (pauliBasisTest P)) :
    (pauliStrategySwap P S).value = S.value := by
  classical
  have hout (x y : PauliQuestion P) (a b : PauliAnswer P) :
      outcomeWeight (pauliStrategySwap P S) x y a b = outcomeWeight S y x b a := by
    let e := Equiv.prodComm S.ιA S.ιB
    have hact : applyOperatorToState (heteroKron ((S.B x).effect a) ((S.A y).effect b))
        (reindexState e S.ψ) = reindexState e (applyOperatorToState
          (heteroKron ((S.A y).effect b) ((S.B x).effect a)) S.ψ) := by
      rw [← WinImplications.reindexOp_prodComm_heteroKron ((S.A y).effect b) ((S.B x).effect a)]
      ext k; exact WinImplications.applyOperatorToState_reindexState_ofLp e _ S.ψ k
    unfold outcomeWeight pauliStrategySwap; dsimp only [e] at hact ⊢
    rw [hact, EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    exact congrArg Complex.re (e.symm.sum_comp fun i =>
      (applyOperatorToState (heteroKron ((S.A y).effect b) ((S.B x).effect a)) S.ψ).ofLp i *
        star (S.ψ.ofLp i))
  unfold Strategy.value avgOver
  have hsup (f : (pauliBasisTest P).QuestionA × (pauliBasisTest P).QuestionB → ℝ) :
      ∑ xy ∈ (pauliBasisTest P).μ.support, (pauliBasisTest P).μ.weight xy * f xy =
      ∑ xy, (pauliBasisTest P).μ.weight xy * f xy :=
    Finset.sum_subset (Finset.subset_univ _) fun xy _ hxy => by
      rw [((pauliBasisTest P).μ).outsideSupport xy hxy, zero_mul]
  rw [hsup, hsup]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun ⟨x, y⟩ => ?_
  change (pauliQuestionDistribution P).weight (x, y) *
      (∑ a, ∑ b, if pauliWinPredicate P x y a b then outcomeWeight (pauliStrategySwap P S) x y a b else 0) =
    (pauliQuestionDistribution P).weight (y, x) *
      (∑ a, ∑ b, if pauliWinPredicate P y x a b then outcomeWeight S y x a b else 0)
  rw [pauliQuestionDistribution_symm P x y]
  congr 1; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  by_cases hw : pauliWinPredicate P y x b a <;>
    simp [pauliWinPredicate_symm P x y a b, hw, hout]

@[reducible] def pauliWitnessSwap {P : AdmissibleParams} {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P S) : PauliSoundnessWitness P (pauliStrategySwap P S) where
  ιA' := w.ιB'
  ιB' := w.ιA'
  φA := w.φB
  φB := w.φA
  aux := reindexState (Equiv.prodComm w.ιA' w.ιB') w.aux
  aux_norm := (reindexState_norm_eq _ w.aux).trans w.aux_norm

private theorem isometryTensor_swap_eq {ιA ιB κA κB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor φB φA (reindexState (Equiv.prodComm ιA ιB) ψ) =
      reindexState (Equiv.prodComm κA κB) (isometryTensor φA φB ψ) := by
  ext ⟨pB, pA⟩
  change (∑ j, ∑ i,
      (EuclideanSpace.equiv κB ℂ) (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) pB *
        (EuclideanSpace.equiv κA ℂ) (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) pA *
        (EuclideanSpace.equiv (ιA × ιB) ℂ) ψ (i, j)) =
    ∑ i, ∑ j,
      (EuclideanSpace.equiv κA ℂ) (φA ((EuclideanSpace.equiv ιA ℂ).symm (Pi.single i 1))) pA *
        (EuclideanSpace.equiv κB ℂ) (φB ((EuclideanSpace.equiv ιB ℂ).symm (Pi.single j 1))) pB *
        (EuclideanSpace.equiv (ιA × ιB) ℂ) ψ (i, j)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem idealState_swap_eq (P : AdmissibleParams) {ιA' ιB' : Type*}
    [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) :
    idealState P (reindexState (Equiv.prodComm ιA' ιB') aux) =
      reindexState (Equiv.prodComm (ιA' × PauliRegister P) (ιB' × PauliRegister P))
        (idealState P aux) := by
  ext ⟨pB, pA⟩; simp [idealState, reindexState, eprState, eq_comm]

private theorem pauliWitnessSwap_state_eq {P : AdmissibleParams} (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) :
    ‖isometryTensor (pauliWitnessSwap w).φA (pauliWitnessSwap w).φB (pauliStrategySwap P S).ψ -
      idealState P (pauliWitnessSwap w).aux‖ =
    ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ := by
  dsimp only [pauliWitnessSwap, pauliStrategySwap]
  rw [isometryTensor_swap_eq, idealState_swap_eq,
    show reindexState _ _ - reindexState _ _ = reindexState _ (_ - _) from rfl,
    reindexState_norm_eq]

private theorem pauliDistanceSwap_eq {P : AdmissibleParams} (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P S) (f : PauliRegister P → Op S.ιB) (W : PauliKind) :
    (∑ u, ‖applyOperatorToState
        (liftedAEffect (pauliStrategySwap P S) (pauliWitnessSwap w).φA (f u) -
          pauliProjOnA'' P W u) (idealState P (pauliWitnessSwap w).aux)‖ ^ 2) =
      ∑ u, ‖applyOperatorToState (liftedBEffect S w.φB (f u) - pauliProjOnB'' P W u)
        (idealState P w.aux)‖ ^ 2 := by
  refine Finset.sum_congr rfl fun u _ => congrArg (· ^ 2) ?_
  dsimp only [pauliWitnessSwap]
  rw [idealState_swap_eq, WinImplications.norm_applyOperatorToState_reindexState]
  congr 2
  ext r c
  simp [reindexOp, liftedAEffect, liftedBEffect, pauliProjOnA'', pauliProjOnB'', and_comm]

@[reducible] def pauliNaimarkStrategy (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) : Strategy (pauliBasisTest P) :=
  paddedStrategy S (none : Option (PauliAnswer P)) (none : Option (PauliAnswer P))
    (fun q => dilatedMeasurement default (S.A q)) (fun q => dilatedMeasurement default (S.B q))

@[reducible] def pauliNaimarkWitness (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) : PauliSoundnessWitness P S where
  ιA' := w.ιA'
  ιB' := w.ιB'
  φA := w.φA.comp (naimarkEmbedding S.ιA (PauliAnswer P))
  φB := w.φB.comp (naimarkEmbedding S.ιB (PauliAnswer P))
  aux := w.aux
  aux_norm := w.aux_norm

@[reducible] private def pauliNaimarkWitnessSwap {P : AdmissibleParams}
    {S : Strategy (pauliBasisTest P)}
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    PauliSoundnessWitness P (pauliNaimarkStrategy P (pauliStrategySwap P S)) where
  ιA' := w.ιB'
  ιB' := w.ιA'
  φA := w.φB
  φB := w.φA
  aux := reindexState (Equiv.prodComm w.ιA' w.ιB') w.aux
  aux_norm := (reindexState_norm_eq _ w.aux).trans w.aux_norm

private theorem pauliNaimarkStrategy_state (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P)) :
    (pauliNaimarkStrategy P S).ψ = isometryTensor
      (naimarkEmbedding S.ιA (PauliAnswer P)) (naimarkEmbedding S.ιB (PauliAnswer P)) S.ψ := by
  change padState none none S.ψ = naimarkDilatedState (PauliAnswer P) S.ψ
  ext p; rw [naimarkDilatedState_apply]; simp only [padState, EuclideanSpace.equiv]
  by_cases hA : p.1.2 = none <;> by_cases hB : p.2.2 = none <;> simp [hA, hB]

theorem pauli_naimark_witness_state_distance_eq (P : AdmissibleParams)
    (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) :
    ‖isometryTensor (pauliNaimarkWitness P S w).φA (pauliNaimarkWitness P S w).φB S.ψ -
      idealState P (pauliNaimarkWitness P S w).aux‖ =
    ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ - idealState P w.aux‖ := by
  rw [pauliNaimarkStrategy_state, ← isometryTensor_comp]

private theorem sum_norm_compression_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N T R : α → Op ι) (Q : Op ι) (hQ : IsProj Q)
    (hN : ∑ a, (N a)ᴴ * N a ≤ 1) (hR : ∑ a, (R a)ᴴ * R a ≤ 1)
    (theta delta : EuclideanSpace ℂ ι)
    (hfix : applyOperatorToState Q theta = theta)
    (hmirror : ∀ a, applyOperatorToState (T a) delta = applyOperatorToState (R a) delta)
    (hcomm : ∀ a, Q * R a = R a * Q) :
    ∑ a, ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
      3 * (∑ a, ‖applyOperatorToState (N a - T a) delta‖ ^ 2) + 6 * ‖delta - theta‖ ^ 2 := by
  have hcontr (v) : ‖applyOperatorToState Q v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_applyOperatorToState_le (conjTranspose_mul_le_one_of_isProj hQ) v) 2
  have hvan : applyOperatorToState (1 - Q) theta = 0 := by
    simp [applyOperatorToState, show Matrix.toEuclideanLin Q theta = theta from hfix]
  have hrng : ‖applyOperatorToState (1 - Q) delta‖ ^ 2 ≤ ‖delta - theta‖ ^ 2 := by
    have h := norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    rw [applyOperatorToState_sub, hvan, sub_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hn := (sum_norm_mul_apply_le N (1 - Q) delta hN).trans hrng
  have hr := (sum_norm_mul_apply_le R (1 - Q) delta hR).trans hrng
  have hpt (a) : ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
      3 * (‖applyOperatorToState (N a - T a) delta‖ ^ 2 +
        ‖applyOperatorToState (N a * (1 - Q)) delta‖ ^ 2 +
        ‖applyOperatorToState (R a * (1 - Q)) delta‖ ^ 2) := by
    have hs : Q * N a * Q - T a = Q * (N a - T a) - Q * (N a * (1 - Q)) - (1 - Q) * T a := by
      noncomm_ring
    have hm : applyOperatorToState ((1 - Q) * T a) delta =
        applyOperatorToState (R a * (1 - Q)) delta := by
      rw [applyOperatorToState_mul, hmirror, ← applyOperatorToState_mul]
      congr 1; rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
    rw [hs, applyOperatorToState_sub_op, applyOperatorToState_sub_op, hm,
      applyOperatorToState_mul, applyOperatorToState_mul]
    set x := applyOperatorToState Q (applyOperatorToState (N a - T a) delta)
    set y := applyOperatorToState Q (applyOperatorToState (N a * (1 - Q)) delta)
    set z := applyOperatorToState (R a * (1 - Q)) delta
    have htri : ‖x - y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by linarith [norm_sub_le (x - y) z, norm_sub_le x y]
    have h3 : ‖x - y - z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) htri 2,
        sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖), sq_nonneg (‖y‖ - ‖z‖)]
    exact h3.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hcontr _) (hcontr _)) le_rfl) (by norm_num))
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpt a
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith

set_option maxHeartbeats 800000 in
-- Finite-register matrix algebra and nested finite sums.
theorem pauli_naimark_operator_distanceA_le
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind) :
    pauliOperatorDistanceA P S (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ - idealState P w.aux‖ ^ 2 := by
  let Q := liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
    (groundProjection S.ιA (PauliAnswer P))
  have hQ : IsProj Q := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor]
    exact MakingMeasurementsProjective.isProj_kronecker
      (conjIsometry_isProj w.φA (isProj_groundProjection _ _)) (.one _)
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor, applyOperatorToState_leftTensor_conjIsometry]
    congr 1
    change applyOperatorToState _ (padState none none S.ψ) = padState none none S.ψ
    rw [show padState (none : Option (PauliAnswer P)) (none : Option (PauliAnswer P)) S.ψ =
      naimarkDilatedState (PauliAnswer P) S.ψ from pauliNaimarkStrategy_state P S]
    exact applyOperatorToState_leftTensor_groundProjection (PauliAnswer P) S.ψ
  have hcomm (h) : Q * pauliProjOnB'' P W h = pauliProjOnB'' P W h * Q := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor, pauliProjOnB_eq_tensor]
    simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have hN : ∑ a, (liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
      ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect a))ᴴ *
      liftedAEffect (pauliNaimarkStrategy P S) w.φA
      ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect a) ≤ 1 := by
    let M := ((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess pauliAnswerOrZero
    have hM := measurement_sum_adjoint_mul_le_one M
    have hcj : ∑ a, (conjIsometry w.φA (M.effect a))ᴴ * conjIsometry w.φA (M.effect a) ≤ 1 := by
      have heq (a) : (conjIsometry w.φA (M.effect a))ᴴ * conjIsometry w.φA (M.effect a) =
          isometryMatrix w.φA * ((M.effect a)ᴴ * M.effect a) * (isometryMatrix w.φA)ᴴ := by
        simp only [conjIsometry_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (isometryMatrix w.φA)ᴴ (isometryMatrix w.φA),
          isometryMatrix_conjTranspose_mul, Matrix.one_mul]
      simp_rw [heq]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      refine le_trans ?_ (isometryMatrix_mul_conjTranspose_le_one w.φA)
      rw [Matrix.le_iff]
      convert (Matrix.le_iff.mp hM).mul_mul_conjTranspose_same (isometryMatrix w.φA) using 1
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp_rw [liftedAEffect_eq_tensor]
    change ∑ a, (leftTensor (ι₂ := w.ιB' × PauliRegister P) (conjIsometry w.φA (M.effect a)))ᴴ *
      leftTensor (conjIsometry w.φA (M.effect a)) ≤ 1
    simpa only [← leftTensor_finset_sum, leftTensor_one, leftTensor_conjTranspose,
      leftTensor_mul_leftTensor] using leftTensor_mono (ι₂ := w.ιB' × PauliRegister P) hcj
  have hR : ∑ h, (pauliProjOnB'' P (ιA' := w.ιA') (ιB' := w.ιB') W h)ᴴ *
      pauliProjOnB'' P W h ≤ 1 := by
    simp only [pauliProjOnB_eq_tensor]
    exact measurement_sum_adjoint_mul_le_one (rightPlacedMeasurement (rightPlacedMeasurement
      (Measurement.ofSumEqOne (pauliProj W) (fun h => (posSemidef_pauliProj W h).nonneg)
        (sum_pauliProj_eq_one W))))
  have hmir (h) : applyOperatorToState (pauliProjOnA'' P W h) (idealState P w.aux) =
      applyOperatorToState (pauliProjOnB'' P W h) (idealState P w.aux) := by
    have htr (M : Op (PauliRegister P)) :
        applyOperatorToState (heteroKron (heteroKron 1 M) 1) (idealState P w.aux) =
          applyOperatorToState (heteroKron 1 (heteroKron 1 Mᵀ)) (idealState P w.aux) := by
      ext p; simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker, Matrix.one_apply,
        idealState, eprState, Fintype.sum_prod_type, mul_comm]
    rw [pauliProjOnA_eq_tensor, pauliProjOnB_eq_tensor]
    simpa only [pauliProj_transpose] using htr (pauliProj W h)
  have hb := sum_norm_compression_sub_sq_le _ (pauliProjOnA'' P W) (pauliProjOnB'' P W)
    Q hQ hN hR _ (idealState P w.aux) hfix hmir hcomm
  rw [norm_sub_rev] at hb
  refine (le_of_eq (Finset.sum_congr rfl fun h _ => ?_)).trans hb
  have hc : (((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).compressAt none =
      (S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero := by
    change ((dilatedMeasurement (default : PauliAnswer P) _).postprocess _).compressAt none = _
    rw [Measurement.compressAt_postprocess, Measurement.compressAt_dilatedMeasurement]
  have heff : naimarkCompression ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
      pauliAnswerOrZero).effect h) = (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) :=
    congrArg (fun M => M.effect h) hc
  have hcomp : liftedAEffect S (ιB' := w.ιB') (pauliNaimarkWitness P S w).φA
      (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) =
      Q * liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
        ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) * Q := by
    dsimp only [Q, pauliNaimarkWitness]
    simp only [liftedAEffect_eq_tensor, ← heff, conjIsometry_comp_naimarkEmbedding,
      naimarkInflation_naimarkCompression, conjIsometry_mul, heteroKron_mul, Matrix.one_mul]
  exact congrArg (fun M => ‖applyOperatorToState (M - pauliProjOnA'' P W h) (idealState P w.aux)‖ ^ 2) hcomp

set_option maxHeartbeats 400000 in
-- Swaps Alice and Bob on the Naimark-dilated strategy.
theorem pauli_naimark_operator_distanceB_le
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind) :
    pauliOperatorDistanceB P S (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ - idealState P w.aux‖ ^ 2 := by
  let S' := pauliStrategySwap P S
  let w' := pauliNaimarkWitnessSwap w
  have hA := pauli_naimark_operator_distanceA_le P S' w' W
  have h1 : pauliOperatorDistanceA P S' (pauliNaimarkWitness P S' w') W =
      pauliOperatorDistanceB P S (pauliNaimarkWitness P S w) W :=
    pauliDistanceSwap_eq S (pauliNaimarkWitness P S w) _ W
  have h2 : pauliOperatorDistanceA P (pauliNaimarkStrategy P S') w' W =
      pauliOperatorDistanceB P (pauliNaimarkStrategy P S) w W :=
    pauliDistanceSwap_eq (pauliNaimarkStrategy P S) w _ W
  have hp : (pauliNaimarkStrategy P S').ψ =
      reindexState (Equiv.prodComm _ _) (pauliNaimarkStrategy P S).ψ := by
    ext ⟨pB, pA⟩
    dsimp only [S', pauliNaimarkStrategy, paddedStrategy, padState, pauliStrategySwap, reindexState]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    by_cases ha : pA.2 = none <;> by_cases hb : pB.2 = none <;> simp [ha, hb]
  have h3 : ‖isometryTensor w'.φA w'.φB (pauliNaimarkStrategy P S').ψ - idealState P w'.aux‖ =
      ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ - idealState P w.aux‖ := by
    rw [hp]; exact pauliWitnessSwap_state_eq (pauliNaimarkStrategy P S) w
  rwa [h1, h2, h3] at hA

/-! ### Scalar absorption and completed-to-raw Pauli transfer -/

theorem deltaQld_nonneg {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 0 ≤ a) (hepsilon : 0 ≤ epsilon) :
    0 ≤ deltaQld a b epsilon P.m P.d P.q := by
  unfold deltaQld; simp only [Real.rpow_eq_pow]
  refine mul_nonneg (mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg _) a)) ?_
  linarith [Real.rpow_nonneg hepsilon b, Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b),
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(b * ((P.m * P.d : ℕ) : ℝ)))]

theorem three_add_six_sq_deltaQld_le {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * deltaQld a b epsilon P.m P.d P.q + 6 * deltaQld a b epsilon P.m P.d P.q ^ 2 ≤
      deltaQld (21 * a ^ 2) b epsilon P.m P.d P.q := by
  have hdeg : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hdeg0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := zero_le_one.trans hdeg
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨k, -, hk⟩ := P.hq; rw [hk]; exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha
  have hpref : (1 : ℝ) ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hdeg ha0)
  let tail := epsilon ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ)))
  have htail0 : 0 ≤ tail := by
    dsimp [tail]; linarith [Real.rpow_nonneg hepsilon b,
      Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(b * ((P.m * P.d : ℕ) : ℝ)))]
  have htail3 : tail ≤ 3 := by
    dsimp [tail]
    linarith [Real.rpow_le_one hepsilon hepsilon1 hb.le,
      Real.rpow_le_one_of_one_le_of_nonpos hq (neg_nonpos.mpr hb.le),
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
        (neg_nonpos.mpr (mul_nonneg hb.le hdeg0))]
  have hnn := deltaQld_nonneg (P := P) (b := b) ha0 hepsilon
  have hub : deltaQld a b epsilon P.m P.d P.q ≤ 3 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) := by
    unfold deltaQld; simp only [Real.rpow_eq_pow]
    nlinarith [mul_nonneg (zero_le_one.trans hpref) (sub_nonneg.mpr htail3)]
  have hstep1 : 3 * deltaQld a b epsilon P.m P.d P.q + 6 * deltaQld a b epsilon P.m P.d P.q ^ 2 ≤
      21 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) * deltaQld a b epsilon P.m P.d P.q := by
    nlinarith [mul_nonneg hnn (sub_nonneg.mpr hub), mul_nonneg hnn (sub_nonneg.mpr hpref)]
  refine hstep1.trans ?_
  unfold deltaQld; simp only [Real.rpow_eq_pow]
  have hpow : ((P.m * P.d : ℕ) : ℝ) ^ (a + a) ≤ ((P.m * P.d : ℕ) : ℝ) ^ (21 * a ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hdeg (by nlinarith)
  rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hdeg)] at hpow
  calc 21 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) * (a * ((P.m * P.d : ℕ) : ℝ) ^ a * tail)
      = 21 * a ^ 2 * (((P.m * P.d : ℕ) : ℝ) ^ a * ((P.m * P.d : ℕ) : ℝ) ^ a) * tail := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) htail0

theorem raw_pauli_operator_distanceA_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ) (W : PauliKind) :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA P S w W + 4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
  classical
  let _ : Nonempty PauliEdge := pauliEdge_nonempty
  let M := S.A (pauliQuestion P W)
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  have hcomp (u : PauliRegister P) : (M.postprocess pauliAnswerOrZero).effect u =
      M.effect (.pauliOutcome u) + if u = 0 then E else 0 := by
    dsimp only [E]; rw [Measurement.postprocess_effect, ProjectiveSetting.wrongFormEffect, Finset.sum_filter]
    by_cases hu : u = 0
    · subst u; simp only [ite_true]
      calc (∑ ans, if pauliAnswerOrZero ans = 0 then M.effect ans else 0)
          = ∑ ans, ((if ans = .pauliOutcome 0 then M.effect ans else 0) +
              (if validPauliAnswer (.pauli W) ans = false then M.effect ans else 0)) :=
            Finset.sum_congr rfl fun ans _ => by cases ans <;> simp [pauliAnswerOrZero, validPauliAnswer] <;> rfl
        _ = _ := by
            rw [Finset.sum_add_distrib]
            congr 1; · simp
            · rw [← Finset.sum_filter]
    · simp only [hu, ite_false, add_zero]
      rw [Finset.sum_eq_single (.pauliOutcome u)]
      · simp [pauliAnswerOrZero]
      · intro ans _ hans
        have h0 : (0 : PauliRegister P) ≠ u := Ne.symm hu
        cases ans <;> simp_all [pauliAnswerOrZero]
      · simp
  have hmass : stateQForm S.ψ (heteroKron E 1) ≤ (Fintype.card PauliEdge : ℝ) * ε := by
    have hpt (z : PauliSpace P) : stateQForm S.ψ (heteroKron E 1) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W) z := by
      have hm : stateQForm S.ψ (heteroKron E 1) =
          aliceEventWeight S (pauliQuestion P W) (fun a => validPauliAnswer (.pauli W) a = false) := by
        dsimp [E, M]; unfold ProjectiveSetting.wrongFormEffect aliceEventWeight
        rw [DistanceCalculus.heteroKron_finset_sum_left, DistanceCalculus.stateQForm_finset_sum,
          Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : validPauliAnswer (.pauli W) a = false <;> simp [ha, stateQForm, aliceOutcomeWeight]
      rw [hm, ← outcome_event_weight_left_eq S (pauliQuestion P W) ((.point W), pauliCL P (.point W) z)]
      unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
      dsimp only [WinImplications.pauliPointEdge, pauliCL, pauliQuestion]
      exact outcome_event_weight_mono S _ _ _ _ fun a b ha => by simp [pauliWinPredicate, ha]
    have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => WinImplications.pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
      rw [← WinImplications.rejectionEventAverage_eq_one_sub_value S]
      unfold pauliBasisTest pauliQuestionDistribution; rw [Distribution.avgOver_map]; rfl
    calc stateQForm S.ψ (heteroKron E 1)
        = avgOver (uniformDistribution (PauliSpace P)) (fun _ => stateQForm S.ψ (heteroKron E 1)) :=
          (avgOver_uniform_const _).symm
      _ ≤ avgOver (uniformDistribution (PauliSpace P))
          (WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W)) :=
          avgOver_mono _ _ _ hpt
      _ ≤ (Fintype.card PauliEdge : ℝ) * avgOver (uniformDistribution (PauliEdge × PauliSpace P))
          (fun ez => WinImplications.pauliRejectionAt S ez.1 ez.2) :=
          WinImplications.avgOver_uniform_fixed_le_card_mul_prod _
            (fun e z => WinImplications.pauliRejectionAt_nonneg S e z) _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  let Q := liftedAEffect S (ιB' := w.ιB') w.φA E
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hEN : E = N.effect false := rfl
  have hQcontr : Qᴴ * Q ≤ 1 := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor, hEN]
    exact conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_conjIsometry w.φA
      (conjTranspose_mul_le_one_of_effect N false))
  have htheta : ‖applyOperatorToState Q (isometryTensor w.φA w.φB S.ψ)‖ ^ 2 ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor, applyOperatorToState_leftTensor_conjIsometry,
      norm_isometryTensor, norm_applyOperatorToState_sq]
    have hKpos : 0 ≤ heteroKron E (1 : Op S.ιB) := kronecker_nonneg (hEN ▸ N.pos false) (by simp)
    have hKle : heteroKron E (1 : Op S.ιB) ≤ 1 := by
      rw [← Matrix.one_kronecker_one, hEN]
      exact kronecker_mono_left (measurement_effect_le_one N false) (by simp)
    rw [(Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans hmass
  let bad := ‖applyOperatorToState Q (idealState P w.aux)‖ ^ 2
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
    dsimp only [bad]
    rw [show applyOperatorToState Q (idealState P w.aux) =
      applyOperatorToState Q (idealState P w.aux - isometryTensor w.φA w.φB S.ψ) +
        applyOperatorToState Q (isometryTensor w.φA w.φB S.ψ) by simp [applyOperatorToState]]
    have hf : ‖applyOperatorToState Q (idealState P w.aux - isometryTensor w.φA w.φB S.ψ)‖ ≤ δ :=
      (norm_applyOperatorToState_le hQcontr _).trans (by rwa [norm_sub_rev])
    have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le
      (applyOperatorToState Q (idealState P w.aux - isometryTensor w.φA w.φB S.ψ))
      (applyOperatorToState Q (isometryTensor w.φA w.φB S.ψ))) 2
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hf 2,
      sq_nonneg (‖applyOperatorToState Q (idealState P w.aux - isometryTensor w.φA w.φB S.ψ)‖ -
        ‖applyOperatorToState Q (isometryTensor w.φA w.φB S.ψ)‖)]
  have hpt (u : PauliRegister P) :
      ‖applyOperatorToState (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) -
          pauliProjOnA'' P W u) (idealState P w.aux)‖ ^ 2 ≤
        2 * ‖applyOperatorToState (liftedAEffect S w.φA
            ((M.postprocess pauliAnswerOrZero).effect u) - pauliProjOnA'' P W u)
          (idealState P w.aux)‖ ^ 2 + if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u; rw [ite_eq_left_iff.mpr fun h => absurd rfl h, hcomp 0]; simp only [ite_true]
      have hadd : liftedAEffect S (ιB' := w.ιB') w.φA (M.effect (.pauliOutcome 0) + E) =
          liftedAEffect S w.φA (M.effect (.pauliOutcome 0)) + Q := by
        dsimp only [Q]
        rw [liftedAEffect_eq_tensor, liftedAEffect_eq_tensor, liftedAEffect_eq_tensor, ← heteroKron_add_left]
        congr 1; simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]
      have hv : applyOperatorToState (liftedAEffect S w.φA (M.effect (.pauliOutcome 0)) -
          pauliProjOnA'' P W 0) (idealState P w.aux) =
        applyOperatorToState (liftedAEffect S w.φA (M.effect (.pauliOutcome 0) + E) -
          pauliProjOnA'' P W 0) (idealState P w.aux) - applyOperatorToState Q (idealState P w.aux) := by
        rw [hadd]; simp [applyOperatorToState]; abel
      rw [hv]; dsimp only [bad]
      have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
        (applyOperatorToState (liftedAEffect S w.φA (M.effect (.pauliOutcome 0) + E) -
          pauliProjOnA'' P W 0) (idealState P w.aux))
        (applyOperatorToState Q (idealState P w.aux))) 2
      nlinarith [sq_nonneg (‖applyOperatorToState (liftedAEffect S w.φA
        (M.effect (.pauliOutcome 0) + E) - pauliProjOnA'' P W 0) (idealState P w.aux)‖ -
        ‖applyOperatorToState Q (idealState P w.aux)‖)]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hu, hcomp u]
      simp only [hu, ite_false, add_zero]
      nlinarith [sq_nonneg ‖applyOperatorToState
        (liftedAEffect S w.φA (M.effect (.pauliOutcome u)) - pauliProjOnA'' P W u)
        (idealState P w.aux)‖]
  unfold rawPauliOperatorDistanceA pauliOperatorDistanceA
  have hs := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hpt u
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hs
  linarith

theorem raw_pauli_operator_distanceB_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ) (W : PauliKind) :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB P S w W + 4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let S' := pauliStrategySwap P S
  let w' := pauliWitnessSwap w
  have hwin' : 1 - ε ≤ S'.value := by rwa [pauliStrategySwap_value]
  have hst' : ‖isometryTensor w'.φA w'.φB S'.ψ - idealState P w'.aux‖ ≤ δ :=
    (pauliWitnessSwap_state_eq S w).trans_le hstate
  have hA := raw_pauli_operator_distanceA_le_completed S' hwin' w' hst' W
  unfold rawPauliOperatorDistanceA pauliOperatorDistanceA at hA
  unfold rawPauliOperatorDistanceB pauliOperatorDistanceB
  dsimp only [S', w'] at hA
  rwa [pauliDistanceSwap_eq S w (fun u => (S.B (pauliQuestion P W)).effect (.pauliOutcome u)) W,
    pauliDistanceSwap_eq S w (fun u => ((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) W] at hA

theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤
                deltaQld a b ε P.m P.d P.q ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceA P S w W ≤ deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : PauliKind,
              rawPauliOperatorDistanceB P S w W ≤ deltaQld a b ε P.m P.d P.q) := by
  obtain ⟨a₀, b, ha₀, hb, hb1, hproj⟩ := exists_projective_setting_isometry_bounds
  let a := 21 * a₀ ^ 2
  have ha : 1 ≤ a := by dsimp [a]; nlinarith [sq_nonneg a₀]
  have ha₀a : a₀ ≤ a := by dsimp [a]; nlinarith [sq_nonneg a₀]
  let K : ℝ := 2 + 4 * (Fintype.card PauliEdge : ℝ)
  have hK : 1 ≤ K := by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card PauliEdge)]
  let A := K * (21 * a ^ 2)
  have h21a : 1 ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have haA : a ≤ A := by
    have : a ≤ 21 * a ^ 2 := by nlinarith [sq_nonneg a]
    exact this.trans (le_mul_of_one_le_left (by positivity) hK)
  have hsmall (P : AdmissibleParams) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
      (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) :
      ∃ w : PauliSoundnessWitness P S,
        ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ deltaQld A b ε P.m P.d P.q ∧
        (∀ W, rawPauliOperatorDistanceA P S w W ≤ deltaQld A b ε P.m P.d P.q) ∧
        (∀ W, rawPauliOperatorDistanceB P S w W ≤ deltaQld A b ε P.m P.d P.q) := by
    have hwinN : 1 - ε ≤ (pauliNaimarkStrategy P S).value := by
      rwa [paddedStrategy_value S none none _ _
        (fun _ _ => dilatedMeasurement_compression default _ _)
        (fun _ _ => dilatedMeasurement_compression default _ _)]
    have hprojN : (pauliNaimarkStrategy P S).IsProjective :=
      paddedStrategy_isProjective S none none _ _
        (fun _ => dilatedMeasurement_isProjective default _)
        (fun _ => dilatedMeasurement_isProjective default _)
    obtain ⟨t, hst0, hA0, hB0⟩ := hproj P ε hε0 hε1 ⟨pauliNaimarkStrategy P S, hprojN, hwinN⟩
    dsimp only at t hst0 hA0 hB0
    let w := pauliNaimarkWitness P S t
    let d₀ := deltaQld a₀ b ε P.m P.d P.q
    let d := deltaQld a b ε P.m P.d P.q
    have hd₀d : d₀ ≤ d := deltaQld_mono ha₀ ha₀a le_rfl hb hε0 hε1
    have hst : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ d :=
      ((pauli_naimark_witness_state_distance_eq P S t).trans_le hst0).trans hd₀d
    have hsq0 : ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ - idealState P t.aux‖ ^ 2 ≤ d₀ ^ 2 := by
      nlinarith [norm_nonneg (isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ - idealState P t.aux)]
    have habs0 : 3 * d₀ + 6 * d₀ ^ 2 ≤ d := three_add_six_sq_deltaQld_le ha₀ hb hε0 hε1
    have hcA (W) : pauliOperatorDistanceA P S w W ≤ d :=
      (pauli_naimark_operator_distanceA_le P S t W).trans (by linarith [hA0 W])
    have hcB (W) : pauliOperatorDistanceB P S w W ≤ d :=
      (pauli_naimark_operator_distanceB_le P S t W).trans (by linarith [hB0 W])
    have hεd : ε ≤ d := by
      have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
      have hpref : 1 ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
        one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hmd (zero_le_one.trans ha))
      have hεp : ε ≤ ε ^ b := by simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb.le hb1.le
      have hq0 := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
      have h20 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(b * ((P.m * P.d : ℕ) : ℝ)))
      dsimp [d, deltaQld]
      nlinarith [hq0, h20, mul_nonneg (sub_nonneg.mpr hpref)
        (add_nonneg (add_nonneg (Real.rpow_nonneg hε0 b) hq0) h20)]
    have habs : 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε ≤
        deltaQld A b ε P.m P.d P.q := by
      have hd_nn := deltaQld_nonneg (P := P) (b := b) (zero_le_one.trans ha) hε0
      have hc_nn : (0 : ℝ) ≤ Fintype.card PauliEdge := Nat.cast_nonneg _
      have h1 : 2 * d + 4 * d ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε ≤ K * (3 * d + 6 * d ^ 2) := by
        dsimp [K]; nlinarith [mul_nonneg hc_nn (sub_nonneg.mpr hεd),
          mul_nonneg hc_nn hd_nn, mul_nonneg hc_nn (sq_nonneg d), sq_nonneg d]
      exact (h1.trans (mul_le_mul_of_nonneg_left (three_add_six_sq_deltaQld_le ha hb hε0 hε1)
        (zero_le_one.trans hK))).trans (scale_deltaQld_le h21a hε0 hK)
    refine ⟨w, hst.trans (deltaQld_mono ha haA le_rfl hb hε0 hε1), fun W => ?_, fun W => ?_⟩
    · exact (raw_pauli_operator_distanceA_le_completed S hwin w hst W).trans (by linarith [hcA W])
    · exact (raw_pauli_operator_distanceB_le_completed S hwin w hst W).trans (by linarith [hcB W])
  refine ⟨A, b, hA, hb, hb1, fun P ε hε0 S hwin => ?_⟩
  rcases le_or_gt ε 1 with hε1 | hε1
  · exact hsmall P ε hε0 hε1 S hwin
  · obtain ⟨w, hst, hAraw, hBraw⟩ := hsmall P 1 zero_le_one le_rfl S
      (by linarith [S.value_nonneg])
    have hmono : deltaQld A b 1 P.m P.d P.q ≤ deltaQld A b ε P.m P.d P.q := by
      unfold deltaQld; simp only [Real.rpow_eq_pow]
      have hεb : (1 : ℝ) ^ b ≤ ε ^ b := Real.rpow_le_rpow zero_le_one hε1.le hb.le
      exact mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (zero_le_one.trans hA) (Real.rpow_nonneg (Nat.cast_nonneg _) A))
    exact ⟨w, hst.trans hmono, fun W => (hAraw W).trans hmono, fun W => (hBraw W).trans hmono⟩

end

end MIPStarRE.QPBT
