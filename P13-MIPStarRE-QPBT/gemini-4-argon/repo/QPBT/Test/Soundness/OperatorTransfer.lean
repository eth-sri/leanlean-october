module

public import QPBT.Test.Soundness.StateTransfer

/-!
# Operator transfer from supplied extraction data
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

variable {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : ProjectiveSetting P epsilon} {w : GlobalPairWitness S deltaG}

private theorem extracted_alice_eq (W : PauliKind) (h : PauliRegister P) :
    S.placeExtractedRegister .alice (pauliProj W h) =
      reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (pauliProjOnA'' P (ιA' := S.toStrategy.ιA × PauliRegister P)
          (ιB' := S.toStrategy.ιB × PauliRegister P) W h) := by
  ext i j
  change (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 *
    (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
    ((1 : Op S.toStrategy.ιB) i.2.1 j.2.1 * pauliProj W h i.1.2.2 j.1.2.2) *
    (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 *
    (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2 = _
  simp [reindexOp, sixRegExtractionEquiv, pauliProjOnA'',
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

private theorem extracted_bob_eq (W : PauliKind) (h : PauliRegister P) :
    S.placeExtractedRegister .bob (pauliProj W h) =
      reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
        (pauliProjOnB'' P (ιA' := S.toStrategy.ιA × PauliRegister P)
          (ιB' := S.toStrategy.ιB × PauliRegister P) W h) := by
  ext i j
  change ((1 : Op S.toStrategy.ιA) i.1.1 j.1.1 * pauliProj W h i.2.2.2 j.2.2.2) *
    (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
    (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
    (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 *
    (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 = _
  simp [reindexOp, sixRegExtractionEquiv, pauliProjOnB'',
    Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

/-- Alice's isometry-conjugated Pauli distance is bounded by twice the concrete
swap-family distance plus twice the actual squared state error. -/
theorem ExtractionWitness.pauli_distance_alice_le_components
    (v : ExtractionWitness S w delta) (W : PauliKind) :
    pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W ≤
      2 * opFamilyDistSq (uniformDistribution Unit)
        (fun (_ : Unit) (h : PauliRegister P) =>
          conjBy (S.placeSide .alice (swapUnitary w .alice))
            (S.placePlayer .alice ((S.pauliMeas .alice W).effect h)))
        (fun (_ : Unit) (h : PauliRegister P) =>
          S.placeExtractedRegister .alice (pauliProj W h))
        (S.idealExpState v.aux) +
      2 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  classical
  have h := sum_norm_leftTensor_conjIsometry_sub_sq_le
    v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
    (S.pauliMeas .alice W).effect (S.swappedPauliMeas w .alice W)
    (pauliProjOnA'' P W)
    (fun h => unitaryAncillaIsometry_intertwines (eprState (PauliRegister P))
      (eprState_norm _) (swapUnitary w .alice) (v.swap_left_unitary .alice)
      ((S.pauliMeas .alice W).effect h))
    S.toStrategy.ψ (idealState P v.toPauliSoundnessWitness.aux)
  have hlift (M : Op S.toStrategy.ιA) :
      liftedAEffect S.toStrategy (ιB' := v.toPauliSoundnessWitness.ιB')
          v.toPauliSoundnessWitness.φA M =
        heteroKron (conjIsometry v.toPauliSoundnessWitness.φA M)
          (1 : Op (v.toPauliSoundnessWitness.ιB' × PauliRegister P)) := by
    ext i j
    simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]
  have hcA (h : PauliRegister P) :
      conjBy (S.placeSide .alice (swapUnitary w .alice))
          (S.placePlayer .alice ((S.pauliMeas .alice W).effect h)) =
        reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron ((S.swappedPauliMeas w .alice W).effect h) 1) :=
    (S.placeSide_swappedPauliMeas w .alice W h).symm
  let D := opFamilyDistSq (uniformDistribution Unit)
    (fun (_ : Unit) (h : PauliRegister P) =>
      conjBy (S.placeSide .alice (swapUnitary w .alice))
        (S.placePlayer .alice ((S.pauliMeas .alice W).effect h)))
    (fun (_ : Unit) (h : PauliRegister P) =>
      S.placeExtractedRegister .alice (pauliProj W h))
    (S.idealExpState v.aux)
  have hc : _ ≤ D := (opFamilyDistSq_uniform_unit _ _ _).symm.le
  simp_rw [hcA, extracted_alice_eq, ← WinImplications.reindexOp_sub,
    ← WinImplications.norm_applyOperatorToState_reindexState] at hc
  have hfull : (∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron ((S.swappedPauliMeas w .alice W).effect h) 1 -
        pauliProjOnA'' P W h) (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) ≤ D := by
    rw [v.idealState_eq]; exact hc
  have hstate := v.state_error_eq
  rw [norm_sub_rev] at hstate
  unfold pauliOperatorDistanceA
  refine (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)).trans
    (h.trans (add_le_add (mul_le_mul_of_nonneg_left hfull (by norm_num))
      (mul_le_mul_of_nonneg_left hstate.le (by norm_num))))
  exact congrArg (fun O => ‖applyOperatorToState (O - pauliProjOnA'' P W a)
    (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) (hlift _)

/-- Bob's isometry-conjugated Pauli distance satisfies the same separate
component estimate as Alice's, on the same ideal state. -/
theorem ExtractionWitness.pauli_distance_bob_le_components
    (v : ExtractionWitness S w delta) (W : PauliKind) :
    pauliOperatorDistanceB P S.toStrategy v.toPauliSoundnessWitness W ≤
      2 * opFamilyDistSq (uniformDistribution Unit)
        (fun (_ : Unit) (h : PauliRegister P) =>
          conjBy (S.placeSide .bob (swapUnitary w .bob))
            (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)))
        (fun (_ : Unit) (h : PauliRegister P) =>
          S.placeExtractedRegister .bob (pauliProj W h))
        (S.idealExpState v.aux) +
      2 * ‖S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat -
        S.idealExpState v.aux‖ ^ 2 := by
  classical
  have h := sum_norm_rightTensor_conjIsometry_sub_sq_le
    v.toPauliSoundnessWitness.φA v.toPauliSoundnessWitness.φB
    (S.pauliMeas .bob W).effect (S.swappedPauliMeas w .bob W)
    (pauliProjOnB'' P W)
    (fun h => unitaryAncillaIsometry_intertwines (eprState (PauliRegister P))
      (eprState_norm _) (swapUnitary w .bob) (v.swap_left_unitary .bob)
      ((S.pauliMeas .bob W).effect h))
    S.toStrategy.ψ (idealState P v.toPauliSoundnessWitness.aux)
  have hlift (M : Op S.toStrategy.ιB) :
      liftedBEffect S.toStrategy (ιA' := v.toPauliSoundnessWitness.ιA')
          v.toPauliSoundnessWitness.φB M =
        heteroKron (1 : Op (v.toPauliSoundnessWitness.ιA' × PauliRegister P))
          (conjIsometry v.toPauliSoundnessWitness.φB M) := by
    ext i j
    simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]
  have hcB (h : PauliRegister P) :
      conjBy (S.placeSide .bob (swapUnitary w .bob))
          (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)) =
        reindexOp (sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (heteroKron 1 ((S.swappedPauliMeas w .bob W).effect h)) :=
    (S.placeSide_swappedPauliMeas w .bob W h).symm
  let D := opFamilyDistSq (uniformDistribution Unit)
    (fun (_ : Unit) (h : PauliRegister P) =>
      conjBy (S.placeSide .bob (swapUnitary w .bob))
        (S.placePlayer .bob ((S.pauliMeas .bob W).effect h)))
    (fun (_ : Unit) (h : PauliRegister P) =>
      S.placeExtractedRegister .bob (pauliProj W h))
    (S.idealExpState v.aux)
  have hc : _ ≤ D := (opFamilyDistSq_uniform_unit _ _ _).symm.le
  simp_rw [hcB, extracted_bob_eq, ← WinImplications.reindexOp_sub,
    ← WinImplications.norm_applyOperatorToState_reindexState] at hc
  have hfull : (∑ h : PauliRegister P, ‖applyOperatorToState
      (heteroKron 1 ((S.swappedPauliMeas w .bob W).effect h) -
        pauliProjOnB'' P W h) (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) ≤ D := by
    rw [v.idealState_eq]; exact hc
  have hstate := v.state_error_eq
  rw [norm_sub_rev] at hstate
  unfold pauliOperatorDistanceB
  refine (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)).trans
    (h.trans (add_le_add (mul_le_mul_of_nonneg_left hfull (by norm_num))
      (mul_le_mul_of_nonneg_left hstate.le (by norm_num))))
  exact congrArg (fun O => ‖applyOperatorToState (O - pauliProjOnB'' P W a)
    (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2) (hlift _)

/-- Alice's isometry-conjugated Pauli family has squared distance at most
`4 * delta` on the ideal state. -/
theorem ExtractionWitness.pauli_distance_alice_le (v : ExtractionWitness S w delta)
    (W : PauliKind) :
    pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W ≤ 4 * delta := by
  have h := v.pauli_distance_alice_le_components W
  have h1 := v.pauli_close .alice W
  have h2 := v.state_close
  linarith

/-- Bob's isometry-conjugated Pauli family satisfies the same bound on the
same ideal state. -/
theorem ExtractionWitness.pauli_distance_bob_le (v : ExtractionWitness S w delta)
    (W : PauliKind) :
    pauliOperatorDistanceB P S.toStrategy v.toPauliSoundnessWitness W ≤ 4 * delta := by
  have h := v.pauli_distance_bob_le_components W
  have h1 := v.pauli_close .bob W
  have h2 := v.state_close
  linarith

/-- Isometry transfer bounds for supplied extraction data in a projective
setting. -/
theorem ExtractionWitness.isometry_transfer_bounds (v : ExtractionWitness S w delta) :
    ∃ t : PauliSoundnessWitness P S.toStrategy,
      ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
        max (Real.sqrt delta) (4 * delta) ∧
      (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
        max (Real.sqrt delta) (4 * delta)) ∧
      (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
        max (Real.sqrt delta) (4 * delta)) :=
  ⟨v.toPauliSoundnessWitness,
    (Real.le_sqrt_of_sq_le v.state_close_ofExtractionWitness).trans (le_max_left _ _),
    fun W => (v.pauli_distance_alice_le W).trans (le_max_right _ _),
    fun W => (v.pauli_distance_bob_le W).trans (le_max_right _ _)⟩

private theorem four_mul_deltaQld_le {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    4 * deltaQld a b epsilon P.m P.d P.q ≤ deltaQld (4 * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hpow := Real.rpow_le_rpow_of_exponent_le hmd (show a ≤ 4 * a by linarith)
  unfold deltaQld
  calc
    4 * (a * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ))))) =
      (4 * a) * Real.rpow ((P.m * P.d : ℕ) : ℝ) a *
        (Real.rpow epsilon b + Real.rpow (P.q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((P.m * P.d : ℕ) : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by linarith))
      (add_nonneg (add_nonneg (Real.rpow_nonneg hepsilon _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (by norm_num) _))

/-- All three conditional soundness bounds have the source error form after
enlarging the universal prefactor and halving the extraction exponent. -/
theorem pauli_soundness_deltaQld_ofExtractionWitness
    (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a) (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
        ∀ (S : ProjectiveSetting P epsilon)
          (w : GlobalPairWitness S (deltaQld a b epsilon P.m P.d P.q))
          (_v : ExtractionWitness S w
            (deltaExtract C (deltaConstructPaulis C epsilon
              (deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q) P.m P.d P.q)),
          ∃ t : PauliSoundnessWitness P S.toStrategy,
            ‖isometryTensor t.φA t.φB S.toStrategy.ψ - idealState P t.aux‖ ≤
              deltaQld a' b' epsilon P.m P.d P.q ∧
            (∀ W : PauliKind, pauliOperatorDistanceA P S.toStrategy t W ≤
              deltaQld a' b' epsilon P.m P.d P.q) ∧
            (∀ W : PauliKind, pauliOperatorDistanceB P S.toStrategy t W ≤
              deltaQld a' b' epsilon P.m P.d P.q) := by
  obtain ⟨A, B, hA, hB, hB1, herror⟩ := deltaExtract_le_deltaQld C a b hC ha hb hb1
  refine ⟨4 * A, B / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon hepsilon hepsilon1 S w v
  obtain ⟨t, ht, htA, htB⟩ := v.isometry_transfer_bounds
  have hmono := deltaQld_mono (P := P) hA (le_refl A) (show B / 2 ≤ B by linarith)
    (show 0 < B / 2 by positivity) hepsilon hepsilon1
  have hfour := four_mul_deltaQld_le (P := P) (b := B / 2) hA hepsilon
  have hnonneg : 0 ≤ deltaQld A (B / 2) epsilon P.m P.d P.q := by
    have hA0 := zero_le_one.trans hA
    simp only [deltaQld, Real.rpow_eq_pow]
    positivity
  have hcommon : max (Real.sqrt _) (4 * _) ≤
      deltaQld (4 * A) (B / 2) epsilon P.m P.d P.q := max_le
    (((Real.sqrt_le_sqrt (herror P epsilon hepsilon hepsilon1)).trans
      (sqrt_deltaQld_le hA hepsilon)).trans
        ((show deltaQld A (B / 2) epsilon P.m P.d P.q ≤
          4 * deltaQld A (B / 2) epsilon P.m P.d P.q by linarith).trans hfour))
    ((mul_le_mul_of_nonneg_left
      ((herror P epsilon hepsilon hepsilon1).trans hmono)
      (by norm_num : (0 : ℝ) ≤ 4)).trans hfour)
  exact ⟨t, ht.trans hcommon, fun W => (htA W).trans hcommon,
    fun W => (htB W).trans hcommon⟩

end

end MIPStarRE.QPBT
