module

public import QPBT.Test.Soundness.StateTransfer

/-!
# Operator transfer from supplied extraction data

The complete swap-conjugated measurements intertwine with the local ancilla
isometries. The range-projection estimates then transfer both Pauli families
to the ideal state, with squared error at most four times the extraction error.

## References

Formalization support for the final argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`.
This conditional construction uses supplied extraction data in a projective
setting; it does not prove blueprint `thm:pauli`. The omitted range projection
is documented in `docs/paper-gaps/qpbt_extraction-transfer.tex` (issue
Dengnifer/MIPStarRE-QPBT-bak#529).
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus
open MIPStarRE.LDT hiding Measurement

noncomputable section

variable {P : AdmissibleParams} {epsilon deltaG delta : ℝ}
  {S : ProjectiveSetting P epsilon} {w : GlobalPairWitness S deltaG}

/-- Add the range-projection cost to the swap comparison. -/
noncomputable abbrev ExtractionWitness.transferError (v : ExtractionWitness S w delta)
    (side : PlayerSide) (W : PauliKind) : ℝ :=
  2 * S.swapPauliDistance w v.aux side W +
    2 * ‖S.swappedState w -
      S.idealExpState v.aux‖ ^ 2

set_option synthInstance.maxSize 400 in
private theorem swapPauliDistance_reindex (v : ExtractionWitness S w delta)
    (side : PlayerSide) (W : PauliKind)
    (A B : PauliRegister P → Op (ExtractionRegisters P S.toStrategy.ιA S.toStrategy.ιB))
    (hA : ∀ h, S.swapPauliOp w side W h =
      reindexOp S.extractionBlocks (A h))
    (hB : ∀ h, S.idealPauliOp side W h =
      reindexOp S.extractionBlocks (B h)) :
    S.swapPauliDistance w v.aux side W = ∑ h, ‖applyOperatorToState (A h - B h)
      (idealState P v.toPauliSoundnessWitness.aux)‖ ^ 2 := by
  classical
  rw [ProjectiveSetting.swapPauliDistance, opFamilyDistSq_uniform_unit]
  simp_rw [hA, hB, ← reindexOp_sub, ← norm_applyOperatorToState_reindexState]
  erw [v.idealState_eq]
  rfl

/-- The same range and state error calculation applies to each local isometry. -/
private theorem ExtractionWitness.pauli_distance_le_components
    (v : ExtractionWitness S w delta) (side : PlayerSide) (W : PauliKind) :
    (match side with
      | .alice => pauliOperatorDistanceA P S.toStrategy v.toPauliSoundnessWitness W
      | .bob => pauliOperatorDistanceB P S.toStrategy v.toPauliSoundnessWitness W) ≤
      v.transferError side W := by
  let t := v.toPauliSoundnessWitness
  let e := S.extractionBlocks
  have hdist := swapPauliDistance_reindex v side W
    (fun a => reindexOp e.symm (S.placeSide side ((S.swappedPauliMeas w side W).effect a)))
    (fun a => reindexOp e.symm (S.placeExtractedRegister side (pauliProj W a)))
    (fun a => by simpa only [e, reindexOp_symm_cancel] using (S.placeSide_swappedPauliMeas w side W a).symm)
    (fun _ => reindexOp_symm_cancel _ _ |>.symm)
  have ht a := unitaryAncillaIsometry_intertwines (eprState (PauliRegister P))
    (eprState_norm _) (swapUnitary w side) (conjTranspose_mul_swapUnitary w side) ((S.pauliMeas side W).effect a)
  have hstate := v.state_error_eq
  rw [norm_sub_rev] at hstate
  rw [transferError, hdist, ← hstate]
  cases side
  · exact sum_norm_leftTensor_conjIsometry_sub_sq_le t.φA t.φB
      (S.pauliMeas .alice W).effect (S.swappedPauliMeas w .alice W) (pauliProjOnA'' P W)
      ht S.toStrategy.ψ (idealState P t.aux)
  · exact sum_norm_rightTensor_conjIsometry_sub_sq_le t.φA t.φB
      (S.pauliMeas .bob W).effect (S.swappedPauliMeas w .bob W) (pauliProjOnB'' P W)
      ht S.toStrategy.ψ (idealState P t.aux)

private theorem ExtractionWitness.transferError_le (v : ExtractionWitness S w delta)
    (side : PlayerSide) (W : PauliKind) : v.transferError side W ≤ 4 * delta := by
  have hp : S.swapPauliDistance w v.aux side W ≤ delta := v.pauli_close side W
  unfold transferError
  linarith [v.state_close]

/-- Isometry transfer bounds for supplied extraction data in a projective
setting. The common bound is `max (sqrt delta) (4 * delta)`: the state norm
is unsquared and both operator distances sum squared norms over all outcomes.
This is blueprint `thm:pauli-concrete-isometry-transfer-support`, a
conditional support theorem for `thm:pauli`, not the source theorem.
The separate component bounds are blueprint
`lem:pauli-extraction-state-distance-support`,
`thm:pauli-extraction-alice-distance-support`, and
`thm:pauli-extraction-bob-distance-support`.
Discharging the supplied-data premise requires the global-pair construction
and extraction; see `docs/paper-gaps/qpbt_extraction-transfer.tex`, issue
Dengnifer/MIPStarRE-QPBT-bak#529. -/
theorem ExtractionWitness.isometry_transfer_bounds (v : ExtractionWitness S w delta) :
    ∃ t : PauliSoundnessWitness P S.toStrategy,
      t.completedWithin (max (Real.sqrt delta) (4 * delta)) := by
  refine ⟨v.toPauliSoundnessWitness, ?_, ?_, ?_⟩
  · exact (Real.le_sqrt_of_sq_le v.state_close_ofExtractionWitness).trans (le_max_left _ _)
  · intro W
    exact (v.pauli_distance_le_components .alice W).trans
      ((v.transferError_le .alice W).trans (le_max_right _ _))
  · intro W
    exact (v.pauli_distance_le_components .bob W).trans
      ((v.transferError_le .bob W).trans (le_max_right _ _))

/-- All three conditional soundness bounds have the source error form after
enlarging the universal prefactor and halving the extraction exponent. This
theorem assumes the actual extraction data in a projective setting; it does
not construct the global-pair witness or assert unrestricted soundness.
This is blueprint `lem:pauli-supplied-extraction-error-form-support`; it
also records the constant adjustment at paper
`14_analysis_of_the_pauli_basis_test.tex:1868-1876`. The remaining source
obligations are documented in `docs/paper-gaps/qpbt_extraction-transfer.tex`. -/
theorem pauli_soundness_deltaQld_ofExtractionWitness
    (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a) (hb : 0 < b) (hb1 : b < 1) :
    ∃ a' b' : ℝ, 1 ≤ a' ∧ 0 < b' ∧ b' < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
        ∀ (S : ProjectiveSetting P epsilon)
          (w : GlobalPairWitness S (P.qldError a b epsilon))
          (_v : ExtractionWitness S w
            (deltaExtract C (deltaConstructPaulis C epsilon
              (P.qldError a b epsilon) P.m P.d P.q) P.m P.d P.q)),
          ∃ t : PauliSoundnessWitness P S.toStrategy,
            t.completedWithin (P.qldError a' b' epsilon) := by
  obtain ⟨A, B, hA, hB, hB1, herror⟩ := deltaExtract_le_deltaQld C a b hC ha hb hb1
  refine ⟨4 * A, B / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon hepsilon hepsilon1 S w v
  obtain ⟨t, ht, htA, htB⟩ := v.isometry_transfer_bounds
  have hmono := deltaQld_mono (P := P) hA (le_refl A) (show B / 2 ≤ B by linarith)
    (show 0 < B / 2 by positivity) hepsilon hepsilon1
  have hfour := scale_deltaQld_le (P := P) (b := B / 2) hA hepsilon (by norm_num : (1 : ℝ) ≤ 4)
  have hnonneg := deltaQld_nonneg (P := P) (b := B / 2) (zero_le_one.trans hA) hepsilon
  have hcommon := max_le
    (((Real.sqrt_le_sqrt (herror P epsilon hepsilon hepsilon1)).trans
      (sqrt_deltaQld_le hA hepsilon)).trans
        ((show P.qldError A (B / 2) epsilon ≤
          4 * P.qldError A (B / 2) epsilon by linarith).trans hfour))
    ((mul_le_mul_of_nonneg_left
      ((herror P epsilon hepsilon hepsilon1).trans hmono)
      (by norm_num : (0 : ℝ) ≤ 4)).trans hfour)
  exact ⟨t, ht.trans hcommon, fun W => (htA W).trans hcommon,
    fun W => (htB W).trans hcommon⟩

end

end MIPStarRE.QPBT
