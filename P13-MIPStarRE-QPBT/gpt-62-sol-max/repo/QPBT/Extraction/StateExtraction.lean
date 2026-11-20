module

public import QPBT.Extraction.ProjectionFromDistance

/-!
# Normalized state extraction from a supplied global witness

The Pauli disagreement estimate is transported to auxiliary/EPR coordinates.
Averaging and the EPR projection identity then select a normalized auxiliary
state, including the case where the unnormalized projection vanishes.

## References

Blueprint `lem:qld-unitary`, Item 1; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715-1783`;
`docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix Classical

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MIPStarRE.LDT DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {epsilon : ℝ} (S : ProjectiveSetting P epsilon)

private theorem reindex_extracted (side : PlayerSide) (T : Op (PauliRegister P)) :
    reindexOp S.extractionShuffle.symm
      (heteroKron (1 : Op (S.ExtractionAux))
        (match side with | .alice => heteroKron T 1 | .bob => heteroKron 1 T)) =
      S.placeExtractedRegister side T := by
  classical
  cases side <;> ext i j <;>
    simp [placeExtractedRegister, placeSide, reindexOp, extractionIdealShuffle, sixRegExtractionEquiv, heteroKron,
      Matrix.kronecker, Matrix.one_apply, Prod.ext_iff, ite_and, ite_mul, mul_ite] <;>
    split_ifs <;> rfl

/-- Changing to auxiliary/EPR coordinates and multiplying all Pauli labels by
a nonzero basis element preserve the uniform disagreement distance. -/
theorem pauli_dist_reindex_extraction
    (theta : EuclideanSpace ℂ (S.ExpandedSpace))
    (W : PauliKind) (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => heteroKron
        (1 : Op (S.ExtractionAux))
        (heteroKron (tauObservable W u) (1 : Op (PauliRegister P))))
      (fun u => heteroKron
        (1 : Op (S.ExtractionAux))
        (heteroKron (1 : Op (PauliRegister P)) (tauObservable W u)))
      (reindexState S.extractionShuffle.symm theta) =
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeExtractedRegister .alice (tauObservable W (P.model.basis j • u)))
      (fun u => S.placeExtractedRegister .bob (tauObservable W (P.model.basis j • u))) theta := by
  classical
  unfold opDistSq opFamilyDistSq
  simp only [Fintype.sum_unique]
  simp_rw [norm_applyOperatorToState_reindexState,
    reindexOp_sub, S.reindex_extracted .alice, S.reindex_extracted .bob]
  let e : PauliRegister P ≃ PauliRegister P := Equiv.piCongrRight
    (fun _ => Equiv.mulLeft₀ (P.model.basis j) (P.model.basis.ne_zero j))
  have he (u : PauliRegister P) : e u = P.model.basis j • u := rfl
  simpa only [Equiv.symm_symm, he] using avgOver_uniform_equiv e.symm
    (fun u => ‖applyOperatorToState
      (S.placeExtractedRegister .alice (tauObservable W u) -
        S.placeExtractedRegister .bob (tauObservable W u))
      theta‖ ^ 2)

end ProjectiveSetting

/-- A supplied global witness determines a normalized auxiliary state within
`16 * deltaConstructPaulis` squared distance of the concrete swapped state.
The universal constant is chosen before the parameters. This proves Item 1
of conditional extraction at the stronger linear construction-error scale.

**Unfaithful:** This uses `extracted_obs_selfConsistent_ofGlobalPairWitness`,
whose global measurement is supplied rather than constructed from
`lem:qld-4-7`. The planned composition with `exists_globalPairWitness` remains
open under issue Dengnifer/MIPStarRE-QPBT-bak#123 in `docs/paper-gaps/qpbt_extraction-transfer.tex`.

**Local fix:** The projection and normalization estimates replace the numerical
steps at paper lines 1743-1783 as documented in the same gap note. -/
theorem exists_extraction_aux_of_global_pair_witness_explicit
    (P : AdmissibleParams) (epsilon deltaG : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1) (hdeltaG : 0 ≤ deltaG)
    (S : ProjectiveSetting P epsilon) (w : GlobalPairWitness S deltaG) :
    ∃ aux : EuclideanSpace ℂ
        (S.ExtractionAux),
      ‖aux‖ = 1 ∧
        ‖S.swappedState w -
          S.idealExpState aux‖ ^ 2 ≤
            16 * deltaConstructPaulis pauliBaselineExtractionConstant
              epsilon deltaG P.m P.d P.q := by
  let theta := S.swappedState w
  let e := S.extractionShuffle.symm
  let delta := deltaConstructPaulis pauliBaselineExtractionConstant
    epsilon deltaG P.m P.d P.q
  have hdelta : 0 ≤ delta := by
    dsimp [delta, deltaConstructPaulis, pauliBaselineExtractionConstant]
    positivity
  let j : Fin P.model.basisDim := ⟨0, P.model.basisDimOdd.pos⟩
  have hdist := Extraction.norm_sub_eprProjection_le_of_pauli_dist
    (reindexState e theta) delta hdelta (fun W => by
      exact (S.pauli_dist_reindex_extraction theta W j).trans_le
        (extracted_obs_self_consistent_of_global_pair_witness_explicit
          P epsilon deltaG hepsilon hepsilon_one hdeltaG S w W j))
  have htransport :
      ‖reindexState e theta - applyOperatorToState
        (heteroKron (1 : Op (S.ExtractionAux))
          (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
            (fun y => star (eprState (PauliRegister P) y)))) (reindexState e theta)‖ =
        ‖theta - applyOperatorToState S.extractionEprProjection theta‖ := by
    have h := norm_applyOperatorToState_reindexState e
      (1 - heteroKron (1 : Op (S.ExtractionAux))
        (Matrix.vecMulVec (fun x => eprState (PauliRegister P) x)
          (fun y => star (eprState (PauliRegister P) y)))) theta
    simpa only [reindexOp_sub, reindexOp_one, MagicSquareRigidity.applyOperatorToState_sub_op,
      applyOperatorToState_one, ProjectiveSetting.extractionEprProjection] using h
  have hprojection := htransport.symm.trans_le hdist
  obtain ⟨aux, haux, hclose⟩ := S.exists_unit_aux_near_eprProjection theta (S.swappedState_norm w)
  refine ⟨aux, haux, ?_⟩
  have hnorm := norm_nonneg (theta - S.idealExpState aux)
  have hsqrt := Real.sqrt_nonneg delta
  have hsquare := Real.sq_sqrt hdelta
  change ‖theta - S.idealExpState aux‖ ^ 2 ≤ 16 * delta
  nlinarith

end

end MIPStarRE.QPBT
