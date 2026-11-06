module

public import QPBT.Extraction.Bounds
public import QPBT.Extraction.ObservableConsistency

/-!
# Observable consistency after the concrete swaps

Unitary conjugation transports the supplied-witness observable estimate to
the canonical Pauli operators on the extracted registers. This is the input
to the EPR correlation argument, before projection and normalization.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1701-1724`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MIPStarRE.LDT DistanceCalculus

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

theorem conjBy_reindexOp (e : I ≃ J) (U A : Op J) :
    conjBy (reindexOp e U) (reindexOp e A) = reindexOp e (conjBy U A) := by
  simp [conjBy, ProjectiveSetting.reindexOp_conjTranspose, WinImplications.reindexOp_mul]

theorem conjBy_heteroKron (U A : Op I) (V B : Op J) :
    conjBy (heteroKron U V) (heteroKron A B) =
      heteroKron (conjBy U A) (conjBy V B) := by
  simp [conjBy, heteroKron_conjTranspose, heteroKron_mul]

variable {P : AdmissibleParams} {epsilon deltaG : ℝ}

/-- Simultaneous swaps conjugate each local operator by its own swap. This
retains the heterogeneous local spaces in the calculation at paper lines 1701-1713. -/
theorem ProjectiveSetting.conjBy_placeBoth_swap_placeSide
    (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (side : PlayerSide)
    (A : Op (ExtractionBlock P (S.LocalSpace side))) :
    conjBy (S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob)) (S.placeSide side A) =
      S.placeSide side (conjBy (swapUnitary w side) A) := by
  cases side <;> simp only [ProjectiveSetting.placeBoth, ProjectiveSetting.placeSide,
    conjBy_reindexOp, conjBy_heteroKron]
  · congr 2
    change swapUnitary w .bob * 1 * (swapUnitary w .bob)ᴴ = 1
    rw [Matrix.mul_one, swapUnitary_mul_conjTranspose]
  · congr 2
    change swapUnitary w .alice * 1 * (swapUnitary w .alice)ᴴ = 1
    rw [Matrix.mul_one, swapUnitary_mul_conjTranspose]

/-- Conjugating both operator families and the state by the same unitary
preserves their state-dependent distance. -/
theorem opDistSq_conjBy_apply_eq {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (mu : Distribution X) (U : Op I)
    (hU : Uᴴ * U = 1) (A B : X → Op I) (psi : EuclideanSpace ℂ I) :
    opDistSq mu (fun x => conjBy U (A x)) (fun x => conjBy U (B x))
      (applyOperatorToState U psi) = opDistSq mu A B psi := by
  have hterm (M N : Op I) : (conjBy U M - conjBy U N) * U = U * (M - N) := by
    simp only [conjBy]
    calc
      _ = U * (M - N) * (Uᴴ * U) := by noncomm_ring
      _ = _ := by simp_all
  unfold opDistSq opFamilyDistSq
  simp
  apply avgOver_congr
  intro x
  rw [← applyOperatorToState_mul, hterm,
    MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hU]

/-- After the swaps, the pulled-apart distance is exactly the distance of the
canonical Pauli observables on the two extracted blocks. -/
theorem opDistSq_extracted_eq_tildeObs
    (S : ProjectiveSetting P epsilon)
    (w : GlobalPairWitness S deltaG) (W : PauliKind) (j : Fin P.model.basisDim) :
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (heteroKron (1 : Op (S.ExpandedLocalSpace .alice))
        (tauObservable W (P.model.basis j • u))))
      (fun u => S.placeSide .bob (heteroKron (1 : Op (S.ExpandedLocalSpace .bob))
        (tauObservable W (P.model.basis j • u))))
      (S.applyBoth (swapUnitary w .alice) (swapUnitary w .bob) S.psiHat) =
    opDistSq (uniformDistribution (PauliRegister P))
      (fun u => S.placeSide .alice (tildeObs w .alice W u j))
      (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat := by
  have h := opDistSq_conjBy_apply_eq (uniformDistribution (PauliRegister P))
    _ (S.placeBoth_swap_left_unitary w)
    (fun u => S.placeSide .alice (tildeObs w .alice W u j))
    (fun u => S.placeSide .bob (tildeObs w .bob W u j)) S.psiHat
  simp_rw [S.conjBy_placeBoth_swap_placeSide w .alice,
    S.conjBy_placeBoth_swap_placeSide w .bob,
    swapUnitary_conj_tildeObs w .alice W,
    swapUnitary_conj_tildeObs w .bob W] at h
  simp_all [ProjectiveSetting.applyBoth]

end

end MIPStarRE.QPBT
