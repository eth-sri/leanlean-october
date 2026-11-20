module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.GameValue
public import QPBT.Combining.DirectLowDegree.Transport.Combining.WinPredicate

/-!
# The value of the combined strategy

`lem:ld-combined-value` transports the value of a projective strategy along
`def:ld-combined-strategy`.  Both games weight their nine ordered type pairs
uniformly, so it suffices to bound the rejection probability of each branch of
the combined game by a bounded number of branch rejection probabilities of the
original game.  Splitting a branch according to the event of
`lem:ld-combined-question-law`, the branch conditioned on a point coordinate
index is the branch of the original game at the same ordered type pair, and the
branch conditioned on a combining coordinate index is the point-versus-point
branch of the original game; on each of the two events the relabelling of
`def:ld-combined-strategy` carries acceptance to acceptance, which is
`directCombinedWinTransport_all`.  Each branch of the combined game is therefore
rejected with probability at most the sum of two branch rejection probabilities
of the original game, and summing over the nine branches multiplies the
rejection probability by at most ten.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:526-568`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum

noncomputable section

variable (D : DirectLdParams) (S : Strategy (directLdGame D)) (types : LdType × LdType)

/-- The rejected mass of the original strategy at the pair of questions
measured by the combined strategy, as a function of the coordinate index and of
the two point parts of the sample of the combined game.  By
`lem:ld-combined-question-law` those three data determine the measured pair. -/
def directCombinedMeasuredRejectedMass
    (i : Fin D.combined.m)
    (pd : (DirectPoint D) × (DirectPoint D)) : ℝ :=
  match directCombinedIndexSplit i with
  | .inl j =>
      directRejectedMass D S
        (types.1, directLdMap types.1 ⟨pd.1, j, pd.2⟩)
        (types.2, directLdMap types.2 ⟨pd.1, j, pd.2⟩)
  | .inr _ =>
      directRejectedMass D S (directLdPointQuestionOf D pd.1)
        (directLdPointQuestionOf D pd.1)

/-- Conditioned on a point coordinate index, the measured pair is the canonical
pair of the original game at the same ordered type pair attached to a uniform
sample. -/
theorem avgOver_directCombinedMeasuredRejectedMass_pointVar (j : Fin D.m) :
    avgOver (uniformDistribution
        ((DirectPoint D) × (DirectPoint D)))
      (directCombinedMeasuredRejectedMass D S types
        (combinedPointVar D.m D.k j)) =
      directLdIndexedBranchRejectionProbability D S types j := by
  apply avgOver_congr
  intro pd
  simp [directCombinedMeasuredRejectedMass]

/-- Conditioned on a combining coordinate index, both measured questions are
the point question at a uniform point, so the branch reduces to the
point-versus-point branch of the original game. -/
theorem avgOver_directCombinedMeasuredRejectedMass_coefficientVar (r : Fin D.k) :
    avgOver (uniformDistribution
        ((DirectPoint D) × (DirectPoint D)))
      (directCombinedMeasuredRejectedMass D S types
        (combinedCoefficientVar D.m D.k r)) =
      directLdBranchRejectionProbability S (.point, .point) := by
  have hcongr : avgOver (uniformDistribution
        ((DirectPoint D) × (DirectPoint D)))
      (directCombinedMeasuredRejectedMass D S types
        (combinedCoefficientVar D.m D.k r)) =
      avgOver (uniformDistribution
        ((DirectPoint D) × (DirectPoint D)))
        (fun pd => (fun (u _ : DirectPoint D) =>
          directRejectedMass D S (directLdPointQuestionOf D u)
            (directLdPointQuestionOf D u)) pd.1 pd.2) := by
    apply avgOver_congr
    intro pd
    simp [directCombinedMeasuredRejectedMass]
  rw [hcongr, avgOver_uniform_prod
      (f := fun (u _ : DirectPoint D) =>
        directRejectedMass D S (directLdPointQuestionOf D u)
          (directLdPointQuestionOf D u)),
    directLdBranchRejectionProbability_point_point_eq]
  apply avgOver_congr
  intro _
  exact avgOver_uniform_const _

/-- Branch-wise half of `lem:ld-combined-value`: every branch of the combined
game is rejected with probability at most the sum of the branch of the original
game at the same ordered type pair and its point-versus-point branch. -/
theorem directLdBranchRejectionProbability_directCombinedStrategy_le :
    directLdBranchRejectionProbability (directCombinedStrategy D S)
        types ≤
        directLdBranchRejectionProbability S types +
        directLdBranchRejectionProbability S (.point, .point) := by
  let dist :=
    uniformDistribution
    ((DirectPoint D) × (DirectPoint D))
  classical
  have hmpos := Nat.lt_of_lt_of_le Nat.zero_lt_one D.hm
  let _ : Nonempty (Fin D.combined.m) :=
    ⟨⟨0, by bound⟩⟩
  have hstep : directLdBranchRejectionProbability
      (directCombinedStrategy D S) types ≤
      avgOver (uniformDistribution (Fin D.combined.m ×
        ((DirectPoint D) × (DirectPoint D))))
        (fun x => directCombinedMeasuredRejectedMass D S types x.1 x.2) := by
    rw [directLdBranchRejectionProbability_eq_avgOver,
      ← directCombinedSample_indexPointParts_uniform, Distribution.avgOver_map]
    exact avgOver_mono _ _ _ fun sample =>
      (by
        refine le_trans (directRejectedMass_directCombinedStrategy_le D S _ _
          (directCombinedWinTransport_all D types.1 types.2 sample)) (le_of_eq ?_)
        rcases hsplit : directCombinedIndexSplit sample.index with j | r
        · have hindex :=
            eq_combinedPointVar_of_indexSplit D hsplit
          rw [directCombined_measuredQuestion_of_pointVar D types.1 j sample hindex,
            directCombined_measuredQuestion_of_pointVar D types.2 j sample hindex]
          simp [directCombinedMeasuredRejectedMass, hsplit, directCombinedSampleProjection]
        · have hindex :=
            eq_combinedCoefficientVar_of_indexSplit D hsplit
          rw [directCombined_measuredQuestion_of_coefficientVar D types.1 r sample hindex,
            directCombined_measuredQuestion_of_coefficientVar D types.2 r sample hindex]
          simp [directCombinedMeasuredRejectedMass, hsplit])
  refine le_trans hstep ?_
  rw [avgOver_uniform_prod,
    avgOver_uniform_eq_inv_card_mul_sum, Fintype.card_fin]
  have hmkNat : D.combined.m = D.m + D.k := rfl
  have hmk : (D.combined.m : ℕ) = D.m + (D.k : ℝ) := by
    push_cast
    ring
  have hsum : ∑ i : Fin D.combined.m,
      avgOver dist
        (directCombinedMeasuredRejectedMass D S types i) =
      (∑ j : Fin D.m, directLdIndexedBranchRejectionProbability D S types j) +
        D.k * directLdBranchRejectionProbability S (.point, .point) := by
    show ∑ i : Fin (D.m + D.k),
        avgOver dist
          (directCombinedMeasuredRejectedMass D S types i) = _
    rw [Fin.sum_univ_add]
    congr 1
    · congr 1 with j
      apply avgOver_directCombinedMeasuredRejectedMass_pointVar
    · have hconst : ∀ r : Fin D.k,
          avgOver dist
            (directCombinedMeasuredRejectedMass D S types
             (Fin.natAdd D.m r)) =
            directLdBranchRejectionProbability S (.point, .point) := avgOver_directCombinedMeasuredRejectedMass_coefficientVar D S types
      simp_all
  have hbranch : ∑ j : Fin D.m,
      directLdIndexedBranchRejectionProbability D S types j =
      D.m * directLdBranchRejectionProbability S types := by
    simp [directLdBranchRejectionProbability_eq_avgOver_index, avgOver_uniform_eq_inv_card_mul_sum]
    field_simp
  simp [hsum]
  have hm : (0 : ℝ) < D.m := by exact_mod_cast hmpos
  have hk : (0 : ℝ) < D.k := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one D.hk)
  rw [inv_mul_eq_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hm.le (directLdBranchRejectionProbability_nonneg D S (.point, .point)), mul_nonneg hk.le (directLdBranchRejectionProbability_nonneg D S types)]

/-- `lem:ld-combined-value`, rejection form.  Both the directly indexed
low-degree game with the original parameters and the one with the combined
parameters weight their nine ordered type pairs uniformly, so averaging the
branch-wise bound over the nine pairs bounds the rejection probability of the
combined strategy by the rejection probability of the original strategy plus
its point-versus-point branch; that branch is in turn at most nine times the
rejection probability of the original strategy.  The universal constant of the
source statement is therefore `10`. -/
theorem directLdRejectionProbability_directCombinedStrategy_le :
    directLdRejectionProbability (directCombinedStrategy D S) ≤
      10 * directLdRejectionProbability S := by
  have hle := directLdBranchRejectionProbability_directCombinedStrategy_le D S
  have hnn := directLdBranchRejectionProbability_nonneg D S
  simp [directLdRejectionProbability, avgOver_ldType_pair]
  linarith [hle (.point, .point), hle (.point, .aline), hle (.point, .dline),
    hle (.aline, .point), hle (.aline, .aline), hle (.aline, .dline),
    hle (.dline, .point), hle (.dline, .aline), hle (.dline, .dline),
    hnn (.point, .point), hnn (.point, .aline), hnn (.point, .dline),
    hnn (.aline, .point), hnn (.aline, .aline), hnn (.aline, .dline),
    hnn (.dline, .point), hnn (.dline, .aline), hnn (.dline, .dline)]

end

end MIPStarRE.QPBT
