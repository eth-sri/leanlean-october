module

public import QPBT.Combining.Lines.SubLinePrefix

/-!
# The two independent blocks of a fresh diagonal direction pair

This module splits the fresh diagonal direction pair of the sub-line sampling
procedure into its two independent blocks.  The coordinate-index event
constrains only the scalar seed of the pair, so conditioning on it leaves the
direction block uniform and independent of the conditioned seed.  The
direction block of a fresh pair is therefore available as an unconstrained
uniform vector, which is what allows the sampling procedure to read it off the
corresponding block of the direction of the sampled extended line.

## References

The block decomposition supports `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate-index event is that of `def:ith-restricted-line`, blueprint
lines 1209--1228, paper lines 1038--1048.
-/

@[expose] public section

variable (L : MIPStarRE.QPBT.LdParams)

open scoped BigOperators Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a scalar seed -/

/-- The coordinate-index event of `def:ith-restricted-line` read on a scalar
seed alone.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
def ldSeedIndexEvent (i : Fin L.m) (s : ScalarQ L) : Prop :=
  chiIndex L s = i

/-- Decidability of the coordinate-index event on a scalar seed. -/
instance ldSeedIndexEvent_decidablePred (L : LdParams) (i : Fin L.m) :
    DecidablePred (ldSeedIndexEvent L i) := by
  intro s
  unfold ldSeedIndexEvent
  infer_instance

/-- Every coordinate-index event of a scalar seed has positive mass under the
uniform law.  Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem ldSeedIndexEvent_positive (i : Fin L.m) :
    0 < ∑ s ∈ (uniformDistribution (ScalarQ L)).support.filter
        (ldSeedIndexEvent L i),
      (uniformDistribution (ScalarQ L)).weight s := by
  refine Finset.sum_pos'
    (fun a _ => (uniformDistribution (ScalarQ L)).nonnegative a)
    ⟨seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩,
      Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · change chiIndex L (seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩) = i
    exact chiIndex_seedOfIndexResidue L i _
  · simp only [uniformDistribution, Distribution.uniformOnFinset_weight,
      Finset.mem_univ, if_true]
    positivity

/-! ## The blocks of a fresh diagonal direction pair -/

/-- A fresh diagonal direction pair at coordinate index `i` is a scalar seed
conditioned on the coordinate-index fiber of `i` together with an independent
uniform direction block.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem freshDiagonalPairDist_eq_prod (i : Fin L.m) :
    freshDiagonalPairDist L i =
      Distribution.prod
        (Distribution.restrict (uniformDistribution (ScalarQ L))
          (ldSeedIndexEvent L i) (ldSeedIndexEvent_positive L i))
        (uniformDistribution (MIPStarRE.QPBT.LdPoint L)) := by
  unfold freshDiagonalPairDist
  exact restrict_uniform_prod_fst (ldSeedIndexEvent L i)
    (ldSeedIndexEvent_positive L i) (ldSeedDirEvent_positive L i)

end

end MIPStarRE.QPBT
