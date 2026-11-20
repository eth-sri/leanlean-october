module

public import QPBT.Combining.Defs

/-!
# Generating laws of the restricted line-point distributions

This module rewrites the two restricted line-point laws of
`def:ith-restricted-line` as push-forwards of a single uniformly sampled
low-degree vector conditioned on the coordinate-index fiber of its retained
scalar seed.  In that form the point block, the seed and the direction block
of the sampled vector are visibly the independent generating data of the
restricted law, which is the description used by the sampling procedure of the
sub-line lemma: there the projected pairs are built either from a direction
block inherited from the extended line or from freshly sampled data, and each
is asserted to follow a restricted law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a single uniform vector -/

variable (L : LdParams) (i : Fin L.m) (z : LdSpace L)

/-- The coordinate-index event of `def:ith-restricted-line` read on the single
uniformly sampled low-degree vector that generates the line-point laws.
Blueprint `def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
def ldSeedEvent : Prop :=
  chiIndex L (LdSpace.seed z) = i

/-- Decidability of the coordinate-index event. -/
instance ldSeedEvent_decidablePred :
    DecidablePred (ldSeedEvent L i) := by
  intro z
  unfold ldSeedEvent
  infer_instance

/-- The coordinate-index event has positive mass under the uniform law on
low-degree vectors, so the conditioning below is normalized.  Blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem ldSeedEvent_positive :
    0 < ∑ z ∈ (uniformDistribution (LdSpace L)).support.filter
        (ldSeedEvent L i),
      (uniformDistribution (LdSpace L)).weight z := by
  classical
  refine Finset.sum_pos'
    (fun a _ => (uniformDistribution (LdSpace L)).nonnegative a)
    ⟨(fun _ => seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩),
      Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · apply chiIndex_seedOfIndexResidue
  · simp only [uniformDistribution, Distribution.uniformOnFinset_weight,
      Finset.mem_univ, if_true]
    positivity

/-! ## Canonical representatives are unchanged by the conditioning maps -/

/-- Two axis-line descriptions with the same seed and the same base agree:
the stored proof of `def:line-representative` invariance is a proposition and
carries no further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_axis_congr {L : LdParams}
    {b b' : LdPoint L} {s : ScalarQ L} (h : b = b')
    (hb : lineRepMap (coordinateDirection (chiIndex L s)) b = b)
    (hb' : lineRepMap (coordinateDirection (chiIndex L s)) b' = b') :
    LineDesc.axis b s hb = LineDesc.axis b' s hb' := by
  subst h
  rfl

/-- Two diagonal-line descriptions with the same seed, the same base and the
same direction agree: the stored proofs of `def:line-representative`
invariance and of the prefix-zero condition are propositions and carry no
further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_diagonal_congr {L : LdParams}
    {b b' d d' : LdPoint L} {s : ScalarQ L}
    (hb : b = b') (hd : d = d')
    (h1 : lineRepMap d b = b)
    (h2 : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d j = 0)
    (h1' : lineRepMap d' b' = b')
    (h2' : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d' j = 0) :
    LineDesc.diagonal b s d h1 h2 = LineDesc.diagonal b' s d' h1' h2' := by
  subst hb
  subst hd
  rfl

/-- The axis-line decoder is unchanged by the axis conditioning map: the
canonical representative of `def:line-representative` is idempotent, so
decoding the conditioned vector and decoding the original vector agree.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem aLineDescOf_ldALineCL :
    aLineDescOf (ldALineCL L z) = aLineDescOf z :=
  lineDesc_axis_congr (lineRepMap_apply_self _ _) _ _

/-- The diagonal-line decoder is unchanged by the diagonal conditioning map:
the prefix projection and the canonical representative of
`def:line-representative` are both idempotent.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem dLineDescOf_ldDLineCL :
    dLineDescOf (ldDLineCL L z) = dLineDescOf z := by
  have hdir : prefixProjection (chiIndex L (LdSpace.seed (ldDLineCL L z)))
        (LdSpace.direction (ldDLineCL L z))
      = _ :=
    prefixProjection_idempotent _ _
  apply lineDesc_diagonal_congr <;> try assumption
  rw [hdir]
  apply lineRepMap_apply_self

/-! ## Generating laws of the restricted line-point distributions -/

/-- The `i`-th restricted axis-line law is the law of the pair consisting of
the canonical axis-parallel line through a low-degree vector and its point
block, when that vector is uniform conditioned on the coordinate-index fiber
of its seed.  This is the generating description used in the sampling
procedure of blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedALineDist_eq_map_restrict :
    restrictedALineDist L i =
      (Distribution.restrict (uniformDistribution (LdSpace L))
          (ldSeedEvent L i) (ldSeedEvent_positive L i)).map
        (fun z => (aLineDescOf z, LdSpace.point z)) := by
  classical
  have hpos := restrictedALineSeedEvent_positive L i
  unfold restrictedALineDist restrictedALinePreDist clDistribution
  rw [Distribution.restrict_map _
      _
      (restrictedLineSeedEvent L i) _ (fun _ => Iff.rfl)
      hpos (ldSeedEvent_positive L i),
    Distribution.map_map]
  apply congrArg
  funext z
  rw [aLineDescOf_ldALineCL]
  rfl

/-- The `i`-th restricted diagonal-line law is the law of the pair consisting
of the canonical diagonal line through a low-degree vector and its point
block, when that vector is uniform conditioned on the coordinate-index fiber
of its seed.  This is the generating description used in the sampling
procedure of blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedDLineDist_eq_map_restrict :
    restrictedDLineDist L i =
      (Distribution.restrict (uniformDistribution (LdSpace L))
          (ldSeedEvent L i) (ldSeedEvent_positive L i)).map
        (fun z => (dLineDescOf z, LdSpace.point z)) := by
  classical
  have hpos := restrictedDLineSeedEvent_positive L i
  unfold restrictedDLineDist restrictedDLinePreDist clDistribution
  rw [Distribution.restrict_map _
      _
      (restrictedLineSeedEvent L i) _ (fun _ => Iff.rfl)
      hpos (ldSeedEvent_positive L i),
    Distribution.map_map]
  apply congrArg
  funext z
  rw [dLineDescOf_ldDLineCL]
  rfl

end

end MIPStarRE.QPBT
