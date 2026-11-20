module

public import QPBT.Combining.Lines.SubLineSource

/-!
# The projected mixtures of the sub-line law

This module assembles the two projected point marginals of the sub-line law of
`lem:qld-sublines` into mixtures of the restricted product laws.  Drawing a
uniform point of the extended line of a mixture of line laws is the same
mixture of the corresponding uniform-point laws, so the two projected
marginals of the sub-line law are the mixtures, over the drawn kind and the
drawn extended coordinate, of the projected marginals of one branch at one
extended coordinate.  Each of those is the component law of the pair of
indices carried by that branch, so the mixing law is the law of the kind
together with the pair of indices assigned to a uniform extended coordinate.

## References

The assembly is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The uniform point of a mixture of line laws -/

variable (P : AdmissibleParams)

/-- Drawing a uniform point of the extended line of a mixture of line-triple
laws is the corresponding mixture of the uniform-point laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLinePointDist_bind {α : Type*}
    (μ : Distribution α) (ν : α → Distribution (SubLineTriple P)) :
    subLinePointDist (Distribution.bind μ ν) =
      Distribution.bind μ (fun a => subLinePointDist (ν a)) := by
  classical
  unfold subLinePointDist
  rw [Distribution.prod_bind_left, Distribution.bind_map]

/-! ## The projected marginals of one branch at one extended coordinate -/

/-- One branch of the sampling procedure, read at a fixed extended coordinate,
is the law of the triple decoded from the auxiliary randomness of that
coordinate.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_eq_bind (kind : LineKind) :
    subLineBranchDist P kind =
      Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
        (Distribution.prod (uniformDistribution (SubLinePointDir P))
            (Distribution.prod (subLineSeedDist (subLineXIndex k))
              (subLineSeedDist (subLineZIndex k)))).map
          fun w => subLineTripleOf kind k w := by
  classical
  rw [subLineBranchDist, subLineSamplingDist, Distribution.bind_map]
  refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
  rw [Distribution.map_map]

/-! ## The mixing law of the two indices -/

/-- The law of the kind and the pair of source indices assigned to a uniform
extended coordinate of one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentBranch
    (kind : LineKind) : Distribution (SubLineComponent P) :=
  (uniformDistribution (Fin (2 * P.m + 2))).map fun k =>
    (kind, (subLineXIndex k, subLineZIndex k))

/-- The mixing law of the sub-line lemma: the equal mixture over the two kinds
of the law of the pair of source indices of a uniform extended coordinate.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentDist :
    Distribution (SubLineComponent P) :=
  Distribution.bind (uniformDistribution (Fin 2))
    ![subLineComponentBranch P .axis, subLineComponentBranch P .diagonal]

/-! ## The two projected marginals of one branch -/

/-- The `X` marginal of a uniform point of the extended line of one branch is
the mixture, along the pair of source indices of a uniform extended
coordinate, of the `X` component laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineXProjection
    (kind : LineKind) :
    (subLinePointDist (subLineBranchDist P kind)).map subLineXProjection =
      Distribution.bind (subLineComponentBranch P kind)
        (subLineXComponentDist P) := by
  classical
  rw [subLineBranchDist_eq_bind, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentBranch, Distribution.bind_map_left]
  refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
  classical
  unfold subLinePointDist
  rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
  apply subLineBranchSamplingData_map_projX

/-- The `Z` marginal of a uniform point of the extended line of one branch is
the mixture, along the pair of source indices of a uniform extended
coordinate, of the `Z` component laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineZProjection
    (kind : LineKind) :
    (subLinePointDist (subLineBranchDist P kind)).map subLineZProjection =
      Distribution.bind (subLineComponentBranch P kind)
        (subLineZComponentDist P) := by
  classical
  rw [subLineBranchDist_eq_bind, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentBranch, Distribution.bind_map_left]
  refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
  classical
  unfold subLinePointDist
  rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
  apply subLineBranchSamplingData_map_projZ

/-! ## The two projected marginals of the sub-line law -/

/-- The `X` point marginal of the sub-line law is the mixture of the `X`
component laws along the mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_subLineXProjection :
    (subLinePointDist (subLineDist P)).map subLineXProjection =
      Distribution.bind (subLineComponentDist P) (subLineXComponentDist P) := by
  classical
  rw [subLineDist, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentDist, Distribution.bind_bind]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · apply subLineBranchDist_map_subLineXProjection
  · apply subLineBranchDist_map_subLineXProjection

/-- The `Z` point marginal of the sub-line law is the mixture of the `Z`
component laws along the mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_subLineZProjection :
    (subLinePointDist (subLineDist P)).map subLineZProjection =
      Distribution.bind (subLineComponentDist P) (subLineZComponentDist P) := by
  classical
  rw [subLineDist, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentDist, Distribution.bind_bind]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · apply subLineBranchDist_map_subLineZProjection
  · apply subLineBranchDist_map_subLineZProjection

end

end MIPStarRE.QPBT
