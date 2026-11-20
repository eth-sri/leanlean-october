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

/-- Drawing a uniform point of the extended line of a mixture of line-triple
laws is the corresponding mixture of the uniform-point laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLinePointDist_bind (P : AdmissibleParams) {α : Type*}
    (μ : Distribution α) (ν : α → Distribution (SubLineTriple P)) :
    subLinePointDist P (Distribution.bind μ ν) =
      Distribution.bind μ (fun a => subLinePointDist P (ν a)) := by
  classical
  unfold subLinePointDist
  rw [Distribution.prod_bind_left, Distribution.bind_map]

/-! ## The projected marginals of one branch at one extended coordinate -/

/-- One branch of the sampling procedure, read at a fixed extended coordinate,
is the law of the triple decoded from the auxiliary randomness of that
coordinate.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_eq_bind (P : AdmissibleParams) (kind : LineKind) :
    subLineBranchDist P kind =
      Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
        (subLineBlocksDist P k).map (subLineTripleOf P kind k) := by
  classical
  simp_all [subLineBranchDist, subLineSamplingDist, Distribution.bind_map, Distribution.map_map]

private theorem subLineBranchDist_map_joint_at (P : AdmissibleParams)
    (kind : LineKind) (k : Fin (2 * P.m + 2)) :
    (subLinePointDist P ((subLineBlocksDist P k).map (subLineTripleOf P kind k))).map
        subLineJointProjection =
      subLineComponentProduct P (kind, subLineXIndex P k, subLineZIndex P k) := by
  unfold subLinePointDist
  rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
  exact subLineBranchSamplingData_map_joint P kind k

/-! ## The mixing law of the two indices -/

section

variable (P : AdmissibleParams)
include P

/-- The law of the kind and the pair of source indices assigned to a uniform
extended coordinate of one branch.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentBranch
    (kind : LineKind) : Distribution (SubLineComponent P) :=
  (uniformDistribution (Fin (2 * P.m + 2))).map fun k =>
    (kind, (subLineXIndex P k, subLineZIndex P k))

/-- The mixing law of the sub-line lemma: the equal mixture over the two kinds
of the law of the pair of source indices of a uniform extended coordinate.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
noncomputable def subLineComponentDist :
    Distribution (SubLineComponent P) :=
  Distribution.bind (uniformDistribution (Fin 2))
    ![subLineComponentBranch P .axis, subLineComponentBranch P .diagonal]

/-- The mixing law has total mass one. -/
theorem subLineComponentDist_isProbability :
    (subLineComponentDist P).IsProbability := by
  refine Distribution.bind_isProbability _ _
    (uniformDistribution_isProbability _) fun c _ => ?_
  fin_cases c
  · exact Distribution.IsProbability.map
      (uniformDistribution_isProbability _) _
  · exact Distribution.IsProbability.map
      (uniformDistribution_isProbability _) _

private theorem subLineBranchDist_map_joint (kind : LineKind) :
    (subLinePointDist P (subLineBranchDist P kind)).map subLineJointProjection =
      Distribution.bind (subLineComponentBranch P kind) (subLineComponentProduct P) := by
  rw [subLineBranchDist_eq_bind, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentBranch, Distribution.bind_map_left]
  exact Distribution.bind_congr_support _ _ _ fun k _ => subLineBranchDist_map_joint_at P kind k

/-- The joint projected law is obtained by mixing independent restricted source samples. -/
theorem subLineDist_source_mixture :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      (subLinePointDist P (subLineDist P)).map subLineJointProjection =
        Distribution.bind components (subLineComponentProduct P) := by
  refine ⟨subLineComponentDist P, subLineComponentDist_isProbability P, ?_⟩
  rw [subLineDist, subLinePointDist_bind, Distribution.bind_map,
    subLineComponentDist, Distribution.bind_bind]
  refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c <;> exact subLineBranchDist_map_joint P _

/-- Integrate an arbitrary function of the two projected line-point samples. -/
theorem SubLineWitness.exists_avgOver_joint (sublines : SubLineWitness P) :
    ∃ components : Distribution (SubLineComponent P), components.IsProbability ∧
      ∀ F : SourceLinePointPair P → ℝ,
        avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
            F (subLineJointProjection (sample, sample.1.base + t • sample.1.direction)))) =
          avgOver components (fun c => avgOver (subLineComponentProduct P c) F) := by
  obtain ⟨components, hc, h⟩ := sublines.source_mixture
  refine ⟨components, hc, fun F => ?_⟩
  simp_all [← avgOver_bind, ← h, Distribution.avgOver_map, subLinePointDist, SandwichProduct.avgOver_distribution_prod]

private theorem restrictedLinePointDist_map_point
    (kind : LineKind) (i : Fin P.m) :
    (restrictedLinePointDist P kind i).map Prod.snd = uniformDistribution (PauliPoint P) := by
  rw [restrictedLinePointDist_eq_map_prod, Distribution.map_map]
  apply Distribution.prod_map_fst
  exact Distribution.prod_isProbability _ _ (subLineSeedDist_isProbability P i)
    (uniformDistribution_isProbability _)

/-- The two point blocks have the same uniform product law in each component. -/
theorem SubLineWitness.avgOver_projX_projZ (sublines : SubLineWitness P)
    (f : PointPair P → ℝ) :
    avgOver sublines.D (fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
        f (projX (directPointToPauli P (sample.1.base + t • sample.1.direction)),
          projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))) =
      avgOver (uniformDistribution (PointPair P)) f := by
  obtain ⟨components, hc, h⟩ := sublines.exists_avgOver_joint P
  refine (h (fun w => f (w.1.2, w.2.2))).trans ?_
  have hcomponent (c : SubLineComponent P) :
      (subLineComponentProduct P c).map (Prod.map Prod.snd Prod.snd) = uniformDistribution _ := by
    simp_all [subLineComponentProduct, ← Distribution.prod_map_prodMap, restrictedLinePointDist_map_point, uniformDistribution_prod]
  refine (avgOver_congr _ _ _ fun c => ?_).trans (avgOver_const_of_isProbability _ hc _)
  change avgOver (subLineComponentProduct P c) (fun w => f (Prod.map Prod.snd Prod.snd w)) = _
  rw [← Distribution.avgOver_map (subLineComponentProduct P c) (Prod.map Prod.snd Prod.snd) f,
    hcomponent]

end

end

end MIPStarRE.QPBT
