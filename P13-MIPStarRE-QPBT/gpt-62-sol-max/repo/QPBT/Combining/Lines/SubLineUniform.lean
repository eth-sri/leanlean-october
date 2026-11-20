module

public import QPBT.Combining.Lines.RestrictedAverage
public import QPBT.Combining.Lines.SubLineExtended

/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. In averaged form this is the resampling identity used
by the line-point samplers: a quantity of the canonical representative and of
the point may equivalently be averaged over the point and an independent
uniform affine parameter along the direction. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/

/-- For the zero direction the canonical representative map of
`def:line-representative` is the identity, since the span of the zero vector
is trivial.  Blueprint `def:line-representative`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
theorem lineRepMap_zero_apply {K : Type*} [Field K] {m : ℕ}
    (u : Fin m → K) : lineRepMap (0 : Fin m → K) u = u := by
  simp [lineRepMap_apply]

/-! ## Uniform points of a line -/

/-- Replacing the affine parameter of a uniform point by an independent
uniform parameter preserves uniformity. For a nonzero direction this swaps
its old affine parameter with the new one. -/
theorem uniformDistribution_map_lineRepMap_add_smul {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K) :
    (uniformDistribution ((Fin m → K) × K)).map
        (fun w => lineRepMap v w.1 + w.2 • v) = uniformDistribution (Fin m → K) := by
  by_cases hv : v = 0
  · subst v
    simpa only [lineRepMap_zero_apply, smul_zero, add_zero] using
      (uniformDistribution_map_fst (α := Fin m → K) (β := K))
  let swap (s : (Fin m → K) × K) :=
    (lineRepMap v s.1 + s.2 • v, directLineRepParameter v s.1)
  have hinv : Function.Involutive swap := by
    intro s
    have e := lineRepMap_add_smul v (lineRepMap v s.1) s.2
    rw [lineRepMap_apply_self] at e
    apply Prod.ext
    · simpa only [swap, e] using (directLineRepParameter_spec v s.1).symm
    · exact directLineRepParameter_eq_of_nonzero hv (by rw [e])
  exact uniformDistribution_map_fst_of_equiv ⟨swap, swap, hinv, hinv⟩ _ fun _ => rfl

/-! ## Resampling a uniform point along its canonical line -/

/-- Finite-average form of the parameterization above: a uniformly random
point may be replaced by a fresh uniform affine parameter on the line through
its canonical representative, while the representative itself is kept in the
sampled value.  The zero direction is included, since the parameterization
has constant fibers there too.  This formalization-only identity is the
common core of the axis and diagonal line-point resampling identities used at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`;
the canonical representative map is blueprint `def:line-representative`. -/
theorem avgOver_uniform_lineRepMap_resample_parameter {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K)
    (value : (Fin m → K) → (Fin m → K) → ℝ) :
    avgOver (uniformDistribution (Fin m → K))
        (fun point => value (lineRepMap v point) point) =
      avgOver (uniformDistribution (Fin m → K)) (fun point =>
        avgOver (uniformDistribution K) (fun param =>
          value (lineRepMap v point) (lineRepMap v point + param • v))) := by
  have hmap := uniformDistribution_map_lineRepMap_add_smul v
  have havg := congrArg (fun dist => avgOver dist
    (fun point => value (lineRepMap v point) point)) hmap
  rw [Distribution.avgOver_map, uniformDistribution_prod,
    SandwichProduct.avgOver_distribution_prod] at havg
  simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm

theorem directPointToPauli_coordinateDirection (P : AdmissibleParams)
    (k : Fin P.extendedDirectLd.m) :
    directPointToPauli P (coordinateDirection k) = coordinateDirection k := rfl

end

end MIPStarRE.QPBT
