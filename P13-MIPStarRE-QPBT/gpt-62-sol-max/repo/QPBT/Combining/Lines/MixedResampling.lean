module

public import QPBT.Combining.Lines.SubLineUniform

/-!
# Mixed line-point parameter resampling

This module combines the axis and diagonal resampling identities for the equal
mixture defining the line-point distribution.

## References

The resampling supports the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`. The
mixed line-point law is `def:line-point-dist` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Resample the point conditionally on the canonical line, allowing a vanishing direction. -/
private theorem avgOver_lineKindPointDist_resample_parameter (L : LdParams) (kind : LineKind)
    (value : (LinePointSample L) → ℝ) :
    avgOver (lineKindPointDist L kind) value =
      avgOver (lineKindPointDist L kind) (fun sample =>
        avgOver (uniformDistribution (ScalarQ L)) (fun t =>
          value (sample.1, sample.1.base + t • sample.1.direction))) := by
  rw [lineKindPointDist_eq_map_blocks]
  simp only [Distribution.avgOver_map]
  let f (p : LdPoint L) (w : ScalarQ L × (LdPoint L)) :=
    value (lineDescOfBlock L kind (p, w), p)
  let g (p : LdPoint L) (w : ScalarQ L × (LdPoint L)) :=
    let line := lineDescOfBlock L kind (p, w)
    avgOver (uniformDistribution (ScalarQ L)) (fun t => value (line, line.base + t • line.direction))
  let μ := uniformDistribution ((LdPoint L) × (ScalarQ L × (LdPoint L)))
  change avgOver μ (fun w => f w.1 w.2) = avgOver μ (fun w => g w.1 w.2)
  dsimp only [μ]
  rw [avgOver_uniform_prod_swap f, avgOver_uniform_prod_swap g]
  refine avgOver_congr _ _ _ fun w => ?_
  let l := fun p => lineDescOfBlock L kind (p, w)
  let v := (l 0).direction
  have hdir p : (l p).direction = v := by cases kind <;> rfl
  have hbase p : (l p).base = lineRepMap v p := by cases kind <;> rfl
  have hl p : l (lineRepMap v p) = l p := by
    cases kind
    · exact lineDesc_axis_congr (lineRepMap_apply_self _ _) _ _
    · exact lineDesc_diagonal_congr (lineRepMap_apply_self _ _) rfl _ _ _ _
  change avgOver (uniformDistribution (LdPoint L)) (fun p => value (l p, p)) =
    avgOver (uniformDistribution (LdPoint L)) (fun p =>
      avgOver (uniformDistribution (ScalarQ L)) fun t => value (l p, (l p).base + t • (l p).direction))
  simp only [hbase, hdir]
  simpa only [hl] using
    avgOver_uniform_lineRepMap_resample_parameter v (fun b p => value (l b, p))

/-- Resampling a uniform affine parameter on a sampled line preserves the
unconditional mixed line-point law, including zero-direction diagonal fibers.
This formalization-only identity combines the axis and diagonal cases of the
conditional sampling used at paper line 955. It is recorded in blueprint
`cor:line-point-parameter-resampling`. -/
theorem avgOver_linePointDist_resample_parameter (L : LdParams)
    (value : (LinePointSample L) → ℝ) :
    avgOver (linePointDist L) value =
      avgOver (linePointDist L) (fun sample =>
        avgOver (uniformDistribution (ScalarQ L)) (fun param =>
          value (sample.1, sample.1.base + param • sample.1.direction))) := by
  rw [linePointDist, avgOver_mix, avgOver_mix]
  exact congrArg₂ (fun a b => 1 / 2 * a + (1 - 1 / 2) * b)
    (avgOver_lineKindPointDist_resample_parameter L .axis value)
    (avgOver_lineKindPointDist_resample_parameter L .diagonal value)

end

end MIPStarRE.QPBT
