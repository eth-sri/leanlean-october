module

public import QPBT.Observables.LineDefs

/-!
# Zero-direction mass for axis lines

This module records that the axis-line component of the line-point sampler has
no mass at zero direction.

## References

The sampler is `def:line-point-dist`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Axis-line sampling gives zero mass to zero directions, since a coordinate
direction is nonzero. This is a formalization-only consequence of
`def:line-point-dist`, paper `08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem aLinePointDist_zero_direction_mass (L : LdParams) :
    avgOver (aLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) = 0 := by
  unfold aLinePointDist
  rw [Distribution.avgOver_map]
  simp [aLineDescOf, chiIndex, LineDesc.direction, coordinateDirection, avgOver]

end

end MIPStarRE.QPBT
