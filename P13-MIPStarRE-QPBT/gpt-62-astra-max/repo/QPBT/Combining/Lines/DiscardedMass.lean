module

public import QPBT.Combining.Lines.ZeroDirectionMass
public import QPBT.Combining.Lines.DiagonalResampling

/-! # Discarded zero-direction mass

## References

Paper `lem:qld-xz-lines`, lines 950--963.
-/

@[expose] public section

namespace MIPStarRE.QPBT
open MIPStarRE.LDT
noncomputable section

variable (L : LdParams)

/-- Under the unchanged diagonal line-point law, zero projected directions have
probability at most the inverse field size: the final unprojected direction coordinate must
vanish and is uniform. Source: `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. This formalization-only bound
supports the collision restriction used in the paired-line construction. -/
theorem dLinePointDist_zero_direction_mass_le :
    avgOver (dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / Fintype.card (ScalarQ L) := by
  classical
  let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
  let coord : LdIndex L := .inr last
  have hmap : (uniformDistribution (LdSpace L)).map (fun raw => raw coord) =
      uniformDistribution (ScalarQ L) := by
    change (uniformDistribution (LdSpace L)).map
      (fun raw => (Equiv.funSplitAt coord (ScalarQ L) raw).1) = _
    rw [← Distribution.map_map, uniformDistribution_map_equiv,
      uniformDistribution_map_fst]
  have hzero : avgOver (uniformDistribution (LdSpace L))
      (fun raw => if raw coord = 0 then 1 else 0) =
      1 / Fintype.card (ScalarQ L) := by
    rw [← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun raw => raw coord) (fun value => if value = 0 then (1 : ℝ) else 0), hmap]
    simp [avgOver, uniformDistribution_weight_apply]
  unfold dLinePointDist clDistribution
  rw [Distribution.avgOver_map, Distribution.avgOver_map]
  refine le_trans (avgOver_mono _ _ _ ?_) hzero.le
  intro raw
  rw [dLineDescOf_ldDLineCL]
  split_ifs with hdir hcoord hcoord
  · exact le_rfl
  · exfalso
    apply hcoord
    have hlast := congrFun hdir last
    change prefixProjection _
      (LdSpace.direction raw) last = 0 at hlast
    have hindex : ¬ last.val < (chiIndex L (LdSpace.seed raw)).val := by
      have := (chiIndex L (LdSpace.seed raw)).isLt
      dsimp [last]
      omega
    simpa [prefixProjection, hindex, LdSpace.direction, coord] using hlast
  · norm_num
  · exact le_rfl

end
end MIPStarRE.QPBT
