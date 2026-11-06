module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # Nested source cylinders and a finite half-density alternative -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/- Increasing a positive radius enlarges the literal Euclidean kinetic cylinder. -/
theorem backwardCylinder_radius_mono {d } (P0 : KineticPoint d) {r R }
    (hr : 0 < r) (hrR : r ≤ R) : backwardCylinder P0 r ⊆ backwardCylinder P0 R := by
  have hR := hr.trans_le hrR
  have hsq := pow_le_pow_left₀ hr.le hrR 2
  have hcube := pow_le_pow_left₀ hr.le hrR 3
  intro P hP
  refine ⟨by linarith only [hP.1, hsq], hP.2.1, ?_, ?_⟩
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
    exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hP.2.2.1).trans_le hrR
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
    exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp
      hP.2.2.2).trans_le hcube

/- At least one side of a real value threshold occupies half a finite sampling region. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
