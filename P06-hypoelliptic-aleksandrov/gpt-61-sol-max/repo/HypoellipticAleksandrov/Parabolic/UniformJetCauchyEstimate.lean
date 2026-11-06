module

public import HypoellipticAleksandrov.Parabolic.SobolevGridFTC
public import HypoellipticAleksandrov.Parabolic.FiniteSupportL1L2
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
public import PDEFoundation.Calculus.RegularityOrder


section
open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
private alias _sharedProof_185_4 := HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset
end


 public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

/-- Coordinate iterated derivatives do not enlarge topological support. -/
theorem coordinateIteratedFDeriv_tsupport_subset
    {d : ℕ} (alpha : TimeVelocityMultiIndex d)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) ⊆
      tsupport f := (_sharedProof_185_4 alpha f)


/-- The grid-FTC sup estimate with the exact common compact-support constant. -/
theorem abs_le_sqrt_volume_mul_eLpNorm_coordinateIteratedFDeriv_allOnes
    (d : ℕ)
    (K : HypoellipticAleksandrov.Parabolic.Region d)
    (hK : IsCompact K)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f)
    (hfsupp : tsupport f ⊆ K)
    (z : TimeVelocity d) :
    |f z| ≤ Real.sqrt (volume.real K) *
      ENNReal.toReal
        (eLpNorm
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (TimeVelocityMultiIndex.allOnes d) f)
          (2 ) (volume )) := by
  let g := TimeVelocityMultiIndex.coordinateIteratedFDeriv
    (TimeVelocityMultiIndex.allOnes d) f

  have hgsupp  :=
    (subset_tsupport g).trans
      ((coordinateIteratedFDeriv_tsupport_subset _ f).trans hfsupp)




  exact (abs_le_integral_abs_coordinateIteratedFDeriv_allOnes d f hf (hK.of_isClosed_subset (isClosed_tsupport (f := f)) hfsupp) z).trans
    (integral_abs_le_sqrt_volume_mul_eLpNorm K hK.measurableSet
      hK.measure_lt_top g ((show ContDiff ℝ PDE.smoothOrder g by
          rw [contDiff_infty]
          intro m
          unfold g TimeVelocityMultiIndex.coordinateIteratedFDeriv
          have hi := (contDiff_infty.mp hf
            (m + (TimeVelocityMultiIndex.allOnes d).order)).iteratedFDeriv_right
            (m := m)
            (i := (TimeVelocityMultiIndex.allOnes d).coordinateList.length) (by simp)
          exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
            (fun i ↦ timeVelocityBasis
              ((TimeVelocityMultiIndex.allOnes d).coordinateList.get i)))).clm_apply hi).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hK hgsupp)) hgsupp)

end HypoellipticAleksandrov.Parabolic
