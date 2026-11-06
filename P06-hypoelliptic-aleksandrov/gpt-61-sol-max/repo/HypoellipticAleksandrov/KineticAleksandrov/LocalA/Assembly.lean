module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.AssemblyInner
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.AssemblyGeometry

/-! # The joint Borel estimate, conditional on the smooth joint statement

The constants are selected before all data. Compact correctors give the estimates
on shifted inner cylinders. Fixed fractions are exhausted below the terminal face;
all spatial orders refer to the same original solution.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Holder
open scoped Matrix.Norms.Elementwise

/-- The smooth joint local estimate implies exactly the Borel joint statement. -/
theorem localTimeVelocityRegularity_of_smooth :
    SmoothLocalRegularityStatement → LocalTimeVelocityRegularityStatement := by
  intro hsmooth hH hLE d hd lam Lam hlam hLam
  obtain ⟨C_m, C, α, hCm, hC, hα, hα1, hest⟩ :=
    hsmooth hH hLE d hd lam Lam hlam hLam
  refine ⟨C_m, C, α, hCm, hC, hα, hα1, ?_⟩
  intro A hA hs hlo hhi P₀ R hR u hc hu he
  have hab  :=
    ((isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image hc).mono
      (image_mono subset_closure)
  have hbb  :=
    ((isCompact_closure_backwardCylinder P₀ R hR).bddBelow_image hc).mono
      (image_mono subset_closure)
  have hKD n : closure (backwardCylinder (borelInnerCentre P₀ R n)
      (borelInnerRadius R hR n)) ⊆ backwardCylinder P₀ R := by
    have hh := closure_reflected_innerCylinder_subset P₀ R hR _
      (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
    rw [kineticReflection_image_innerCylinder] at hh
    exact hh
  have hi n := borel_inner_joint_estimates hH hLE hd lam Lam hlam hLam
    C_m hCm C α hest A hA hs hlo hhi P₀ R hR u hu he
    (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
    (borelInnerRadius_pos R hR n) (hKD n)
  have hosc n  :=
    oscillationOn_mono (backwardCylinder_nonempty _ (borelInnerRadius_pos R hR n))
      (subset_closure.trans (hKD n)) hab hbb
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨P₁, r, hr, hsub, hPin⟩ :=
      exists_inner_margin_cylinder (isOpen_backwardCylinder P₀ R hR) hP
    exact (borel_inner_joint_estimates hH hLE hd lam Lam hlam hLam C_m hCm C α
      hest A hA hs hlo hhi P₀ R hR u hu he P₁ r hr hsub).1 P hPin |>.1
  · intro m hm P hP

    have hevent := borel_inner_fraction_exhaustion P₀ R hR (3 / 4) (by norm_num) P (show _ by
        convert hP using 1; ring)

    have ht := ((borelInnerRadius_tendsto R hR).pow (3 * m)).mul_const
      ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖
    exact le_of_tendsto ht (by
        filter_upwards [hevent] with n hn

        exact ((hi n).1 P (show _ by
            convert hn using 1; ring)).2 m hm |>.trans
          (mul_le_mul_of_nonneg_left (hosc n) (hCm m)))
  · intro P hP Q hQ


    have hp := borel_inner_fraction_exhaustion P₀ R hR (1 / 2) (by norm_num) P (by
        convert hP using 1; ring)
    have hq := borel_inner_fraction_exhaustion P₀ R hR (1 / 2) (by norm_num) Q (by
        convert hQ using 1; ring)

    have ht := ((tendsto_const_nhds (x := kineticIncrement P₀ P Q)).div
      (borelInnerRadius_tendsto R hR) (ne_of_gt hR)).rpow_const (Or.inr hα.le)
    exact ge_of_tendsto (ht.const_mul (C * oscillationOn u (backwardCylinder P₀ R))) (by
        filter_upwards [hp, hq] with n hnP hnQ


        have hh := (hi n).2 P (show _ by convert hnP using 1; ring) Q (show _ by convert hnQ using 1; ring)

        rw [(show kineticIncrement (borelInnerCentre P₀ R n) P Q =
            kineticIncrement P₀ P Q from rfl)] at hh
        exact hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hosc n) hC.le) (Real.rpow_nonneg
            (div_nonneg (by
              unfold kineticIncrement
              exact add_nonneg
                (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
                  (PDE.vecEuclideanNorm_nonneg _))
                (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _))
              (borelInnerRadius_pos R hR n).le) α)))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
