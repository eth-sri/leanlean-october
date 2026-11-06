module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous

/-!
# Reverse-time Bochner energy bound

This module turns a continuous spatial Sobolev curve with separate value and
gradient energy bounds into its quotient-valued reverse-time Bochner class.
-/

 public section

open MeasureTheory Set
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A continuous spatial Sobolev curve satisfying the stated value and
gradient bounds has a reverse-time Bochner `L²(V)` representative with the
corresponding constant-one graph-norm energy bound. -/
theorem exists_reverseTimeL2V_of_continuousOn_energy
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω) {T lam B G : ℝ}
    (hT : 0 < T) (hlam : 0 < lam)
    (w : ℝ → H10HilbertGraph hΩ)
    (hw : ContinuousOn w (Set.Icc 0 T))
    (hvalue : ∀ t ∈ Set.Icc 0 T,
      ‖valueCLM hΩ (w t)‖ ^ 2 ≤ B)
    (hgradient : lam * ∫ t in Set.Ioc 0 T,
      ‖gradientCLM hΩ (w t)‖ ^ 2 ≤ G) :
    ∃ W : ReverseTimeL2V hΩ T,
      W =ᵐ[reverseTimeVolume T] w ∧
      ‖W‖ ^ 2 ≤ T * B + G / lam := by
  let sharedTerm_f591be58fb := (∫ t in Set.Ioc 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2)
  let sharedTerm_3350184be2 := (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T)
  let sharedTerm_3709607d93 := (∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T)
  let W : ReverseTimeL2V hΩ T := reverseTimeL2OfContinuousOn T w hw

  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance







  have hvalueIntegrable  := (memLp_two_reverseTime_of_continuousOn T _ ((valueCLM hΩ).continuous.comp_continuousOn hw)).integrable_norm_pow (by norm_num)


  have hgradientIoc :
      (sharedTerm_3709607d93) =
        sharedTerm_f591be58fb := by
    change (∫ t in Set.Ioo 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2) =
      sharedTerm_f591be58fb
    exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc


  refine ⟨W, coeFn_reverseTimeL2OfContinuousOn T w hw, ?_⟩
  calc
    ‖W‖ ^ 2 = ∫ t, ‖w t‖ ^ 2 ∂reverseTimeVolume T := (show (∫ t, ‖w t‖ ^ 2 ∂reverseTimeVolume T) = ‖W‖ ^ 2 by
        simpa only [W, reverseTimeL2OfContinuousOn] using
          integral_norm_sq_eq_norm_sq_toLp w (memLp_two_reverseTime_of_continuousOn T w hw)).symm
    _ = ∫ t, (‖valueCLM hΩ (w t)‖ ^ 2 + ‖gradientCLM hΩ (w t)‖ ^ 2)
        ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards with t
      exact norm_sq_h10HilbertGraph hΩ (w t)
    _ = (sharedTerm_3350184be2) +
        sharedTerm_3709607d93 :=
      integral_add hvalueIntegrable ((memLp_two_reverseTime_of_continuousOn T _ ((gradientCLM hΩ).continuous.comp_continuousOn hw)).integrable_norm_pow (by norm_num))
    _ ≤ T * B + G / lam := add_le_add (by
          calc
            (sharedTerm_3350184be2) ≤
                ∫ _ : ℝ, B ∂reverseTimeVolume T := (integral_mono_ae hvalueIntegrable (integrable_const B)
        (id
          (Filter.mp_mem (ae_restrict_mem measurableSet_Ioo)
            (Filter.univ_mem' (id fun t ht => hvalue t ⟨le_of_lt ht.left, le_of_lt ht.right⟩)))))
            _ = T * B := by
              rw [integral_const, smul_eq_mul, reverseTimeVolume_real_univ T hT]) (by
        rw [hgradientIoc]
        apply (le_div_iff₀ hlam).mpr
        simpa only [mul_comm] using hgradient)

end HypoellipticAleksandrov.Parabolic.Dirichlet
