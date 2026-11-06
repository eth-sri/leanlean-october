module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Total-variation product bound for Fourier kernel composition -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/- Temporal Fourier composition contracts total variation by the largest terminal norm. -/
theorem fourierKernel_totalVariation_composition {d }
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0)
      MeasurableSet.univ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤
      totalVariationNorm (fourierKernel K σ r hσr ξ v) *
        ⨆ v' : PDE.Vec d, totalVariationNorm (fourierKernel K r τ hrτ ξ v') := by
  classical
  let ν := fourierKernel K σ r hσr ξ v
  let ν' := fourierKernel K σ τ (hσr.trans hrτ) ξ v
  let C := ⨆ v' : PDE.Vec d, totalVariationNorm (fourierKernel K r τ hrτ ξ v')
  have hB : ‖ContinuousLinearMap.mul ℝ ℂ‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal
      (LinearMap.mkContinuous₂_norm_le (LinearMap.mul ℝ ℂ) zero_le_one
        (fun x y => by simpa only [LinearMap.mul_apply', one_mul] using norm_mul_le x y))).trans_eq
      ENNReal.ofReal_one
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨P, _, hPd, hPm, hPgt⟩ :=
    VectorMeasure.exists_lt_sum_of_lt_variation ν' MeasurableSet.univ hlt
  have hsum : ∑ E ∈ P, ‖ν' E‖ₑ ≤ totalVariationNorm ν * C := by
    calc
      _ ≤ ∑ E ∈ P, ∫⁻ v', ‖fourierKernel K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        apply Finset.sum_le_sum
        intro E hEP
        have _h_xinl_0 : fourierKernel K σ τ (hσr.trans hrτ) ξ v E =
      ∫ᵛ v', fourierKernel K r τ hrτ ξ v' E
        ∂[ContinuousLinearMap.mul ℝ ℂ; fourierKernel K σ r hσr ξ v] := by
          have hE := (hPm E hEP)
          let p : EvolutionState (wholeSpace d) (fun _ => 0) σ :=
            ⟨(v, 0), (wholeSpaceQuery σ r hσr v 0).property.2⟩
          let f := fun v' => fourierKernel K r τ hrτ ξ v' E
          let g := (E ×ˢ univ).indicator (fourierPhase ξ (0 : PDE.Vec d))
          have hf : Measurable f := measurable_fourierKernel_apply K r τ hrτ ξ E hE
          have hg : Measurable g := (continuous_fourierPhase ξ 0).measurable.indicator
            (hE.prod MeasurableSet.univ)
          have hgb : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
            refine ⟨1, fun w => ?_⟩
            by_cases hw : w ∈ E ×ˢ univ
            · simpa only [g, indicator_of_mem hw] using (norm_fourierPhase ξ 0 w).le
            · simp only [g, indicator_of_notMem hw, norm_zero, zero_le_one]
          have hfb : ∃ C : ℝ, ∀ v', ‖f v'‖ ≤ C :=
            ⟨1, fun v' => fourierKernel_apply_norm_le_one K r τ hrτ ξ v' E⟩
          rw [fourierProjection_integral_complex K _ ξ _
            (fourierKernel_spec K σ r hσr ξ v) f hf hfb]
          change _ = ∫ w, f w.1 * fourierPhase ξ 0 w
            ∂K.master (evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ r hσr p)
          rw [fourierKernel_spec K σ τ (hσr.trans hrτ) ξ v E hE,
            ← integral_indicator (hE.prod MeasurableSet.univ)]
          change (∫ w, g w ∂K.master
            (evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ τ (hσr.trans hrτ) p)) = _
          rw [master_integral_composition K MeasurableSet.univ hcomp σ r τ hσr hrτ p g hg hgb,
            master_integral_eq_fiber K MeasurableSet.univ σ r hσr p
              (fun w => f w.1 * fourierPhase ξ 0 w)
              ((hf.comp measurable_fst).mul (continuous_fourierPhase ξ 0).measurable)]
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro w
          change (∫ w', g w' ∂K.master (wholeSpaceQuery r τ hrτ w.1.1 w.1.2)) =
            fourierKernel K r τ hrτ ξ w.1.1 E * fourierPhase ξ 0 w.1
          rw [← fourierKernel_eq_startingPosition K hcov r τ hrτ ξ w.1.1 w.1.2,
            fourierProjection_spec K _ ξ E hE,
            ← integral_indicator (hE.prod MeasurableSet.univ), ← integral_mul_const]
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro w'
          by_cases hw' : w'.1 ∈ E
          · simp only [g, indicator_of_mem (show w' ∈ E ×ˢ univ from ⟨hw', mem_univ _⟩)]
            rw [fourierPhase_factor ξ 0 w.1 w', mul_comm]
            rfl
          · simp only [g, indicator_of_notMem
              (show w' ∉ E ×ˢ univ from fun hw => hw' hw.1), zero_mul]
        rw [_h_xinl_0]
        exact (VectorMeasure.enorm_integral_le_lintegral_enorm).trans
          (by
            simpa only [one_mul] using
              (mul_le_mul' hB (le_refl
                (∫⁻ v', ‖fourierKernel K r τ hrτ ξ v' E‖ₑ ∂ν.variation))))
      _ = ∫⁻ v', ∑ E ∈ P, ‖fourierKernel K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        rw [lintegral_finsetSum P (fun E hEP =>
          (measurable_fourierKernel_apply K r τ hrτ ξ E (hPm E hEP)).enorm)]
      _ ≤ ∫⁻ v', C ∂ν.variation := by
        apply lintegral_mono
        intro v'
        exact (VectorMeasure.le_variation (fourierKernel K r τ hrτ ξ v')
          MeasurableSet.univ (fun E _ => subset_univ E) hPd).trans
          (le_iSup (fun x => totalVariationNorm (fourierKernel K r τ hrτ ξ x)) v')
      _ = totalVariationNorm ν * C := by
        rw [lintegral_const, mul_comm]
  exact (not_lt_of_ge hsum) hPgt

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
