module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsComposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels
import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation

/-! # Total-variation product bound for Fourier kernel composition -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/- Temporal Fourier composition contracts total variation by the largest terminal norm. -/
theorem intervalFourierKernel_totalVariation_composition {a c }
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) :
    totalVariationNorm (intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤
      totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) *
        ⨆ v' : PDE.oneDimensionalAxisBox a c,
          totalVariationNorm (intervalFourierKernel K r τ hrτ ξ v') := by
  classical
  let ν := intervalFourierKernel K σ r hσr ξ v
  let ν' := intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v
  let C := ⨆ v' : PDE.oneDimensionalAxisBox a c,
    totalVariationNorm (intervalFourierKernel K r τ hrτ ξ v')
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
      _ ≤ ∑ E ∈ P, ∫⁻ v', ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        apply Finset.sum_le_sum
        intro E hEP
        have _h_xinl_0 : intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v E =
      ∫ᵛ v', intervalFourierKernelZero K r τ hrτ ξ v' E
        ∂[ContinuousLinearMap.mul ℝ ℂ; intervalFourierKernel K σ r hσr ξ v] := by
          have hE := (hPm E hEP)
          let p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
            ⟨(v.1, 0), ⟨by simpa only [movingDomain_stationary] using v.2, mem_univ _⟩⟩
          let f := fun v' => intervalFourierKernelZero K r τ hrτ ξ v' E
          let g := (E ×ˢ univ).indicator (fourierPhase ξ (0 : PDE.Vec 1))
          have hf : Measurable f := measurable_intervalFourierKernelZero_apply K hJ r τ hrτ ξ E hE
          have hg : Measurable g := (continuous_fourierPhase ξ 0).measurable.indicator
            (hE.prod MeasurableSet.univ)
          have hgb : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
            refine ⟨1, fun w => ?_⟩
            by_cases hw : w ∈ E ×ˢ univ
            · simpa only [g, indicator_of_mem hw] using (norm_fourierPhase ξ 0 w).le
            · simp only [g, indicator_of_notMem hw, norm_zero, zero_le_one]
          have hfb : ∃ C : ℝ, ∀ v', ‖f v'‖ ≤ C :=
            ⟨1, fun v' => intervalFourierKernelZero_apply_norm_le_one K r τ hrτ ξ v' E⟩
          rw [fourierProjection_integral_complex K _ ξ _
            (intervalFourierKernel_spec K σ r hσr ξ v) f hf hfb]
          change _ = ∫ w, f w.1 * fourierPhase ξ 0 w
            ∂K.master (evolutionQueryOfState (PDE.oneDimensionalAxisBox a c)
              stationary σ r hσr p)
          rw [intervalFourierKernel_spec K σ τ (hσr.trans hrτ) ξ v E hE,
            ← integral_indicator (hE.prod MeasurableSet.univ)]
          change (∫ w, g w ∂K.master
            (evolutionQueryOfState (PDE.oneDimensionalAxisBox a c)
              stationary σ τ (hσr.trans hrτ) p)) = _
          rw [master_integral_composition K hJ hcomp σ r τ hσr hrτ p g hg hgb,
            master_integral_eq_fiber K hJ σ r hσr p
              (fun w => f w.1 * fourierPhase ξ 0 w)
              ((hf.comp measurable_fst).mul (continuous_fourierPhase ξ 0).measurable)]
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro w
          let wv : PDE.oneDimensionalAxisBox a c :=
            ⟨w.1.1, by simpa only [movingDomain_stationary] using w.2.1⟩
          have he := intervalFourierKernelZero_coe K r τ hrτ ξ wv
          change (∫ w', g w' ∂K.master
            (movingQuery r τ hrτ wv.1 w.1.2
              (by simpa only [movingDomain_stationary] using wv.2))) =
            intervalFourierKernelZero K r τ hrτ ξ wv.1 E * fourierPhase ξ 0 w.1
          have _h_xinl_0 : fourierProjection K (movingQuery r τ hrτ wv.1 w.1.2
              (by simpa only [movingDomain_stationary] using wv.2)) ξ =
              intervalFourierKernel K r τ hrτ ξ wv := by
            let z := w.1.2
            let p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary r :=
              ⟨(wv.1, 0), by exact ⟨by simpa only [movingDomain_stationary] using wv.2, mem_univ _⟩⟩
            have hq : evolutionQueryOfState (PDE.oneDimensionalAxisBox a c) stationary r τ hrτ
                (evolutionStateShift (PDE.oneDimensionalAxisBox a c) stationary r z p) =
                movingQuery r τ hrτ wv.1 z
                  (by simpa only [movingDomain_stationary] using wv.2) := by
              apply Subtype.ext
              simp only [evolutionQueryOfState, evolutionStateShift, evolutionAmbientStateShift,
                movingQuery, p, zero_add]
            have ht := fourierProjection_translation hJ K hcov r τ hrτ p z ξ
            rw [hq] at ht
            exact ht
          rw [he, ← _h_xinl_0,
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
                (∫⁻ v', ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ ∂ν.variation))))
      _ = ∫⁻ v', ∑ E ∈ P, ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        rw [lintegral_finsetSum P (fun E hEP =>
          (measurable_intervalFourierKernelZero_apply K hJ r τ hrτ ξ E (hPm E hEP)).enorm)]
      _ ≤ ∫⁻ v', C ∂ν.variation := by
        apply lintegral_mono
        intro v'
        change (∑ E ∈ P, ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ) ≤ C
        by_cases hv' : v' ∈ PDE.oneDimensionalAxisBox a c
        · rw [intervalFourierKernelZero_coe K r τ hrτ ξ ⟨v', hv'⟩]
          exact (VectorMeasure.le_variation (intervalFourierKernel K r τ hrτ ξ ⟨v', hv'⟩)
            MeasurableSet.univ (fun E _ => subset_univ E) hPd).trans
            (le_iSup (fun x => totalVariationNorm (intervalFourierKernel K r τ hrτ ξ x))
              ⟨v', hv'⟩)
        · simp only [intervalFourierKernelZero_of_notMem K r τ hrτ ξ v' hv',
            zero_apply, enorm_zero, Finset.sum_const_zero, zero_le]
      _ = totalVariationNorm ν * C := by
        rw [lintegral_const, mul_comm]
  exact (not_lt_of_ge hsum) hPgt

end HypoellipticAleksandrov.KineticAleksandrov.Interval
