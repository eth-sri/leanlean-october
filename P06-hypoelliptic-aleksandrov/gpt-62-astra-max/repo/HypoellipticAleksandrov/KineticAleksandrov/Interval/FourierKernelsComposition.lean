module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition

/-! # Composition of interval Fourier kernels with their zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
variable {a c : ℝ}

variable (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) (E : Set (PDE.Vec 1))

include hJ in
/-- Evaluations of the killed zero extension are measurable on ambient velocity space. -/
theorem measurable_intervalFourierKernelZero_apply (hE : MeasurableSet E) :
    Measurable (fun v => intervalFourierKernelZero K σ τ hστ ξ v E) := by
  convert ((MeasurableEmbedding.subtype_coe hJ).measurable_extend (measurable_intervalFourierKernel_apply K σ τ hστ ξ E hE) (measurable_const (a := (0 : ℂ)))) using 1
  funext v
  by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
  · exact (congrArg (fun ν : ComplexMeasure (PDE.Vec 1) => ν E)
      (intervalFourierKernelZero_coe K σ τ hστ ξ ⟨v, hv⟩)).trans (Subtype.val_injective.extend_apply (fun w => intervalFourierKernel K σ τ hστ ξ w E) (fun _ => (0 : ℂ)) ⟨v, hv⟩).symm
  · rw [intervalFourierKernelZero_of_notMem K σ τ hστ ξ v hv]
    simp_all

/-- Every interval Fourier kernel evaluation has norm at most one. -/
theorem intervalFourierKernel_apply_norm_le_one :
    ‖intervalFourierKernel K σ τ hστ ξ v E‖ ≤ 1 := by
  have he :=
    (measure_mono (subset_univ E)).trans
      (intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ v)
  exact (VectorMeasure.norm_measure_le_variation (μ := intervalFourierKernel K σ τ hστ ξ v) (ne_of_lt (he.trans_lt ENNReal.one_lt_top))).trans (by exact ENNReal.toReal_mono ENNReal.one_ne_top he)

/-- The zero extension retains the uniform evaluation bound. -/
theorem intervalFourierKernelZero_apply_norm_le_one (ξ v : PDE.Vec 1) (E : Set (PDE.Vec 1)) :
    ‖intervalFourierKernelZero K σ τ hστ ξ v E‖ ≤ 1 := by
  by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
  · exact (intervalFourierKernelZero_coe K σ τ hστ ξ ⟨v, hv⟩ ▸
      intervalFourierKernel_apply_norm_le_one K σ τ hστ ξ ⟨v, hv⟩ E)
  · rw [intervalFourierKernelZero_of_notMem K σ τ hστ ξ v hv]
    simp

/-- Chapman--Kolmogorov on an interval, integrating the killed zero extension. -/
theorem intervalFourierKernel_composition
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) (E : Set (PDE.Vec 1)) (hE : MeasurableSet E) :
    intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v E =
      ∫ᵛ v', intervalFourierKernelZero K r τ hrτ ξ v' E
        ∂[ContinuousLinearMap.mul ℝ ℂ; intervalFourierKernel K σ r hσr ξ v] := by
  let p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
    ⟨(v.1, 0), ⟨by simp, mem_univ _⟩⟩
  let f := fun v' => intervalFourierKernelZero K r τ hrτ ξ v' E
  let g := (E ×ˢ univ).indicator (fourierPhase ξ 0)
  have hf := measurable_intervalFourierKernelZero_apply K hJ r τ hrτ ξ E hE
  have hg := (continuous_fourierPhase ξ 0).measurable.indicator
    (hE.prod MeasurableSet.univ)
  have hgb : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    refine ⟨1, fun w => ?_⟩
    by_cases hw : w ∈ E ×ˢ univ
    · simpa only [g, indicator_of_mem hw] using (norm_fourierPhase ξ 0 w).le
    · simp [g, indicator_of_notMem hw]
  rw [fourierProjection_integral_complex K _ ξ _
    (intervalFourierKernel_spec K σ r hσr ξ v) f hf ⟨1, fun v' => intervalFourierKernelZero_apply_norm_le_one K r τ hrτ ξ v' E⟩]
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
    ⟨w.1.1, by simpa using w.2.1⟩
  change (∫ w', g w' ∂K.master
    (movingQuery r τ hrτ wv.1 w.1.2
      (by simp))) =
    intervalFourierKernelZero K r τ hrτ ξ wv.1 E * fourierPhase ξ 0 w.1
  rw [(intervalFourierKernelZero_coe K r τ hrτ ξ wv), ← intervalFourierKernel_eq_startingPosition K hJ hcov r τ hrτ ξ wv w.1.2,
    fourierProjection_spec K _ ξ E hE,
    ← integral_indicator (hE.prod MeasurableSet.univ), ← integral_mul_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w'
  by_cases hw' : w'.1 ∈ E
  · simp only [g, indicator_of_mem (show w' ∈ E ×ˢ univ from ⟨hw', mem_univ _⟩)]
    rw [fourierPhase_factor ξ 0 w.1 w', mul_comm]
    rfl
  · simp [g, indicator_of_notMem
      (show w' ∉ E ×ˢ univ from fun hw => hw' hw.1)]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
