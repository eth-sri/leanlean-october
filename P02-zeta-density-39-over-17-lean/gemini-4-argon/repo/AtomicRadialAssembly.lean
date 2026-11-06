module
public import AtomicRadialFubini

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

theorem retained_cubic_radial_assembly (ν : Measure ℝ) [IsFiniteMeasure ν] {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (L : ℝ) (S : Finset ℤ) :
    kernelCubic ν (retainedPoissonKernel (volume.restrict (Icc l u)) a L S) =
      (L:ℂ)^3 * ∑ m₁ ∈ S, ∑ m₂ ∈ S, ∑ m₃ ∈ S,
        ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
          radialKernel a L (m₁,m₂,m₃) p * ratioFourierProduct (measureFourier ν) p := by
  obtain ⟨B,hB,hb⟩ := assembly_cutoff_bound ha.continuous hs
  have hbF (ξ : ℝ) : ‖measureFourier ν ξ‖ ≤ ν.real univ := by
    simpa only [measureFourier,one_mul] using norm_integral_le_of_norm_le_const
      (μ := ν) (f := fun t => phase (-ξ*t)) (C := 1)
      (Filter.Eventually.of_forall (fun t => (phase_norm _).le))
  rw [retainedPoissonKernel_cubic ν _ ha.continuous.measurable hB.le hb]
  exact retained_cubic_radial_sum ha hl hlu hs
    (operator_measureFourier_continuous ν) ENNReal.toReal_nonneg hbF L S

