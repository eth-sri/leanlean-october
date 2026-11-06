module
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ZetaAppendix

@[expose] public section
namespace ZetaAppendix
open Real Complex MeasureTheory Finset Filter Topology Set Summable

/-- Public form of the non-stationary phase estimate used in the sharp-zeta
Poisson argument. -/
theorem nonstationary_phase_integral_bound {a b : ℝ} (ha : a < b)
    (φ : ℝ → ℝ) (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
    (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b,
        (h t : ℂ) * Complex.exp (2 * Real.pi * I * (φ t : ℂ))‖ ≤
      |g a| / Real.pi := by
  simpa only [e] using
    lemma_aachmonophase ha φ hφ_C1 hφ'_ne0 h g hg hg_cont hg_mon

end ZetaAppendix
