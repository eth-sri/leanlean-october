module

public import RequestProject.LocalConformalInverse
public import RequestProject.LocalConformalGradient
public import RequestProject.DiskHarmonicModes

/-!
# Physical test functions for smooth disk modes

The local inverse supplies a compact physical test whose conformal
pullback is exactly a prescribed smooth disk test in the genuine H¹
space. This is the test needed in the weak Neumann equation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

theorem smoothTraceH1_eq_of_eqOn {U : Set ℂ} (hU : IsOpen U)
    (f g : smoothTraceTests) (hfg : EqOn (f : ℂ → ℂ) (g : ℂ → ℂ) U) :
    smoothTraceH1 U f = smoothTraceH1 U g := by
  apply h1Value_injective hU
  rw [h1Value_smoothTraceH1, h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [(smoothTraceTests_memLp U f).coeFn_toLp, (smoothTraceTests_memLp U g).coeFn_toLp, ae_restrict_mem hU.measurableSet] with x; grind

theorem exists_localConformal_physical_test {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ f : smoothTraceTests,
      (∀ z ∈ closedBall (0 : ℂ) 1, f (F z) = φ z) ∧
      coords.pullback (smoothTraceH1 (F '' ball (0 : ℂ) 1) f) =
        smoothTraceH1 (ball (0 : ℂ) 1)
          ⟨diskHarmonicCutoff φ, diskHarmonicCutoff_testFunction hφ⟩ := by
  obtain ⟨f, hf, hfe⟩ := localSmoothInverse_testFunction coords.model coords.smooth_inv
    (isCompact_closedBall (0 : ℂ) 1) coords.source hφ
  let e := coords.model
  have he : (e : ℂ → ℂ) = F := coords.model_eq
  let f₀ : smoothTraceTests := ⟨f, hf⟩
  have hp (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : f₀ (F z) = φ z := by
    have hp' := (hfe (e z) (mem_image_of_mem e hz)).self_of_nhds
    change f (e z) = φ (e.symm (e z)) at hp'
    rw [e.left_inv (coords.source hz)] at hp'
    aesop
  refine ⟨f₀, hp, ?_⟩
  rw [localConformalH1Pullback_smooth coords.one_lt_radius F coords.smooth coords.bounded
    coords.lipschitz coords.holomorphic coords.injOn coords.lower]
  apply smoothTraceH1_eq_of_eqOn isOpen_ball
  intro z hz
  rw [smoothDiskCompositionLin_eq_closedDisk coords.one_lt_radius F coords.smooth f₀ (ball_subset_closedBall hz),
    hp z (ball_subset_closedBall hz)]
  exact (diskHarmonicCutoff_eq_closedDisk φ (ball_subset_closedBall hz)).symm

end PolyaNeumann

end
