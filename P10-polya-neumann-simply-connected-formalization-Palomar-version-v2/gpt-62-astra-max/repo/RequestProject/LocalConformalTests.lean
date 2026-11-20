module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalInverse
public import RequestProject.LocalConformalGradient
public import RequestProject.DiskHarmonicModes
public import RequestProject.PlanarNotation

/-!
# Physical test functions for smooth disk modes

The local inverse supplies a compact physical test whose conformal
pullback is exactly a prescribed smooth disk test in the genuine H¹
space. This is the test needed in the weak Neumann equation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

theorem smoothTraceH1_eq_of_eqOn {U : Set ℂ} (hU : IsOpen U)
    (f g : smoothTraceTests) (hfg : EqOn (f : ℂ → ℂ) (g : ℂ → ℂ) U) :
    smoothTraceH1 U f = smoothTraceH1 U g := by
  apply h1Value_injective hU
  rw [h1Value_smoothTraceH1, h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [(smoothTraceTests_memLp U f).coeFn_toLp,
    (smoothTraceTests_memLp U g).coeFn_toLp, ae_restrict_mem hU.measurableSet]
    with z hf hg hz
  rw [hf, hg]
  exact hfg hz

theorem exists_localConformal_physical_test (Φ : ConformalDiskMap)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ∃ f : smoothTraceTests,
      (∀ z ∈ closedDisk, f (Φ.map z) = φ z) ∧
      Φ.h1Pullback Φ.lipschitzDomain (smoothTraceH1 Φ.domain f) =
        smoothTraceH1 unitDisk
          ⟨diskHarmonicCutoff φ, diskHarmonicCutoff_testFunction hφ⟩ := by
  obtain ⟨f, hf, hfe⟩ := localSmoothInverse_testFunction e hes
    (isCompact_closedBall 0 1) hsource hφ
  let f₀ : smoothTraceTests := ⟨f, hf⟩
  have hp (z : ℂ) (hz : z ∈ closedDisk) : f₀ (Φ.map z) = φ z := by
    have hp' := (hfe (e z) (mem_image_of_mem e hz)).self_of_nhds
    change f (e z) = φ (e.symm (e z)) at hp'
    rw [e.left_inv (hsource hz)] at hp'
    simpa [he] using hp'
  refine ⟨f₀, hp, ?_⟩
  rw [localConformalH1Pullback_smooth Φ]
  apply smoothTraceH1_eq_of_eqOn isOpen_ball
  intro z hz
  rw [smoothDiskCompositionLin_eq_closedDisk Φ.one_lt_radius Φ.map Φ.smooth f₀ (ball_subset_closedBall hz),
    hp z (ball_subset_closedBall hz)]
  exact (diskHarmonicCutoff_eq_closedDisk φ (ball_subset_closedBall hz)).symm

end PolyaNeumann

end
