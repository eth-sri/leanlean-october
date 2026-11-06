module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalInverse
public import RequestProject.LocalConformalGradient
public import RequestProject.DiskHarmonicModes

/-!
# Physical test functions for smooth disk modes

The local inverse supplies a compact physical test whose conformal
pullback is exactly a prescribed smooth disk test in the genuine H¹
space. This is the test needed in the weak Neumann equation.
-/

public section

open scoped ContDiff



namespace PolyaNeumann

open MeasureTheory Set Metric

theorem smoothTraceH1_eq_of_eqOn  (hU : IsOpen U)
    (f g : smoothTraceTests) (hfg : EqOn (f : PlaneMap) (g : PlaneMap) U) :
    smoothTraceH1 U f = smoothTraceH1 U g := by
  apply h1Value_injective hU
  rw [h1Value_smoothTraceH1, h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [(smoothTraceTests_memLp U f).coeFn_toLp,
    (smoothTraceTests_memLp U g).coeFn_toLp, ae_restrict_mem hU.measurableSet]
    with z hf hg hz
  rw [hf, hg]
  exact hfg hz

theorem exists_localConformal_physical_test  hR F
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    hL
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) 
    (hC : DiskInverseJacobianBound F C)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
     hφ :
    ∃ f : smoothTraceTests,
      (∀ z ∈ closedUnitDisk, f (F z) = φ z) ∧
      localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' unitDisk) f) =
        smoothTraceH1 unitDisk
          ⟨diskHarmonicCutoff φ, diskHarmonicCutoff_testFunction hφ⟩ := by
  obtain ⟨f, hf, hfe⟩ := localSmoothInverse_testFunction e hes
    (isCompact_closedBall 0 1) hsource hφ
  let f₀ : smoothTraceTests := ⟨f, hf⟩
  have hp (z : ℂ) (hz : z ∈ closedUnitDisk) : f₀ (F z) = φ z := by
    have hp' := (hfe (e z) (mem_image_of_mem e hz)).self_of_nhds
    change f (e z) = φ (e.symm (e z)) at hp'
    rw [e.left_inv (hsource hz)] at hp'
    simpa  [he] using hp'
  refine ⟨f₀, hp, ?_⟩
  rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC]
  apply smoothTraceH1_eq_of_eqOn isOpen_ball
  intro z hz
  rw [smoothDiskCompositionLin_eq_closedDisk hR F hFs f₀ (ball_subset_closedBall hz),
    hp z (ball_subset_closedBall hz)]
  exact (diskHarmonicCutoff_eq_closedDisk φ (ball_subset_closedBall hz)).symm

end PolyaNeumann
