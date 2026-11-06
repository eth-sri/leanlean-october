module

public import RequestProject.LocalConformalTests
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalMassForcing
public import RequestProject.DiskWeakModes
public import RequestProject.NeumannNormalizedBoundary

/-!
# Harmonic-mode identities for the genuine Neumann weak equation

The test vectors are obtained from a smooth local inverse. Both their
gradient pairing and their mass pairing come from the actual physical H¹
space. The boundary load is the constructed conformal half trace.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

theorem h1Value_diskHolomorphicH1Test (m : ℕ) :
    h1Value (ball (0 : ℂ) 1) (diskHolomorphicH1Test m) = diskHolomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskHolomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)⟩

theorem h1Value_diskAntiholomorphicH1Test (m : ℕ) :
    h1Value (ball (0 : ℂ) 1) (diskAntiholomorphicH1Test m) = diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

section

variable {R : ℝ} (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

end

end PolyaNeumann

end
