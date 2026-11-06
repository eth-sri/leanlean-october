module

public import RequestProject.DiskHardyExtension
public import RequestProject.LocalConformalH1Equiv
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalCauchyRiemann

/-!
# The genuine supplied-coordinate Hardy extension in the physical domain

The disk harmonic extension is transported by the proved inverse of the actual
H¹ pullback. Every input produces a physical H¹ vector. Its normalized circle
trace is exactly the nonpositive Fourier projection, with the zero mode included.
The series converges in the physical H¹ norm, and the inverse-coordinate estimate
gives its norm bound. The initial conformal map is supplied explicitly.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

/-- The actual disk extension followed by the actual physical H¹ pushforward. -/
def localConformalHardyH1Extension :
    L2Z →L[ℂ] NeumannH1 (F '' ball 0 1) :=
  (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes).comp
    diskHardyExtension

local notation "Φ1" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes

@[simp] theorem localConformalH1Pullback_hardyExtension b :
    localConformalH1Pullback hR F hFs hL
      (Φ1 b) =
        diskHardyExtension b := by
  exact localConformalH1Pullback_pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes
    (diskHardyExtension b)

local notation "Φ0" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive b
    (hneg : ∀ n : ℤ, 0 < n → b n = 0) :
    localConformalDiskHalfTrace hR F hFs hL
      (Φ1 b) = b := by
  change diskHalfTrace (localConformalH1Pullback hR F hFs hL
    (Φ0 b)) = _
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hneg

/-- The transported vector satisfies the actual physical weak CR equation. -/
theorem localConformalHardyH1Extension_cauchyRiemann b :
    h1Gradient (F '' ball 0 1) 0
        (Φ0 b) =
      Complex.I • h1Gradient (F '' ball 0 1) 1
        (Φ1 b) := by
  apply (localConformalH1Pullback_antiholomorphic_iff hR F hFs hb hL hhol hinj hC
    (Φ0 b)).mp
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_cauchyRiemann b

end PolyaNeumann

end
