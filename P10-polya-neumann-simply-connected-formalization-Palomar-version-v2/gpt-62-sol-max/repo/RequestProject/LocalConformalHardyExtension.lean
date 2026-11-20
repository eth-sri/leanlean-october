module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.DiskHardyExtension
public import RequestProject.LocalConformalH1Equiv
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalGradientComponents

/-!
# The genuine supplied-coordinate Hardy extension in the physical domain

The disk harmonic extension is transported by the proved inverse of the actual
H¹ pullback. Every input produces a physical H¹ vector. Its normalized circle
trace is exactly the nonpositive Fourier projection, with the zero mode included.
The series converges in the physical H¹ norm, and the inverse-coordinate estimate
gives its norm bound. The initial conformal map is supplied explicitly.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

/-- The actual disk extension followed by the actual physical H¹ pushforward. -/
def localConformalHardyH1Extension :
    L2Z →L[ℂ] NeumannH1 (F '' ball (0 : ℂ) 1) :=
  (localConformalH1Pushforward coords).comp
    diskHardyExtension

@[simp] theorem localConformalH1Pullback_hardyExtension (b : L2Z) :
    coords.pullback
      (localConformalHardyH1Extension coords b) =
        diskHardyExtension b := by
  exact localConformalH1Pullback_pushforward coords
    (diskHardyExtension b)

theorem localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive (b : L2Z)
    (hneg : ∀ n : ℤ, 0 < n → b n = 0) :
    coords.halfTrace
      (localConformalHardyH1Extension coords b) = b := by
  change diskHalfTrace (coords.pullback
    (localConformalHardyH1Extension coords b)) = _
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hneg

/-- The transported vector satisfies the actual physical weak CR equation. -/
theorem localConformalHardyH1Extension_cauchyRiemann (b : L2Z) :
    h1Gradient (F '' ball (0 : ℂ) 1) 0
        (localConformalHardyH1Extension coords b) =
      Complex.I • h1Gradient (F '' ball (0 : ℂ) 1) 1
        (localConformalHardyH1Extension coords b) := by
  apply (localConformalH1Pullback_antiholomorphic_iff coords
    (localConformalHardyH1Extension coords b)).mp
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_cauchyRiemann b

end PolyaNeumann

end
