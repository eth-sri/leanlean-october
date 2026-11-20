module

public import RequestProject.DiskCoordinates

public import RequestProject.DiskHardyExtension
public import RequestProject.LocalConformalH1Equiv
public import RequestProject.LocalConformalTrace
public import RequestProject.LocalConformalCauchyRiemann
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric

section

variable (Φ : DiskCoordinates) (b : L2Z)

/-- The actual disk extension followed by the actual physical H¹ pushforward. -/
def DiskCoordinates.hardyH1Extension :
    L2Z →L[ℂ] NeumannH1 Φ.domain :=
  Φ.h1Pushforward.comp
    diskHardyExtension

@[simp] theorem localConformalH1Pullback_hardyExtension :
    Φ.h1Pullback Φ.lipschitzDomain
      (Φ.hardyH1Extension b) =
        diskHardyExtension b := by
  exact localConformalH1Pullback_pushforward Φ (diskHardyExtension b)

theorem localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive
    (hneg : ∀ n : ℤ, 0 < n → b n = 0) :
    Φ.pulledBackHalfTrace Φ.lipschitzDomain
      (Φ.hardyH1Extension b) = b := by
  change diskHalfTrace (Φ.h1Pullback Φ.lipschitzDomain
    (Φ.hardyH1Extension b)) = _
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hneg

/-- The transported vector satisfies the actual physical weak CR equation. -/
theorem localConformalHardyH1Extension_cauchyRiemann :
    h1Gradient Φ.domain 0
        (Φ.hardyH1Extension b) =
      Complex.I • h1Gradient Φ.domain 1
        (Φ.hardyH1Extension b) := by
  apply (localConformalH1Pullback_antiholomorphic_iff Φ (Φ.hardyH1Extension b)).mp
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_cauchyRiemann b

end

end PolyaNeumann

end
