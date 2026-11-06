module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

variable {R C K : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)

/-- The actual disk extension followed by the actual physical H¹ pushforward. -/
def localConformalHardyH1Extension :
    L2Z →L[ℂ] NeumannH1 (F '' unitDisk) :=
  (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes).comp
    diskHardyExtension
local notation "hardyH1ExtensionFixed" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes


@[simp] theorem localConformalH1Pullback_hardyExtension b :
    localConformalH1Pullback hR F hFs hL
      (hardyH1ExtensionFixed b) =
        diskHardyExtension b := localConformalH1Pullback_pushforward hR F hFs hb hL hhol hinj hC hK e he hsource hes
    (diskHardyExtension b)

theorem localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive b
    (hneg : ∀ n : ℤ, 0 < n → b n = 0) :
    localConformalDiskHalfTrace hR F hFs hL
      (hardyH1ExtensionFixed b) = b := by
  change diskHalfTrace (localConformalH1Pullback hR F hFs hL
    (hardyH1ExtensionFixed b)) = _
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hneg

/-- The transported vector satisfies the actual physical weak CR equation. -/
theorem localConformalHardyH1Extension_cauchyRiemann b :
    h1Gradient (F '' unitDisk) 0
        (hardyH1ExtensionFixed b) =
      Complex.I • h1Gradient (F '' unitDisk) 1
        (hardyH1ExtensionFixed b) := by
  apply (localConformalH1Pullback_antiholomorphic_iff hR F hFs hb hL hhol hinj hC
    (hardyH1ExtensionFixed b)).mp
  rw [localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_cauchyRiemann b

end PolyaNeumann

end
