module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalMass
public import RequestProject.LpBoundedMultiplierReal
public import RequestProject.DiskMassForcing

/-!
# The physical mass forcing in conformal coordinates

Multiplication by the Jacobian density is built on the actual L² pullback.
The mass pairing identifies it with the original weak equation. Its disk
moments gain one full Fourier derivative by the proved area Bessel estimate.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

section

variable {R } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) {C K }
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)

def localConformalMassForcing :
    NeumannH1 (F '' unitDisk) →L[ℂ] L2 unitDisk :=
  (lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)).comp
      (localConformalMassPullback hR F hFs hL hK)

include hb hhol hinj hC in
theorem localConformal_mass_pairing
    v u :
    ⟪h1Value (F '' unitDisk) v, h1Value (F '' unitDisk) u⟫_ℂ =
      ⟪h1Value unitDisk (localConformalH1Pullback hR F hFs hL v),
        localConformalMassForcing hR F hFs hL hK u⟫_ℂ := by
  rw [← localConformalMassPullback_inner hR F hFs hb hL hhol hinj hC hK v u]
  exact inner_lpBoundedMultiplier_real (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
    (Eventually.of_forall fun z => Complex.conj_ofReal _) _ _

def localConformalMassFourierH1 :
    NeumannH1 (F '' unitDisk) →L[ℂ] L2Z :=
  diskMassForcingH1.comp (localConformalMassForcing hR F hFs hL hK)

end

end PolyaNeumann

end
