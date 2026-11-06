module

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate InnerProductSpace ContDiff

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)

local notation "Φ0" => ball 0 1

def localConformalMassForcing :
    NeumannH1 (F '' Φ0) →L[ℂ] L2 (Φ0) :=
  (lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)).comp
      (localConformalMassPullback hR F hFs hL hK)


local notation "Φ1" => localConformalMassForcing hR F hFs hL hK
include hb hhol hinj hC in
theorem localConformal_mass_pairing
    v u :
    ⟪h1Value (F '' Φ0) v, h1Value (F '' Φ0) u⟫_ℂ =
      ⟪h1Value (Φ0) (localConformalH1Pullback hR F hFs hL v),
        Φ1 u⟫_ℂ := by
  rw [← localConformalMassPullback_inner hR F hFs hb hL hhol hinj hC hK v u]
  exact inner_lpBoundedMultiplier_real (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
    (Eventually.of_forall fun z => Complex.conj_ofReal _) _ _

def localConformalMassFourierH1 :
    NeumannH1 (F '' Φ0) →L[ℂ] L2Z :=
  diskMassForcingH1.comp (Φ1)

@[simp] theorem localConformalMassFourierH1_apply
    u n :
    localConformalMassFourierH1 hR F hFs hL hK u n =
      (sobWeight n : ℂ) *
        diskMassForcingCoeff (Φ1 u) n := rfl

end

end PolyaNeumann

end
