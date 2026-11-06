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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate InnerProductSpace

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) {C K : ℝ}
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)

def localConformalMassForcing :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  (lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)).comp
      (localConformalMassPullback hR F hFs hL hK)

include hb hhol hinj hC in
theorem localConformal_mass_pairing
    (v u : NeumannH1 (F '' ball 0 1)) :
    ⟪h1Value (F '' ball 0 1) v, h1Value (F '' ball 0 1) u⟫_ℂ =
      ⟪h1Value (ball 0 1) (localConformalH1Pullback hR F hFs hL v),
        localConformalMassForcing hR F hFs hL hK u⟫_ℂ := by
  rw [← localConformalMassPullback_inner hR F hFs hb hL hhol hinj hC hK v u]
  exact inner_lpBoundedMultiplier_real (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
    (Eventually.of_forall fun z => Complex.conj_ofReal _) _ _

def localConformalMassFourierH1 :
    NeumannH1 (F '' ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskMassForcingH1.comp (localConformalMassForcing hR F hFs hL hK)

@[simp] theorem localConformalMassFourierH1_apply
    (u : NeumannH1 (F '' ball 0 1)) (n : ℤ) :
    localConformalMassFourierH1 hR F hFs hL hK u n =
      sobWeight n *
        diskMassForcingCoeff (localConformalMassForcing hR F hFs hL hK u) n := rfl

end

end PolyaNeumann

end
