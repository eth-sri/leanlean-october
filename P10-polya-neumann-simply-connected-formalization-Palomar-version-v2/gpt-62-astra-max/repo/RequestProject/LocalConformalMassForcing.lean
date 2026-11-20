module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalMass
public import RequestProject.LpBoundedMultiplierReal
public import RequestProject.DiskMassForcing
public import RequestProject.PlanarNotation

/-!
# The physical mass forcing in conformal coordinates

Multiplication by the Jacobian density is built on the actual L² pullback.
The mass pairing identifies it with the original weak equation. Its disk
moments gain one full Fourier derivative by the proved area Bessel estimate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate InnerProductSpace

section

section

variable (Φ : SmoothDiskMap) (hL : IsLipschitzDomain Φ.domain)

include hL in
def SmoothDiskMap.massForcing {K : ℝ} (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) :
    NeumannH1 Φ.domain →L[ℂ] L2 unitDisk :=
  (lpBoundedMultiplier (localConformalMassDensity Φ.map)
    (localConformalMassDensity_aemeasurable Φ)
    (localConformalMassDensity_ae_bound Φ.map hK)).comp
      (Φ.massPullback hL hK)

theorem localConformal_mass_pairing (Φ : ControlledDiskMap)
    (v u : NeumannH1 Φ.domain) :
    ⟪h1Value Φ.domain v, h1Value Φ.domain u⟫_ℂ =
      ⟪h1Value unitDisk (Φ.h1Pullback Φ.lipschitzDomain v),
        Φ.massForcing Φ.lipschitzDomain Φ.deriv_upper u⟫_ℂ := by
  rw [← localConformalMassPullback_inner Φ v u]
  
  exact inner_lpBoundedMultiplier_real (localConformalMassDensity Φ.map)
    (localConformalMassDensity_aemeasurable Φ)
    (localConformalMassDensity_ae_bound Φ.map Φ.deriv_upper)
    (Eventually.of_forall fun z => Complex.conj_ofReal _) _ _

include hL in
def SmoothDiskMap.massFourierH1 {K : ℝ} (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) :
    NeumannH1 Φ.domain →L[ℂ] L2Z :=
  diskMassForcingH1.comp (Φ.massForcing hL hK)

@[simp] theorem localConformalMassFourierH1_apply {K : ℝ} (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K)
    (u : NeumannH1 Φ.domain) (n : ℤ) :
    Φ.massFourierH1 hL hK u n =
      (sobWeight n : ℂ) *
        diskMassForcingCoeff (Φ.massForcing hL hK u) n := rfl

end

end

end PolyaNeumann

end
