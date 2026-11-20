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

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)

local notation "D" => ball (0 : ℂ) 1
local notation "Ω" => F '' D

def localConformalMassForcing :
    NeumannH1 Ω →L[ℂ] L2 D :=
  (localConformalMassMultiplier coords).comp
    (localConformalMassPullback coords)

theorem localConformal_mass_pairing
    (v u : NeumannH1 Ω) :
    ⟪h1Value Ω v, h1Value Ω u⟫_ℂ =
      ⟪h1Value D (coords.pullback v),
        localConformalMassForcing coords u⟫_ℂ := by
  rw [← localConformalMassPullback_inner coords v u]
  exact inner_lpBoundedMultiplier_real _ (localConformalMassDensity_aemeasurable F)
    (localConformalMassDensity_ae_bound coords)
    (Eventually.of_forall fun z => Complex.conj_ofReal _) _ _

def localConformalMassFourierH1 :
    NeumannH1 Ω →L[ℂ] L2Z :=
  diskMassForcingH1.comp (localConformalMassForcing coords)

end

end PolyaNeumann

end
