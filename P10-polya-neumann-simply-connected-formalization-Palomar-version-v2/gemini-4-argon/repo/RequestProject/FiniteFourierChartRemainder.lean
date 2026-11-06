module

public import RequestProject.FourierFiniteRankRegularity

/-!
# The regular principal correction of a finite Fourier chart

The input and output vectors of the actual chart correction have finite
Fourier support. Expanding its adjoint proves that the correction to the
compressed positive principal part is regular at every Sobolev order.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

local notation "H₁" => nonpositiveFourierSubspaceᗮ

def finiteFourierChart  (u : Fin d → H₁) (v : Fin d → L2Z) :
    H₁ →L[ℂ] L2Z :=
  Submodule.subtypeL H₁ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)

theorem finiteFourierChart_correction_sobolev {d : ℕ}
    (u : Fin d → H₁) v
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (s : ℝ) z :
    IsSobolevSeq s ((finiteFourierChart u v z - (z : L2Z) : L2Z) : ℤ → ℂ) := by
  rw [show finiteFourierChart u v z - z = (∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z by
    simp [finiteFourierChart, Submodule.subtypeL_apply]]
  change _ ∈ fourierSobolevSubmodule s
  rw [ContinuousLinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  rw [InnerProductSpace.rankOne_apply]
  exact (fourierSobolevSubmodule s).smul_mem _
    (isSobolevSeq_of_finite_fourier_support s (hv r))

end PolyaNeumann

end
