module

public import RequestProject.PlanarTypes

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

local notation "H₁" => nonpositiveFourierSubspaceᗮ

def finiteFourierChart {d : ℕ} (u : Fin d → H₁) (v : Fin d → L2Z) :
    H₁ →L[ℂ] L2Z :=
  Submodule.subtypeL H₁ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)

theorem finiteFourierChart_correction_sobolev 
    u (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : FourierSeq)).Finite)
    s z :
    IsSobolevSeq s ((finiteFourierChart u v z - (z : L2Z) : L2Z) : FourierSeq) := by
  have heq : finiteFourierChart u v z - (z : L2Z) =
      (∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z := by
    simp_all [finiteFourierChart, PolyaNeumann.L2Z]
  rw [heq]
  change _ ∈ fourierSobolevSubmodule s
  rw [ContinuousLinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  exact (fourierSobolevSubmodule s).smul_mem _
    (isSobolevSeq_of_finite_fourier_support s (hv r))

end PolyaNeumann

end
