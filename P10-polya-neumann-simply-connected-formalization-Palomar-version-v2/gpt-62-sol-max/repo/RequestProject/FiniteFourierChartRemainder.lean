module

public import RequestProject.FourierFiniteRankRegularity

/-!
# The regular principal correction of a finite Fourier chart

The output vectors of the finite-rank chart correction have finite Fourier
support, so the correction is regular at every Sobolev order.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

local notation "H₁" => nonpositiveFourierSubspaceᗮ

section

variable {d : ℕ} (u : Fin d → H₁) (v : Fin d → L2Z)
include d u v

def finiteFourierChart  :
    H₁ →L[ℂ] L2Z :=
  Submodule.subtypeL H₁ + ∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)

theorem finiteFourierChart_correction_sobolev 
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (s : ℝ) (z : H₁) :
    IsSobolevSeq s ((finiteFourierChart u v z - (z : L2Z) : L2Z) : ℤ → ℂ) := by
  have heq : finiteFourierChart u v z - (z : L2Z) =
      (∑ r, InnerProductSpace.rankOne ℂ (v r) (u r)) z := by
    simp  [finiteFourierChart, ContinuousLinearMap.add_apply,
      Submodule.subtypeL_apply, add_sub_cancel_left]
  rw [heq]
  change _ ∈ fourierSobolevSubmodule s
  rw [ContinuousLinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  rw [InnerProductSpace.rankOne_apply]
  exact (fourierSobolevSubmodule s).smul_mem _
    (isSobolevSeq_of_finite_fourier_support s (hv r))

end

end PolyaNeumann

end
