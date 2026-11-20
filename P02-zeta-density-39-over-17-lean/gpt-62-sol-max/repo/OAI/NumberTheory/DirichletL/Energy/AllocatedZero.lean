module
public import OAI.NumberTheory.DirichletL.Energy.AllocatedBound
public import OAI.NumberTheory.DirichletL.Energy.AllocatedProfiles
public import OAI.NumberTheory.DirichletL.Energy.Bands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedZero
open HeckeFamily CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedNaturalSource CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma allocatedScale_le (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(X:ℝ)(hX:0<X)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):
    clippedScale (rawScale D a X j)/(Ideal.absNorm (∏I∈F,I):ℝ)≤max 1 X:=by
  have hn:1≤(Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a j):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hf:1≤(Ideal.absNorm (∏I∈F,I):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr hF))
  have hx:rawScale D a X j≤X:=div_le_self hX.le hn
  exact (div_le_self (by unfold clippedScale;positivity) hf).trans
    (max_le_max_left 1 hx)

end SevenEighths.CenteredMomentEnergyAllocatedZero

end

end OAI
