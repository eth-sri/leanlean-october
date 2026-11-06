module
public import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

lemma paired_sqrt (A E₁ E₂ c d:ℝ) (hA:0≤A) (hE₁:0≤E₁) (hE₂:0≤E₂)
    (hc:0<c) (_hd:0<d) :
    Real.sqrt (A*E₁/c)*Real.sqrt (A*E₂/d)=A/Real.sqrt (c*d)*Real.sqrt (E₁*E₂) := by
  rw [←Real.sqrt_mul (div_nonneg (mul_nonneg hA hE₁) hc.le)]
  rw [show A*E₁/c*(A*E₂/d)=A^2*(E₁*E₂)/(c*d) by ring]
  rw [Real.sqrt_div (mul_nonneg (sq_nonneg A) (mul_nonneg hE₁ hE₂)),
    Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq hA]
  ring

omit [DecidableEq ι] in
theorem paired_core_budget (s:Input ι) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (Ce Z δ E₁ E₂ t:ℝ) (hCe:0≤Ce) (hZ:0≤Z) (hE₁:0≤E₁) (hE₂:0≤E₂)
    (J₁ J₂:ℕ) :
    windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)=
      (Ce*Z^δ*profileCost s*volume s.toData)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hA:0≤Ce*Z^δ*profileCost s*volume s.toData:=by
    exact mul_nonneg (mul_nonneg (mul_nonneg hCe (Real.rpow_nonneg hZ _)) (profileCost_nonneg s)) (volume_pos s.toData).le
  have he (G:Ideal O) (E:ℝ):core s G Ce Z δ E=
      (Ce*Z^δ*profileCost s*volume s.toData)*E/(G.absNorm:ℝ):=by
    unfold core volume
    ring
  rw [he C E₁,he D E₂]
  simp only [windowBudget,pow_add]
  have hh:=paired_sqrt _ E₁ E₂ _ _ hA hE₁ hE₂ hc hd
  calc
    _=(Real.sqrt (_*E₁/(C.absNorm:ℝ))*Real.sqrt (_*E₂/(D.absNorm:ℝ)))*
      (heightEnvelope t^J₁*heightEnvelope t^J₂)*profileMoment J₁*profileMoment J₂:=by ring
    _=_:=by rw [hh]

end SevenEighths.CenteredMomentSecondNonexceptionalPhysical

end

end OAI
