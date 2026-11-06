module

public import OAI.NumberTheory.DirichletL.Energy.ZeroReferenceLive
public import OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
public import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry

@[expose] public section

namespace OAI

noncomputable section

open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyZeroReferenceLive CenteredMomentEnergyOriginalSource CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry CenteredMomentCommonRadialData CenteredMomentSourceRow CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O

def balancedInput {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):Input (Fin 0):=
  naturalInput s p ha (fun _=>∅) (by simp) (fun _=>s.character) (fun _=>0)
    (fun _=>1) (fun _=>1) (by simp) (by simp) 1 1 (by norm_num)
    (by simp) (by simp) t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂ (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

lemma balanced_volume {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    CenteredMomentAmplificationChildInput.volume (balancedInput s p ha t X₁ X₂ hX₁ hX₂)=X₁*X₂:=by
  simp only [CenteredMomentAmplificationChildInput.volume,
    balancedInput,naturalInput,completeInput,naturalData,Finset.univ_eq_empty,Finset.prod_empty,mul_one]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysical

end

end OAI
