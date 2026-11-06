module
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
public import OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission
public import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=>le_rfl)
  simp_all

theorem four_upper_scales (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    (balancedSource).X₁≤Z^L ∧ (balancedSource).X₂≤Z^L ∧
    (balancedSource).Y₁≤Z^L ∧ (balancedSource).Y₂≤Z^L := by
  have hp:0<Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
  have hxy:X₁*X₂≤volume balancedSource:=by
    change X₁*X₂≤X₁*X₂*(∏i,Z^(w i))
    simp_all
  have hY:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI
