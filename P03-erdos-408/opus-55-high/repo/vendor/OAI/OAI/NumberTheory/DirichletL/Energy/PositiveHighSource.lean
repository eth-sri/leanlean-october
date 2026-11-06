module

public import OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
public import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLivePower
public import OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
public import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyPositiveHighSource
open HeckeFamily
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState
open CenteredMomentCommonRadialData
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal HeckeFamily.O)[NeZero M]
local instance : Finite (HeckeFamily.O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (HeckeFamily.O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (by grind)
  have hx (X:ℝ):X≤Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (by positivity)]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (by grind) (by grind) hX₂.le (by positivity)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

end SevenEighths.CenteredMomentEnergyPositiveHighSource

end

end OAI
