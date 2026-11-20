module

public import OAI.NumberTheory.DirichletL.Energy.AllocatedPaid
public import OAI.NumberTheory.DirichletL.Energy.AllocatedZero

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentAllocatedNaturalSource
open CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def pair (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    {a b:ℝ}(ha:0<a)(p:Profiles a b)(v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    Profiles (a/max 1 b) b :=
  retainedPair a b ha p ![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
    (by intro i;fin_cases i;exact rawScale_pos D alloc X₁ hX₁ 0;exact rawScale_pos D alloc X₂ hX₂ 1) v

def scale (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O)):ℝ:=
  clippedScale (rawScale D alloc X j)/((∏I∈F,I).absNorm:ℝ)

lemma scale_pos (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):0<scale D alloc X j F:=by
  refine div_pos (by unfold clippedScale;positivity) ?_
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hF))

lemma scale_cap (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (Z L X:ℝ)(hZ:1≤Z)(hL:0≤L)(hX:0<X)(hc:X≤Z^L)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):scale D alloc X j F≤Z^L:=
  (allocatedScale_le D alloc X hX j F hF).trans (max_le (Real.one_le_rpow hZ hL) hc)

lemma allocated_pair {Z Bmask bΦ a b:ℝ}(st:NaturalState Z Bmask bΦ)(hunit:st.puncture=1)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (ha:0<a)(p:Profiles a b)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1)) pool β P v X₁ X₂ hX₁ hX₂ F₁ F₂ J =
    energy st.character st.mask 1 0
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 0)
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 1)
      (fun i:↥(liveIndices D alloc\J)=>pool i)
      (fun i:↥(liveIndices D alloc\J)=>CenteredMomentCommonMaskEnergy.heightCoefficient (β i) v)
      (fun i:↥(liveIndices D alloc\J)=>P i)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      st.radial.keep st.radial.profile st.radial.scale:=by
  simp only [allocatedEnergy,pair,retainedPair,scale,NaturalState.mask,hunit,
    Matrix.cons_val_zero,Matrix.cons_val_one]


end SevenEighths.CenteredMomentEnergyAllocatedClipped

end

end OAI
