module

public import OAI.NumberTheory.DirichletL.Energy.CanonicalLiveCapacity
public import OAI.NumberTheory.DirichletL.Energy.AllocatedPaid
public import OAI.NumberTheory.DirichletL.Energy.AllocatedZero
public import OAI.NumberTheory.DirichletL.Energy.AllocatedClipped
public import OAI.NumberTheory.DirichletL.Energy.ChildState

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalPaidSource
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentAllocatedNaturalSource
open CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary QuadraticInitialBound
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock HeckeFamily
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyCanonicalLiveBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_canonical_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    WithChildBands (α := α) M H hH W bslot a b L Lslot lo hi Mcap εchild κ Z η₀ Q degree S fun C₀ C₁ =>
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    WithSlotBounds Lslot lo hi w σ freq height mesh <|
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨dc,Cb,hCb,hbound⟩ := actual_allocated_paid_bands (α:=α) M H hH W aslot bslot Mcap 2 Lslot
    εremove lo hi κ ha hWs hW hMcap (by norm_num) hLs hε hbeta hκ
  obtain ⟨n,T,Cp,hCp,hprofile⟩ := retained_pair_control a b haPlain S
  refine ⟨n,T,dc,Cb*Cp^2,mul_pos hCb (sq_pos_of_pos hCp),?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hz:=hZ₀.trans_le hZ
  have hz0:=zero_lt_one.trans hz
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  by_cases hne:LiveChild τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · let st := canonicalState Z 0 hz τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
    have he := hbound Z hZ (a/max 1 b) b 0 L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J st rfl rfl hwidth (pair D alloc haPlain p v X₁ X₂ hX₁ hX₂)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
      (scale_cap D alloc Z L X₁ hz.le hL hX₁ hc₁ 0 F₁ hF₁)
      (scale_cap D alloc Z L X₂ hz.le hL hX₂ hc₂ 1 F₂ hF₂)
    dsimp only at he
    have he' := (allocated_pair st rfl D alloc haPlain p d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J).le.trans he
    let U:Fin 2→ℝ:=![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
    have hU:∀i,0<U i:=by
      intro i;fin_cases i
      · exact rawScale_pos D alloc X₁ hX₁ 0
      · exact rawScale_pos D alloc X₂ hX₂ 1
    have hp:(pair D alloc haPlain p v X₁ X₂ hX₁ hX₂).control S≤
        Cp*p.control T*(1+|v|+height)^(2*n):=by
      have h:=hprofile p U hU v
      exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith) _) (mul_nonneg hCp.le (p.control_nonneg T)))
    have hcost := live_source_paid_cost src C R B D alloc J τ (canonicalRadial τ (internalQ Q η₀) dyad)
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      v Z X₁ X₂ κ A Mparent Mnom
      (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))
      u ell δ₁ δ₂ θclip w hX₁ hX₂ F₁ F₂ (hZ₀.trans_le hZ)
      (by linarith) hw hmatch.scale hF₁ hF₂ hparent hshift hdefect hu hell hδ₁ hδ₂ hθclip hclip hne
    have hd := diagonalControl_nonneg st.radial.profile
    have hpt := p.control_nonneg T
    apply he'.trans
    refine mul_le_mul ?_ (Real.rpow_le_rpow_of_exponent_le hz.le ?_) (Real.rpow_nonneg hz0.le _) (by positivity)
    · calc
        _ ≤ Cb*(C₀+C₁)*diagonalControl st.radial.profile*
            (Cp*p.control T*(1+|v|+height)^(2*n))^2*(1+(|v|+height))^(dc+degree) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2) (by positivity)
        _ = _ := by change _ = (Cb*Cp^2)*(C₀+C₁)*diagonalControl st.radial.profile*
              (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)
                    ring
    · simp only [st,canonicalState,NaturalState.width]
      linarith only [hcost]
  · have he:=energy_zero_of_not_live τ rad (fun z hz=>hz.1) D alloc V₁ V₂
      d.slots d.coefficient d.P d.P_pos v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hne
    change allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J≤_
    rw [he]
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hp:=p.control_nonneg T
    positivity

end SevenEighths.CenteredMomentEnergyCanonicalPaidSource

end

end OAI
