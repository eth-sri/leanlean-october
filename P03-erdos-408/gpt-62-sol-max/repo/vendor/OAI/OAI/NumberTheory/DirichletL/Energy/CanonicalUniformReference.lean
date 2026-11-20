module

public import OAI.FiniteMajorant

public import OAI.NumberTheory.DirichletL.Energy.CanonicalPaidSource
public import OAI.NumberTheory.DirichletL.Energy.AllocatedBound
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon
public import OAI.NumberTheory.DirichletL.Energy.BandSubtypeTransport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalUniformReference
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource
open CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

/-- Uniform reference estimates over a finite family of embedded slot types. -/
theorem uniform_reference_paid {ι : Type*} [Fintype ι] (slot : ι → Type*)
    [∀ i, Fintype (slot i)] [∀ i, DecidableEq (slot i)] (embed : ∀ i, slot i ↪ α) (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀i:ι,∀θ:slot i→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    WithChildBands (α := α) M H hH W bslot a b L Lslot lo hi Mcap εchild κ Z η₀ Q degree S fun C₀ C₁ =>
    ∀(w σ freq:slot i→ℝ)(v height mesh:ℝ),
    WithSlotBounds Lslot lo hi w σ freq height mesh <|
    ∀src:Input (slot i),Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0<reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  have hex (i:ι):=actual_canonical_paid_source (α:=slot i) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  choose n T dc Cp hCp hbound using hex
  have hexM (i : ι) := actual_common_from_energy (α:=slot i) (fun _=>bslot) (fun _=>Mslot)
    (fun _=>hMslot) εmask hεmask
  choose Cm hCm hcommon using hexM
  let Cc (i : ι) := 2*Cm i*Cp i
  let n₀:=∑J:ι,n J
  let dc₀:=∑J:ι,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  obtain ⟨Ctot, hCt, hcTotal⟩ := exists_real_majorant 0 Cc
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=Σi:ι,slot i→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  obtain ⟨Z₀, hZ₀, hZchoice_le⟩ := exists_real_majorant 1 Zchoice
  refine ⟨Z₀,hZ₀,?_⟩
  intro i θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi := (hZchoice_le ⟨i, θ⟩).trans hZ
  have hc := hcTotal i
  have hp:=positiveAt_embedding M H hH (embed i) W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hz:=hZ₀.trans_le hZ
  have hz0:=zero_lt_one.trans hz
  have hrOne:1≤ratioPenalty dyad:=le_max_left _ _
  have hr0:=zero_lt_one.trans_le hrOne
  have hlog:=Real.logb_nonneg hz hrOne
  let Mnom := Real.logb Z reference
  let δ := δ₁+Real.logb Z (ratioPenalty dyad)
  have hδ : 0 ≤ δ := add_nonneg hδ₁ hlog
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  let E:=Cp i*(C₀+C₁)*diagonalControl rad.profile*(p.control (T i))^2*
    (1+(|v|+height))^(dc i+degree+4*n i)*
    Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ/6+θclip/3)+κ*mesh)
  have he:0≤E:=by
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    dsimp [E]
    have := hCp i
    positivity
  have hleft:∀X₁ X₂:ℝ,∀h₁:0<X₁,∀h₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
      X₁*X₂=d.X₁*d.X₂ → ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
      ∀J,allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
        v X₁ X₂ h₁ h₂ F₁ F₂ J≤E:=by
    intro X₁ X₂ h₁ h₂ hc₁ hc₂ hprod F₁ F₂ hF₁ hF₂ J
    apply hb ⟨i,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ h₁ h₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
      A Mparent Mnom u ell δ δ₂ θclip hu hell hδ hδ₂ hθclip hparent _ hdefect hclip
    rw [hprod]
    dsimp only [δ, Mnom, d]
    linarith only [hshift]
  have hh:=hcommon i src hhi hMs τ v C R hR B D alloc V₁ V₂ hp₁ hp₂ rad
    (fun z hz=>hz.1) E E he he (by
      intro left F₁ hF₁ F₂ hF₂ J hJ
      have hf₁:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₁) hi)).ne_zero
      have hf₂:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₂) hi)).ne_zero
      cases left
      · exact hleft d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos hY₁ hY₂ d.same_product F₁ F₂ hf₁ hf₂ J
      · exact hleft d.X₁ d.X₂ d.X₁_pos d.X₂_pos hX₁ hX₂ rfl F₁ F₂ hf₁ hf₂ J)
  have hscale:Z^(Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh)=
      reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh):=by
    rw [show Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh=
      Real.logb Z reference+Real.logb Z (ratioPenalty dyad)*((1:ℝ)/6)+
        (εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) by ring]
    rw [Real.rpow_add hz0,Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' href,
      Real.rpow_mul hz0.le,Real.rpow_logb hz0 hz.ne' hr0]

  have ht:T i⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T i)≤p.control T₀:= p.control_mono ht
  have hn₀:n i≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have hdc₀:dc i≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have hdeg:dc i+degree+4*n i≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc i+degree+4*n i)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T i)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hr:0<ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  calc
    _ ≤ _ := hh
    _ = Cc i*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl rad.profile*
        (p.control (T i))^2*(1+(|v|+height))^(dc i+degree+4*n i)*reference*
          (ratioPenalty dyad)^((1:ℝ)/6)*Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
      dsimp only [E,Cc,δ,Mnom]
      rw [hscale]
      ring
    _ ≤ _ := by
      dsimp only [rad]
      gcongr

end SevenEighths.CenteredMomentEnergyCanonicalUniformReference

end

end OAI
