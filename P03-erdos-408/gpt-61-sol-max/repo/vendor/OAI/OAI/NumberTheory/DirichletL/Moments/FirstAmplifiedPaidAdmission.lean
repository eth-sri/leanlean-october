module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedActiveAffine
public import OAI.NumberTheory.DirichletL.Moments.SecondCapacitySourceShift
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius

variable {ι:Type*}[Fintype ι]


open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentFirstAmplifiedActiveAffine CenteredMomentFirstAmplifiedActiveCapacitySource
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

def sourceReserve {α}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal HeckeFamily.O)(Z delta reserve cost a:ℝ) :=
  max (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
    min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
    Real.logb Z fixedPresentationCost-Real.logb Z cost+
    Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
    (Fintype.card α:ℝ)*Real.logb Z (max 1 childInput.upper)) 0

section
variable (s : Input ι) (τ υ : Character) (C D R0 : Ideal HeckeFamily.O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D)) (R : Ideal HeckeFamily.O) (B : actualAllocations s.pools C) (t : ℝ) (hB : frozenCoefficient B.val C R0 s.ν s.W s.P≠0) (K Z κ A M sigma delta reserve cost a : ℝ) (hK : 0<K) (hZ : 1<Z) (hcost : 0<cost) (ha : 0<a)


lemma sourceReserve_nonneg {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
     C D  Z delta reserve cost a :0≤sourceReserve s childInput C D Z delta reserve cost a :=
  le_max_right _ _

include hZ in
lemma common_affine    
      (hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hp:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M):
    A+(6*κ-1)*(∑i:liveIndices B.val,Real.logb Z (s.P i.val))≤M := by
  have hs:=common_slot_logs_le s C B Z hZ hP
  have hm:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

include hC hD hCD hB hK hZ hcost ha in
theorem actual_main_admission    
       
       
     
         
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:HeckeFamily.O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal HeckeFamily.O))(β:Ideal HeckeFamily.O→ℂ) C₂ D₂ 
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
     U (R:ℝ)(rows:Finset HeckeFamily.O)(W:𝓢(ℝ,ℂ)) n 
    (hlower:∀I:Ideal HeckeFamily.O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0)
     Cpick Rpick (hside:Cpick=C₂ ∨ Cpick=D₂)
     B₂ 
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (child s C R0 B τ t).ν (child s C R0 B τ t).W (child s C R0 B τ t).P≠0)
     κ Mdecl (hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=child s C R0 B τ t;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*(sigma/3)+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ):=mul_pos hcost hq
  have hf:=inherited_affine_parent s C R0 B Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(child s C R0 B τ t).P i:=fun i=>hP i.val
  have hparent:=common_affine (child s C R0 B τ t) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (child s C R0 B τ t) υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ))-
      Real.logb Z (volume (child s C R0 B τ t))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
  rw [common_volume,Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

include hC hD hCD hB hK hZ hcost ha in
theorem actual_active_error_admission    
       
       
     
         
     p (hp:p≠0) k (hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
     Bp  v 
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:HeckeFamily.O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal HeckeFamily.O))(β:Ideal HeckeFamily.O→ℂ) C₂ D₂ 
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
     U (R:ℝ)(rows:Finset HeckeFamily.O)(W:𝓢(ℝ,ℂ)) n 
    (hlower:∀I:Ideal HeckeFamily.O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0)
     Cpick Rpick (hside:Cpick=C₂ ∨ Cpick=D₂)
     B₂ 
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).ν (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).W (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P≠0)
     κ Mdecl (hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*errorRemoval p Z k+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k):=by positivity
  have hf:=active_error_parent_affine s C R0 B τ t (Ideal.span {p}) k Bp υ v Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P i:=fun i=>hP i.val.val
  have hparent:=common_affine (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
  have hQ:(Ideal.span {p})≠(0:Ideal HeckeFamily.O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

lemma common_preVolume_height    
     τ υ  v t :
    preVolume (commonData (withHeight s τ v) C R B)=
      preVolume (commonData (withHeight s υ t) C R B) := rfl

end

end SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

end

end OAI
