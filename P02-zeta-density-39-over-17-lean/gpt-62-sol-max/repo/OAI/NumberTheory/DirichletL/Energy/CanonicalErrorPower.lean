module
public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianFrame
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorAdmitted
public import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
public import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorGaussian
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorUniform
public import OAI.NumberTheory.DirichletL.Moments.FrozenFamilyDescent
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
public import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPaid
public import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
public import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPower
open CanonicalGaussianFrame
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary QuadraticInitialBound CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization CenteredMomentFirstSecondInputGates

theorem actual_error_power_from_bands
    (g : CanonicalSources.Geometry α)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    GaussProvider M fun n T dc Cc J Sp Sf Cm Ce Cd Ct η₀ Q Kc Z₀ =>
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    CanonicalSources.WithSourceFrame M H hH g η₀ Q θ g.lows g.highs Z
      fun εchild C₀ C₁ w σ freq height mesh src =>
    CanonicalSources.WithColumn src fun C D R0 E B τ t =>
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → g.a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    WithSeedProfile g src Z Bseed fun seed p =>
    WithWidthBudget g src Z K sigma asource w fun Mdecl _Mwidth θclip =>
    WithGaussFamily input ((R0*C)*(Ideal.span {prime})^(k+1)) seed fun _Scols _β _family _χ₀ _m =>
    WithLowerLengths input Z fun r =>
    let paid:=(Bcap+Bcap)*g.εmask+εchild+g.εremove+(delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+g.degree+4*n);
    let Hweights:=coefficients g.N g.upper (max 1 g.b) (max 1 g.b) (mass src) Sp p J
      (internalQ Q η₀) Kc v0 εsrc (seed.absNorm:ℝ)
      (CenteredMomentEnergyFirstGaussianCoefficients.fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase v0
        (CenteredMomentSecondInputCapacitySource.lowerFactor g.N g.lower g.a) (seed.absNorm:ℝ)
        (dc+g.degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,Hweights j*CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalErrorAdmitted.actual_error_smaller_gaussian (α:=α) M H hH g εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hboundProvider⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
  obtain ⟨family,hfamily,hbound⟩:=hboundProvider θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input rfl
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+g.degree+4*n)
  let paid:=(Bcap+Bcap)*g.εmask+εchild+g.εremove+(delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤g.N:=
    (live_card_le Bp.val).trans ((live_card_le B.val).trans hcard)
  have hloProd:=CenteredMomentEnergyOriginalProfileControl.lower_product input g.N g.lower g.hlower hcardInput
    (fun i=>hlowerSrc.trans (src.lower_le i.val.val))
  have hlo:CenteredMomentSecondInputCapacitySource.lowerFactor g.N g.lower g.a≤(∏i,input.lo i)*g.a*g.a:=by
    unfold CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg g.a)
  have hcoef:=CenteredMomentEnergyFirstGaussianCoefficients.error_coefficients
    g.N g.upper (max 1 g.b) (max 1 g.b) (mass src) Sp p J (internalQ Q η₀) Kc prime (k+1)
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Km v0 (τ.modulus.absNorm:ℝ) cost Ebase
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
    (∏i,input.lo i) g.a (CenteredMomentSecondInputCapacitySource.lowerFactor g.N g.lower g.a) (seed.absNorm:ℝ)
    (dc+g.degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans g.hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold Km errorCommonRadius;positivity)
    (CenteredMomentSecondInputCapacitySource.lowerFactor_pos g.N g.lower g.a g.hlower g.haPlain) hlo
  have hexp:
      (Bcap+Bcap)*g.εmask+(εchild+g.εremove+errorRemoval prime Z (k+1)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh)=
      errorRemoval prime Z (k+1)+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
    dsimp [paid];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos input).le (powers εsrc j))
  simpa only [CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPower

end

end OAI
