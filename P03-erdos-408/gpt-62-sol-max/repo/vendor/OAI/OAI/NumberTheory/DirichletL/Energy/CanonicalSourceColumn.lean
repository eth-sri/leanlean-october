module

public import OAI.NumberTheory.DirichletL.Energy.FirstTwoSeedAdmission
public import OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularLower
public import OAI.NumberTheory.DirichletL.Energy.SeededProfileContext
public import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
public import OAI.NumberTheory.DirichletL.Moments.FirstCommonReferencePower
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedDiagonal
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedExceptionalLow
public import OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters
public import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform
public import OAI.NumberTheory.DirichletL.Energy.AmplifierFamilyAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstRawScaleAdmission
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower
public import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
public import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
public import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform
public import OAI.NumberTheory.DirichletL.Moments.SeededGaussianPower
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
public import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
public import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
public import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

public import OAI.NumberTheory.DirichletL.Energy.CanonicalWindow

public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianContext

public import OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalSourceColumn
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve
open CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization Filter
open CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentEnergyCanonicalAmplifiedUniform
open CenteredMomentEnergyAmplifierFamilyAdmission CenteredMomentEnergyFirstLiveAdmission
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentEnergyFirstRawScaleAdmission
open CenteredMomentEnergyInputParentCapacity CenteredMomentFirstReferenceSource
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationEligibility CenteredMomentFirstPhysicalSource
open CenteredMomentFirstPhysicalDyadicRows CenteredMomentFirstAmplifiedPowerBudget
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower
open CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstMixedRightTransport

/-- The volume bound in the low regime or the four lower scale bounds in the high regime. -/
def WidthAdmissible {ι : Type*} [Fintype ι] (high : Bool) (src : Input ι) (Z Mdecl Mwidth : ℝ) : Prop :=
  if high then
    Mwidth ≤ Mdecl ∧ Z^(Mwidth/4) ≤ src.X₁ ∧ Z^(Mwidth/4) ≤ src.X₂ ∧
      Z^(Mwidth/4) ≤ src.Y₁ ∧ Z^(Mwidth/4) ≤ src.Y₂
  else Real.logb Z (volume src) ≤ 5*Mdecl/6

lemma source_mass_cap {ι:Type*}[Fintype ι](s:Input ι)(N:ℕ)(Mslot:ℝ)
    (hc:Fintype.card ι≤N)(hM:∀i,s.M i≤Mslot):mass s≤(max 1 Mslot)^N:=by
  calc
    _≤∏i:ι,max 1 Mslot:=by
      apply Finset.prod_le_prod₀
      · intro i _;exact zero_le_one.trans (s.M_ge_one i)
      · intro i _;exact (hM i).trans (le_max_right _ _)
    _=(max 1 Mslot)^Fintype.card ι:=by simp
    _≤_:=pow_le_pow_right₀ (le_max_left _ _) hc

lemma inherited_height_split (t height:ℝ)(J:ℕ)(hh:0≤height):
    (1+|t|+height)^J≤(1+height)^J*(1+|t|)^(2*J):=by
  have hbase:1+|t|+height≤(1+height)*(1+|t|):=by
    nlinarith [abs_nonneg t,mul_nonneg hh (abs_nonneg t)]
  calc
    _≤((1+height)*(1+|t|))^J:=pow_le_pow_left₀ (by positivity) hbase J
    _=(1+height)^J*(1+|t|)^J:=mul_pow _ _ _
    _≤_:=mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega:J≤2*J)) (by positivity)

open scoped Classical BigOperators ContDiff

open CenteredMomentEnergyCanonicalAnnularLower


private theorem finite_power_budget (upper nc Z eps Bcommon deficit primeLoss G F seed:ℝ)
    (N:ℕ)(hupper:1≤upper)(hnc:0≤nc)(hZ:1<Z)(heps:0≤eps)(heps1:eps≤1)
    (hncap:nc≤Z^Bcommon)(hG:0≤G)
    (H srcLoss actualLoss:Fin 4→ℝ)(hH:∀j,0≤H j)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    nc^eps*(∑j:Fin 4,(upper^N)^(powers eps j)*
      (G*H j*Z^(deficit+actualLoss j+primeLoss)))≤
      (upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+actualLoss j):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hncPow:nc^eps≤Z^(eps*Bcommon):=by
    have hh:=Real.rpow_le_rpow hnc hncap heps
    simpa only [←Real.rpow_mul hz.le,mul_comm Bcommon eps] using hh
  have hu:1≤upper^N:=one_le_pow₀ hupper
  have hup (j:Fin 4):(upper^N)^(powers eps j)≤upper^N:=by
    have hp:powers eps j≤1:=by fin_cases j <;> simp [powers] <;> linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hp
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj0 := hH j
  calc
    _≤Z^(eps*Bcommon)*(upper^N*(G*(F*Z^(srcLoss j)/seed)*Z^(deficit+actualLoss j+primeLoss))):=by
      apply mul_le_mul hncPow _ (by positivity) (by positivity)
      apply mul_le_mul (hup j) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left (hbound j) hG
    _=(upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*Z^(srcLoss j+actualLoss j):=by
      calc
        _=(upper^N*G*F/seed)*(Z^(eps*Bcommon)*Z^(srcLoss j)*Z^(deficit+actualLoss j+primeLoss)):=by ring
        _=_:=by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          rw [show eps*Bcommon + srcLoss j + (deficit+actualLoss j+primeLoss) =
            (deficit+eps*Bcommon+primeLoss)+(srcLoss j+actualLoss j) by ring,
            Real.rpow_add hz]
          ring

theorem actual_original_column
    (cfg : CanonicalEnergyWindow α)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed) (high right : Bool) :
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ForSmallInternalConductors M fun η₀ Q =>
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    AcrossCanonicalBands cfg M H hH Z η₀ Q fun εchild C₀ C₁ =>
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤cfg.Lslot) → (∀i,cfg.lo≤σ i) → (∀i,σ i≤cfg.hi) → 0≤height → (∀i,|freq i|≤height) →
    ForCanonicalRaySources (cfg.reindex Subtype.val) M H hH η₀ θ w σ freq Z fun src =>
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),(if right then τ=F.right else τ=F.left ∨ τ=F.right) →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles cfg.a cfg.b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^cfg.L → src.X₂≤Z^cfg.L → src.Y₁≤Z^cfg.L → src.Y₂≤Z^cfg.L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*cfg.κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤cfg.Mcap →
    Real.logb Z (max 1 cfg.b*max 1 cfg.b)≤2*θclip →
    cfg.a0≤CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a →
    WidthAdmissible high src Z Mdecl Mwidth →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let Cpick := if right then D else C;
    let Dpick := if right then C else D;
    let hpick : Supported Cpick := by cases right <;> assumption;
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(Cpick.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance Cpick Dpick Z);
    (commonEnergy (original src R0 seed0) Cpick hpick τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  let Bcap:=readyBudget A Pcap
  have hBcap:0≤Bcap:=readyBudget_nonneg A Pcap hA hPcap
  have hAmp:0≤amplifierCap A 0 ξ:=by unfold amplifierCap;positivity
  obtain ⟨U,J,huniform⟩:=actual_original_subsets_amplified_power (α:=α) M H hH
    cfg εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma referenceCost hsigma hξsmall referenceCost_ge_one
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers cfg.N cfg.lower cfg.upper εsrc cfg.hlower cfg.hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp : 0 ≤ Mamp := hAmp
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 cfg.Mslot)^(2*cfg.N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Zbase,hZbase,hm,he⟩:=huniform η₀ Q hQM hQ0 hQt hQ72
  have hall:=Filter.eventually_all.mpr (fun Aorig:Finset α=>
    eventually_original_subsets_power_amplification (Ω:=Aorig) M H hH fixedBadPrimes (Finset.Subset.refl _)
      sigma primeLoss (Pcap+A+1) Bseed (amplifierCap A 0 ξ) (max 1 cfg.bslot) eta 1 ξ reserve
      hsigma hPrimeLoss hAmp (by positivity) heta (by norm_num) hξ.le hreserve)
  have hsourceEvent:=eventually_source_admission cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) A 0 ξ
    cfg.hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_main_packet cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) cfg.lower cfg.a A Pcap
    cfg.hupper (le_max_left _ _) (le_max_left _ _) cfg.hlower cfg.haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 cfg.bslot) eta hsigma hPrimeLoss hAmp heta
  have herrorEvent:=CenteredMomentEnergyFirstTwoSeedAdmission.eventually_error_packet
    cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) cfg.lower cfg.a A Pcap
    cfg.hupper (le_max_left _ _) (le_max_left _ _) cfg.hlower cfg.haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and
      (hall.and (eventually_ge_atTop Zbase))))))
  let Ccolumn:=Cb*cfg.upper^cfg.N*avg*Ca*(max 1 cfg.Mslot)^(2*cfg.N)
  have := cfg.hupper
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidth t
  obtain ⟨hsource,hmain,herror,hsepdata,hampSet,hZZbase⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZZbase
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*cfg.κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z cfg.κ A hZ cfg.hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints cfg.upper (max 1 cfg.b) (max 1 cfg.b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact cfg.hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→cfg.a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→cfg.a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ cfg.a cfg.haPlain hW₁) (lower_profile_zero src.W₂ cfg.a cfg.haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1, CanonicalEnergyWindow.reindex] using hb1max)
    (by simpa only [abs_of_nonneg hb2, CanonicalEnergyWindow.reindex] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let H0:=dyadicScale (n 1)
  have hH0 : 0 < H0 := zero_lt_one.trans hamp.2.1
  have hHcap : 8*H0 ≤ Z^Mamp := hamp.2.2.2.1
  have hPcard := (hampSet (∅:Finset α)).2.2.1
  choose υ hυ henergy using fun (τ : Character) (U : Finset α) => (hampSet U).2.2.2 τ
  suffices hbound : ∀(C D:Ideal O)(hC:Supported C), Supported D → primeSupport C=primeSupport D →
    (C.absNorm:ℝ)≤Z^(A+1) → ∀(E:Finset (CommonIndex C D))(τ:Character), seed0∣C →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
        K (volume src)) Z ξ →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      (∀ j, ∀ I ∈ (activeInput (child src C R0 B τ t)).slots j, IsCoprime (Ideal.span {prime.val}) I) →
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control U)^2*(1+height)^J*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*J) by
    have hchar : τ = F.left ∨ τ = F.right := by
      cases right
      · exact hτ
      · exact Or.inr hτ
    have hmAll :=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ cfg.κ cfg.hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hchar
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock
    have heAll :=herror.2 src hcard hends hlowerSrc hW₁ hW₂ cfg.κ cfg.hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hchar
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock
    cases right
    · dsimp only at hτ ⊢
      have hseedC := hcols.2.2.2.1
      have hNC : (C.absNorm : ℝ) ≤ Z^(A+1) := hcols.2.2.2.2.2.1.trans hradius.1
      have hmod:τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
          Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}:=by
        rcases hτ with rfl|rfl
        · exact F.left_modulus
        · exact F.right_modulus
      have houter:dyadicScale (n 1)≤4*frequencyRadius
          (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
            K (volume src)) Z ξ:=by simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
      apply hbound C D hC hD hCD hNC E τ hseedC hmod houter
      intro B hB
      have hm := hmAll false B t hB
      refine ⟨?_,?_⟩
      · simpa only [mul_one] using! hm.1
      · intro prime i χ Bp hcop
        have hk:errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by
          have := errorIndex_cases i; omega
        have hrad:=hυ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
        have he := heAll false B t seed hB M H fixedBadPrimes (Finset.Subset.refl _)
          prime.val prime.property (errorIndex i+1) hk hcop Bp χ
          (υ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
          (by simpa only [Nat.add_sub_cancel] using hrad)
        rcases he with hdead|hlive
        · exact Or.inl hdead.1
        · exact Or.inr (by simpa only [mul_one] using! hlive.1)
    · dsimp only at hτ ⊢
      subst τ
      have hseedD := hcols.2.2.2.2.1
      have hND : (D.absNorm : ℝ) ≤ Z^(A+1) := hcols.2.2.2.2.2.2.trans hradius.1
      let Es:=swapSubset C D E
      have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
          Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
        exact right_modulus src.η C D hC E χ₁ χ₂ F
      have hnom:firstNominalScale D C
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
          firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
        dsimp only [Es]
        rw [swapSubset_generator,nominal_swap]
      have houter:dyadicScale (n 1)≤4*frequencyRadius
          (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
            K (volume src)) Z ξ:=by
        rw [hnom]
        simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
      apply hbound D C hD hC hCD.symm hND Es F.right hseedD hmod houter
      intro B hB
      refine ⟨?_,?_⟩
      · simpa only [mul_one, columnMainRadius, columnIdeal, oppositeIdeal, ite_true,
          mainRadius, swapSubset_generator, nominal_swap, Es] using! (hmAll true B t hB).1
      · intro prime i χ Bp hslot
        have hk:=errorIndex_cases i
        have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
        have hN:=hυ F.right Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
        have he := heAll true B t seed hB M H fixedBadPrimes (Finset.Subset.refl _)
          prime.val prime.property (errorIndex i+1) hk' hslot Bp χ
          (υ F.right Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
          (by simpa only [Nat.add_sub_cancel] using hN)
        rcases he with hdead|hlive
        · exact Or.inl hdead.1
        · exact Or.inr (by simpa only [mul_one, columnErrorRadius, columnIdeal, oppositeIdeal, ite_true,
            errorRadius, swapSubset_generator, nominal_swap, Es] using! hlive.1)
  intro C D hC hD hCD hNC E τ hseed0 hmod houter hpackets
  let delta:=frequencyLoss Z 32 ξ
  let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=(if high then Mwidth/4 else parentLower src Z)-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    obtain ⟨hreadym,herrorPacket⟩ := hpackets B hB
    have hann : childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0 ≤
        (∑ j, sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
          (fun j => Hcoef j * mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving
            (parentLower src Z-Real.logb Z (C.absNorm:ℝ)) j)
          (fun prime i χ j => Hcoef j * errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
            (Kerror prime i χ) deficit paid saving
            (parentLower src Z-Real.logb Z (C.absNorm:ℝ)-errorRemoval prime Z (errorIndex i+1)) j)
          (powers εsrc) j * (volume (child src C R0 B τ t))^(powers εsrc j)) *
          mass (child src C R0 B τ t)^2 := by
      let input:=child src C R0 B τ t
      let delta:=frequencyLoss Z 32 ξ
      have hdelta:0≤delta:=frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le
      have hRC:(R0*C).absNorm=R0.absNorm*C.absNorm:=map_mul _ _ _
      have hRcommon:( (R0*C).absNorm:ℝ)≤Z^(Pcap+A+1):=by
        rw [hRC,Nat.cast_mul]
        calc
          _≤Z^Pcap*Z^(A+1):=mul_le_mul hRcap hNC (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
          _=Z^(Pcap+A+1):=by rw [←Real.rpow_add (by linarith:0<Z)];congr 1;ring
      have hmainlower:=main_minimum_lower src C R0 hC.1 B τ t Z hZ
      have hmain:=hm Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
        w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
        hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
        K delta reserve cfg.a0 hK cfg.ha0 hdelta hreserve.le le_rfl
        hreadym seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
        hcap hMdecl hMwidth hdrop hclip hsourceLower _
        hmainlower.1 hmainlower.2.1 hmainlower.2.2.1 hmainlower.2.2.2
      let rbase := parentLower src Z - Real.logb Z (C.absNorm:ℝ)
      let amain := fun j => Hcoef j * mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        deficit paid saving rbase j
      let aerror := fun (prime : elementPool P) (i : Fin 3) (χ : RayCharacter) j => Hcoef j * errorPowers prime (errorIndex i+1)
        (τ.modulus.absNorm:ℝ) Z (Kerror prime i χ) deficit paid saving
        (rbase-errorRemoval prime Z (errorIndex i+1)) j
      have haerror : ∀ prime i χ j, 0 ≤ aerror prime i χ j := fun prime i χ j =>
        mul_nonneg (hHcoef j)
          (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j)
      have hsupp:∀i,Function.support (input.W i)⊆Set.Iic (max 1 cfg.bslot):=by
        intro i x hx
        exact ((src.support i.val hx).2.trans (hhi i.val)).trans (le_max_right _ _)
      let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun i=>w i.val
      have hz:∀i,z i≤eta:=fun i=>hweta i.val
      have hlen:∀i,input.P i=Z^(z i):=fun i=>hmatch.scale i.val
      obtain ⟨_,_,_,hsep,hdata,_⟩:=hsepdata
      have herror:∀prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))),
          ∀i:Fin 3,∀χ:RayCharacter,
          ∀Bp:actualAllocations (activeInput input).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
          childNormalizedGaussSource (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1))
            (R0*C) seed Bp (υ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t
            CenteredMomentFirstAmplificationChoice.ballProfile
            (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))≤
          (∑j,aerror prime i χ j*(volume (child (activeInput input)
            ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
            (υ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t))^(powers εsrc j))*
            mass (child (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
            (υ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t)^2:=by
        intro prime i χ Bp
        have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
          (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
        have hprime:prime.val≠0:=hd.1.ne_zero
        have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
          exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
            Z sigma (max 1 cfg.bslot) eta hZ.le (by positivity) hsep z hz hlen hsupp
            (original input (R0*C) seed).active_slot
            (fun j Q hQ=>input.prime j Q ((original input (R0*C) seed).active_subset _ hQ))
            _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
        have hk:=CenteredMomentFirstAmplificationChoice.errorIndex_cases i
        have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
        have hN:=hυ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
        have hvcap:=actual_error_reference_cap τ _ χ prime.val hprime (errorIndex i) hk Z hZ hN
        have hre:=herrorPacket prime i χ Bp hcop
        rcases hre with hdead|hlive
        · change normalizedGaussSource _ _ _ _ _≤_
          apply (CenteredMomentFirstSecondInputGates.normalized_zero _ _ _ hdead _ _).le.trans
          exact mul_nonneg (Finset.sum_nonneg (fun j _=>mul_nonneg (haerror prime i χ j)
            (Real.rpow_nonneg (volume_pos _).le _))) (sq_nonneg _)
        · have cfg.hlower:=error_minimum_lower src C R0 hC.1 B τ t prime.val hprime
            (errorIndex i+1) Bp (υ τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t Z hZ
          have hprimeScale: sigma/6≤Real.logb Z (normValue prime.val):=by
            have hh:=Real.logb_le_logb_of_le hZ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/6)) (hdata _ hd.2.1).2.2.1
            simpa only [normValue,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
          have hh:=he Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
            w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
            hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
            K delta reserve cfg.a0 hK cfg.ha0 hdelta hreserve.le le_rfl
            prime.val hprime (errorIndex i) hk hprimeScale hcop Bp _ χ hN hvcap _ rfl
            hlive seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
            hcap hMdecl hMwidth hdrop hclip hsourceLower _
            cfg.hlower.1 cfg.hlower.2.1 cfg.hlower.2.2.1 cfg.hlower.2.2.2
          exact hh
      have hE:Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}≠0:=
        Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
      have hann:=henergy τ Aorig (CenteredMomentCommonProfile.liveIndices B.val) input rfl hsupp z hz hlen
        (R0*C) seed (mul_ne_zero hR0 hC.1) hseedne hRcommon hseedCap
        (Real.logb Z (D.absNorm:ℝ)) (Real.logb Z (C.absNorm:ℝ)) C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hE K (volume src) _
        hK (volume_pos src) (by simp only [one_mul];exact le_rfl) H0 hH0 houter hHcap
        amain aerror (powers εsrc) haerror (by simpa only [mul_one,nominalLog,input,amain,Hcoef,Kmain,mainRadius,paid,deficit,rbase,delta] using hmain)
        (by simpa only [mul_one,nominalLog,errorRadius,delta] using herror)
      apply hann.trans_eq
      rw [source_coefficients_identity _ _ _ (volume_pos input).le]
      dsimp only [normValue]
      ring
    cases high with
    | false => exact hann
    | true =>
      obtain ⟨_, hx₁, hx₂, hy₁, hy₂⟩ := hwidth
      exact hann.trans (actual_high_annular_sum src P C D R0 E B τ t
        K Z sigma delta reserve Mamp deficit paid saving Mwidth εsrc hZ hsigma hMamp
        hx₁ hx₂ hy₁ hy₂ Hcoef hHcoef)
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hscalar :
      (∑ j, normalizedPower cfg.upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) cfg.N (powers εsrc j)) ≤
      (cfg.upper^cfg.N*avg*front/(seed.absNorm:ℝ))*Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j) := by
    let credit : ℝ := if high then Mwidth/4 else 0
    have hv : Real.logb Z (volume src) ≤ Mdecl := by
      cases high with
      | false =>
        have hl : Real.logb Z (volume src) ≤ 5*Mdecl/6 := hwidth
        linarith
      | true =>
        have hV := original_volume_cap src Z cfg.κ Mdecl hZ cfg.hκsmall hPs
          (by simpa only [hlogs] using hcap)
        exact (Real.logb_le_iff_le_rpow hZ (volume_pos src)).mpr hV
    have hb : Real.logb Z (volume src) + (Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))/6 ≤
        Mdecl + 2*credit/3 := by
      cases high with
      | false =>
        have hl : Real.logb Z (volume src) ≤ 5*Mdecl/6 := hwidth
        dsimp [credit]
        linarith
      | true =>
        dsimp [credit]
        linarith
    have hc := CenteredMomentFirstScale.norm_pos C hC.1
    have hclog := Real.logb_nonneg hZ (QuadraticMainBoundary.norm_one_le hC.1)
    have hmain : credit ≤ Real.logb Z (C.absNorm:ℝ) + max rmain 0 := by
      cases high <;> dsimp [credit,rmain]
      · exact add_nonneg hclog (le_max_right _ _)
      · linarith [le_max_left (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) (0:ℝ)]
    have herr : ∀ (prime : elementPool P) (i : Fin 3) (χ : RayCharacter), credit ≤ Real.logb Z (C.absNorm:ℝ) +
        errorRemoval prime Z (errorIndex i+1) + max (rerror prime i χ) 0 := by
      intro prime i χ
      cases high with
      | false =>
        dsimp [credit]
        apply add_nonneg (add_nonneg hclog ?_) (le_max_right _ _)
        have hp := elementPool_data P
          (fun Q hQ => (primePool_data M H fixedBadPrimes (Finset.Subset.refl _) _ _ _ Q hQ).1)
          (fun Q hQ => (primePool_data M H fixedBadPrimes (Finset.Subset.refl _) _ _ _ Q hQ).2) prime prime.property
        have hl := Real.logb_nonneg hZ (normValue_ge_one _ hp.1.ne_zero)
        unfold errorRemoval
        positivity
      | true =>
        have hh := le_max_left (rerror prime i χ) 0
        dsimp [rerror,rmain] at hh
        dsimp [credit,rerror,rmain]
        linarith
    have hav := actual_four_coefficients M H fixedBadPrimes (Finset.Subset.refl _)
      src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl A Mamp primeLoss credit
      hK (volume_pos src) hZ hsigma hεsrc.le hMA hMdecl hv hb hPrimeLoss.le hMamp hPcard hmod
      Hcoef hHcoef rmain rerror hmain herr
    have hn := actual_power_reference_identity P ((Mamp+2*sigma)/(sigma/6)) cfg.upper (volume src) (C.absNorm:ℝ)
      (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z) εsrc cfg.N Hcoef
      Kmain (sigma/3) deficit paid saving rmain Kerror rerror (volume_pos src) hc hq hZpos
    dsimp only at hn hav
    refine le_trans ?_ (finite_power_budget cfg.upper (C.absNorm:ℝ) Z εsrc (A+1) deficit primeLoss
      avg front (seed.absNorm:ℝ) cfg.N cfg.hupper (Nat.cast_nonneg _) hZ hεsrc.le heps1 hNC havg.le
      Hcoef _ (lossVector sigma delta reserve paid εsrc A saving) hHcoef (fun j=>le_rfl))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _=> ?_)
    rw [show normalizedPower cfg.upper (volume src) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (CenteredMomentFirstMixedAllowance.allowance C D Z) εsrc (coeff j) cfg.N (powers εsrc j) = _ from hn j]
    exact (mul_le_mul_of_nonneg_left (hav j) (by positivity)).trans_eq (by ring)
  have hmass:=source_mass_cap src cfg.N cfg.Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 cfg.Mslot)^(2*cfg.N):=by
    calc
      _≤((max 1 cfg.Mslot)^cfg.N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ref*(Cb*mass src^2*∑j,normalizedPower cfg.upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) cfg.N (powers εsrc j)):=hcommonBound
    _≤ref*(Cb*mass src^2*((cfg.upper^cfg.N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ref*(Cb*(max 1 cfg.Mslot)^(2*cfg.N)*((cfg.upper^cfg.N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans cfg.hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans cfg.hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring


end SevenEighths.CenteredMomentEnergyCanonicalSourceColumn

end

end OAI
