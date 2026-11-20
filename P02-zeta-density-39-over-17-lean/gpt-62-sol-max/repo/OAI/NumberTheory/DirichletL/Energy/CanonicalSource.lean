module
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport
public import OAI.NumberTheory.DirichletL.Energy.CanonicalSources
public import OAI.NumberTheory.DirichletL.Energy.FirstTwoSeedAdmission
public import OAI.NumberTheory.DirichletL.Energy.CanonicalColumn
public import OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularPower
public import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn
public import OAI.NumberTheory.DirichletL.Energy.FirstGaussianUniformPowers
public import OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform
public import OAI.NumberTheory.DirichletL.Energy.AmplifierFamilyAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstRawScaleAdmission
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSubsets
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorSubsets
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainHomogeneous
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower
public import OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparated
public import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients
public import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform
public import OAI.NumberTheory.DirichletL.Moments.FrozenFamilyDescent
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
public import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
public import OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid
public import OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidReserve
public import OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
public import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalSource
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary QuadraticInitialBound CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization CenteredMomentFirstSecondInputGates CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput



open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentFirstMixedRightTransport

open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice CenteredMomentSecondRetainedRows CenteredMomentLogDyadic CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn CenteredMomentFirstCommonReferencePower CenteredMomentEnergyCanonicalColumn CenteredMomentFirstNonexceptionalLocalWeightSum


/-- A common profile budget and threshold for the two oriented columns. -/
theorem actual_original_columns (high : Bool)
    (g : CanonicalSources.Geometry α)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    CanonicalSources.WithInternalModulus M fun η₀ Q =>
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    CanonicalSources.WithBands (α:=α) M H hH g.Wslot g.bslot g.a g.b g.L g.Lslot g.lo g.hi g.Mcap g.κ Z η₀ Q g.degree g.S
      fun εchild C₀ C₁ =>
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤g.Lslot) → (∀i,g.lo≤σ i) → (∀i,σ i≤g.hi) → 0≤height → (∀i,|freq i|≤height) →
    CanonicalSources.WithMatchedSource M H hH η₀ θ w σ freq (fun i => g.lows i.val) (fun i => g.highs i.val)
      g.Wslot g.bslot Z g.Mslot g.N g.lower g.upper g.b fun src =>
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles g.a g.b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^g.L → src.X₂≤Z^g.L → src.Y₁≤Z^g.L → src.Y₂≤Z^g.L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*g.κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤g.Mcap →
    Real.logb Z (max 1 g.b*max 1 g.b)≤2*θclip →
    g.a0≤CenteredMomentSecondInputCapacitySource.lowerFactor g.N g.lower g.a →
    CanonicalSources.SourceRegime high src Z Mdecl Mwidth →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*g.εmask+εchild+g.εremove+(delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let bound (C D : Ideal O) (hC : Supported C) (τ : Character) :=
      let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
      (commonEnergy (original src R0 seed0) C hC τ t seed
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
          Z^(deficit+εsrc*(A+1)+primeLoss)*
          ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
            lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight);
    bound C D hC F.left ∧ bound D C hD F.right :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_column (high:=high) (α:=α) M H hH g εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission g.N g.upper (max 1 g.b) (max 1 g.b) A 0 ξ
    g.hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_main_packet g.N g.upper (max 1 g.b) (max 1 g.b) g.lower g.a A Pcap
    g.hupper (le_max_left _ _) (le_max_left _ _) g.hlower g.haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 g.bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=CenteredMomentEnergyFirstTwoSeedAdmission.eventually_error_packet
    g.N g.upper (max 1 g.b) (max 1 g.b) g.lower g.a A Pcap
    g.hupper (le_max_left _ _) (le_max_left _ _) g.hlower g.haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hregime t
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*g.κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z g.κ A hZ g.hκsmall hPs hcapacity
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
  have hends:Endpoints g.upper (max 1 g.b) (max 1 g.b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact g.hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→g.a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→g.a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ g.a g.haPlain hW₁) (lower_profile_zero src.W₂ g.a g.haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedC:seed0∣C:=hcols.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hNC:(C.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.1.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  obtain ⟨_,_,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨_,_,_,hseparate,hpdata,_⟩:=hsep
  have hslot (C' : Ideal O) (τ : Character) (B : actualAllocations src.pools C')
      (q : elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3)))) :
      ∀ j, ∀ I ∈ (activeInput (child src C' R0 B τ t)).slots j, IsCoprime (Ideal.span {q.val}) I := by
    have hd:=elementPool_data _ (fun I hI=>(hpdata I hI).1)
      (fun I hI=>(hpdata I hI).2.1) q.val q.property
    let input:=child src C' R0 B τ t
    let data:=original input (R0*C') seed
    exact original_slot_coprime data.active Z sigma (max 1 g.bslot) eta hZ.le (by positivity)
      hseparate (fun j=>w j.val) (fun j=>hweta j.val) (fun j=>hmatch.scale j.val)
      (fun j _ hx=>((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _))
      data.active_slot (fun j I hI=>input.prime j I (data.active_subset _ hI))
      _ (hpdata _ hd.2.1).1 (hpdata _ hd.2.1).2.2.1
  have hindex (i : Fin 3) : errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7 := by
    have := errorIndex_cases i
    omega
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
        K (volume src)) Z ξ:=by simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  have mainPacket (τ : Character) (hτ : τ=F.left ∨ τ=F.right) :=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ g.κ g.hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
  have errorPacket (τ : Character) (hτ : τ=F.left ∨ τ=F.right) :=herror.2 src hcard hends hlowerSrc hW₁ hW₂ g.κ g.hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock
  constructor
  · obtain ⟨υ,hυ,hbound⟩:=hfamilies F.left
    apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E F.left_modulus
      K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedC
      seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hregime
      hcap hMdecl hMwidth hdrop hclip hsourceLower
    intro B hB
    have hm:=mainPacket F.left (Or.inl rfl) hblock false B t hB
    refine ⟨?_,?_⟩
    · simpa only [mul_one, columnMainRadius, mainRadius, columnIdeal, oppositeIdeal, ite_false, Bool.false_eq_true] using! hm.1
    · intro prime i χ Bp
      have hrad:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
      have he:=errorPacket F.left (Or.inl rfl) false B t seed hB M H fixedBadPrimes (Finset.Subset.refl _)
        prime.val prime.property (errorIndex i+1) (hindex i) (hslot C F.left B prime) Bp χ
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
        (by simpa only [Nat.add_sub_cancel] using hrad)
      rcases he with hdead|hlive
      · exact Or.inl hdead.1
      · exact Or.inr (by simpa only [mul_one, columnErrorRadius, errorRadius, columnIdeal, oppositeIdeal, ite_false, Bool.false_eq_true] using! hlive.1)
  · let Es:=swapSubset C D E
    have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
      exact right_modulus src.η C D hC E χ₁ χ₂ F
    obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
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
      exact houter
    apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap (hcols.2.2.2.2.2.2.trans hradius.1) Es hmod
      K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hcols.2.2.2.2.1
      seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hregime
      hcap hMdecl hMwidth hdrop hclip hsourceLower
    intro B hB
    have hm:=mainPacket F.right (Or.inr rfl) hblock true B t hB
    refine ⟨?_,?_⟩
    · simpa only [mul_one, columnMainRadius, mainRadius, columnIdeal, oppositeIdeal, ite_true,
        Es, swapSubset_generator, nominal_swap] using! hm.1
    · intro prime i χ Bp
      have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
      have he:=errorPacket F.right (Or.inr rfl) true B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
        (errorIndex i+1) (hindex i) (hslot D F.right B prime) Bp χ
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
        (by simpa only [Nat.add_sub_cancel] using hN)
      rcases he with hdead|hlive
      · exact Or.inl hdead.1
      · exact Or.inr (by simpa only [mul_one, columnErrorRadius, errorRadius, columnIdeal, oppositeIdeal, ite_true,
          Es, swapSubset_generator, nominal_swap] using! hlive.1)

end SevenEighths.CenteredMomentEnergyCanonicalSource

end

end OAI
