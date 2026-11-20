module
public import OAI.NumberTheory.DirichletL.Energy.CanonicalSources
public import OAI.NumberTheory.DirichletL.Energy.CanonicalSource
public import OAI.NumberTheory.DirichletL.Energy.FirstColumnPairing
public import OAI.NumberTheory.DirichletL.Energy.FirstPhysicalNormalization
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

namespace SevenEighths.CenteredMomentEnergyCanonicalPhysical
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

open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice CenteredMomentSecondRetainedRows CenteredMomentLogDyadic CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn CenteredMomentFirstCommonReferencePower CenteredMomentEnergyCanonicalColumn CenteredMomentFirstNonexceptionalLocalWeightSum


theorem actual_physical (high : Bool)
    (g : CanonicalSources.Geometry α)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0<lowerProduct):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    CanonicalSources.WithInternalModulus M fun η₀ Q =>
    ∃Cphysical:ℝ,0<Cphysical ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    CanonicalSources.WithBands (α:=α) M H hH g.Wslot g.bslot g.a g.b g.L g.Lslot g.lo g.hi g.Mcap g.κ Z η₀ Q g.degree g.S
      fun εchild C₀ C₁ =>
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤g.Lslot) → (∀i,g.lo≤σ i) → (∀i,σ i≤g.hi) → 0≤height → (∀i,|freq i|≤height) →
    CanonicalSources.WithMatchedSource M H hH η₀ θ w σ freq (fun i => g.lows i.val) (fun i => g.highs i.val)
      g.Wslot g.bslot Z g.Mslot g.N g.lower g.upper g.b fun src =>
    lowerProduct≤(∏i,src.lo i)*g.a*g.a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤K →
    ∀p:Profiles g.a g.b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^g.L → src.X₂≤Z^g.L → src.Y₁≤Z^g.L → src.Y₂≤Z^g.L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*g.κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤g.Mcap →
    Real.logb Z (max 1 g.b*max 1 g.b)≤2*θclip →
    g.a0≤CenteredMomentSecondInputCapacitySource.lowerFactor g.N g.lower g.a →
    CanonicalSources.SourceRegime high src Z Mdecl Mwidth →
    (∀j:Fin 4,
      CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*g.εmask+εchild+g.εremove+
          (frequencyLoss Z 32 ξ+reserve+g.θsource)/6+θclip/3+g.κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨U,J,hcolumns⟩:=CenteredMomentEnergyCanonicalSource.actual_original_columns (high:=high)
    (α:=α) M H hH g
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  have hphysical (T:Finset α):=CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) J J (fun i=>|g.highs i.val|) (max 1 g.b) (max 1 g.b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  let Cmass:ℝ:=1+∑T:Finset α,Cp T
  have hCmass:0<Cmass:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
    dsimp [Cmass];linarith
  have hCpCap (T:Finset α):Cp T≤Cmass:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
      (Finset.mem_univ T)
    dsimp [Cmass];linarith
  refine ⟨U,2*(J+J),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hcolumns⟩:=hcolumns η₀ Q hQM hQ0 hQt hQ72
  have hm:=CenteredMomentSecondWindowBudget.profileMoment_nonneg J
  let Cm:ℝ:=Cmass*C*(1+CenteredMomentSecondWindowBudget.profileMoment J)^2
  have hCm:0<Cm:=by dsimp [Cm];positivity
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp (Filter.eventually_all.mpr hp)
  refine ⟨Cm,hCm,max Zp Z₀,hZ₀.trans_le (le_max_right _ _),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hregime hfit
  have hZZ₀:Z₀≤Z:=(le_max_right _ _).trans hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ₀
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤Z^A:=original_volume_cap src Z g.κ A hZ g.hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→g.a≤x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→g.a≤x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*g.εmask+εchild+g.εremove+
    (delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let Fcap:=C*(C₀+C₁+1)*(p.control U)^2*(1+height)^J
  let front:=Fcap*Z^(deficit+base)
  have hFcap:0≤Fcap:=by dsimp [Fcap];positivity
  have hfront:0≤front:=by dsimp [front];positivity
  have hcoeff (j:Fin 4):front*Z^(powers j)≤Fcap*Z^(deficit+ell):=by
    dsimp only [front]
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) hFcap
    have hh:powers j+base≤ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z J J
        (fun j=>front*Z^(powers j)) (fun j=>front*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums <;>
      intro innerL hLcap hLsq χ v
    all_goals
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hcolumns T θ Z hZZ₀ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hregime v
      first
      | simpa only [front,Fcap,powers,delta,paid,deficit,base,add_assoc,
          CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh.1
      | simpa only [front,Fcap,powers,delta,paid,deficit,base,add_assoc,
          CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh.2
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=>by rw [hhiSrc]) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    g.a g.a K g.haPlain g.haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=>ell) (fun _=>ell)
    (fun j=>front*Z^(powers j)) (fun j=>front*Z^(powers j)) hFcap
    (fun j=>mul_nonneg hfront (Real.rpow_nonneg hz.le _))
    (fun j=>mul_nonneg hfront (Real.rpow_nonneg hz.le _))
    hcoeff hcoeff (fun _=>le_rfl)
    (fun _=>le_rfl) (fun lab E _ n hne=>hcols lab E n hne)
  have hconst:Cp T*C*CenteredMomentSecondWindowBudget.profileMoment J^2≤Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
  have hheightProduct:(1+height)^J*(1+|src.t|)^(J+J)≤
      (1+|src.t|+height)^(2*(J+J)):=by
    have heq:(1+|src.t|+height)^(2*(J+J))=
        (1+|src.t|+height)^(J+J)*(1+|src.t|+height)^(J+J):=by
      rw [two_mul, pow_add]
    rw [heq]
    apply mul_le_mul
      ((pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) J).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg src.t]) (by omega)))
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*C*CenteredMomentSecondWindowBudget.profileMoment J^2)*(C₀+C₁+1)*
          (p.control U)^2*((1+height)^J*(1+|src.t|)^(J+J))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalPhysical

end

end OAI
