module

public import OAI.FiniteMajorant

public import OAI.NumberTheory.DirichletL.Energy.CanonicalSourceColumn
public import OAI.NumberTheory.DirichletL.Energy.FirstColumnPairing
public import OAI.NumberTheory.DirichletL.Energy.FirstPhysicalNormalization
public import OAI.NumberTheory.DirichletL.Energy.FirstTwoSeedAdmission
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

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalPhysical
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
open CenteredMomentEnergyCanonicalSourceColumn (WidthAdmissible)
open CenteredMomentFirstNonexceptionalLocalWeightSum

theorem actual_physical
    (cfg : CanonicalEnergyWindow α)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0<lowerProduct) (high : Bool) :
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ForSmallInternalConductors M fun η₀ Q =>
    ∃Cphysical:ℝ,0<Cphysical ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    AcrossCanonicalBands cfg M H hH Z η₀ Q fun εchild C₀ C₁ =>
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤cfg.Lslot) → (∀i,cfg.lo≤σ i) → (∀i,σ i≤cfg.hi) → 0≤height → (∀i,|freq i|≤height) →
    ForCanonicalRaySources (cfg.reindex Subtype.val) M H hH η₀ θ w σ freq Z fun src =>
    lowerProduct≤(∏i,src.lo i)*cfg.a*cfg.a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤K →
    ∀p:Profiles cfg.a cfg.b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^cfg.L → src.X₂≤Z^cfg.L → src.Y₁≤Z^cfg.L → src.Y₂≤Z^cfg.L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*cfg.κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤cfg.Mcap →
    Real.logb Z (max 1 cfg.b*max 1 cfg.b)≤2*θclip →
    cfg.a0≤CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a →
    WidthAdmissible high src Z Mdecl Mwidth →
    (∀j:Fin 4,
      CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*cfg.εmask+εchild+cfg.εremove+
          (frequencyLoss Z 32 ξ+reserve+cfg.θsource)/6+θclip/3+cfg.κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨UL,JL,hleft⟩:=CenteredMomentEnergyCanonicalSourceColumn.actual_original_column
    (α:=α) M H hH cfg
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed high false
  obtain ⟨UR,JR,hright⟩:=CenteredMomentEnergyCanonicalSourceColumn.actual_original_column
    (α:=α) M H hH cfg
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed high true
  have hphysical (T:Finset α):=CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) JL JR (fun i=>|cfg.highs i.val|) (max 1 cfg.b) (max 1 cfg.b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  obtain ⟨Cmass, hCmass, hCpCap⟩ := exists_real_majorant 0 Cp
  refine ⟨UL∪UR,2*(JL+JR),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CL,hCL,ZL,hZL,hleft⟩:=hleft η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CR,hCR,ZR,hZR,hright⟩:=hright η₀ Q hQM hQ0 hQt hQ72
  have hmL:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JL
  have hmR:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JR
  let Cm:ℝ:=Cmass*(CL+CR)*(1+CenteredMomentSecondWindowBudget.profileMoment JL)*
    (1+CenteredMomentSecondWindowBudget.profileMoment JR)
  have hCm:0<Cm:=by dsimp [Cm];positivity
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hp
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp hall
  refine ⟨Cm,hCm,max Zp (max ZL ZR),lt_of_lt_of_le hZL
    ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hwidth hfit
  have hZL':ZL≤Z:=(le_max_left _ _).trans ((le_max_right _ _).trans hZZ)
  have hZR':ZR≤Z:=(le_max_right _ _).trans ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hZL.trans_le hZL'
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤Z^A:=original_volume_cap src Z cfg.κ A hZ cfg.hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→cfg.a≤x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→cfg.a≤x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*cfg.εmask+εchild+cfg.εremove+
    (delta+reserve+cfg.θsource)/6+θclip/3+cfg.κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let FL:=CL*(C₀+C₁+1)*(p.control UL)^2*(1+height)^JL
  let FR:=CR*(C₀+C₁+1)*(p.control UR)^2*(1+height)^JR
  let Fcap:ℝ:=(CL+CR)*(C₀+C₁+1)*(p.control (UL∪UR))^2*(1+height)^(JL+JR)
  let frontL:=FL*Z^(deficit+base)
  let frontR:=FR*Z^(deficit+base)
  have hfrontL:0≤frontL:=by dsimp [frontL,FL];positivity
  have hfrontR:0≤frontR:=by dsimp [frontR,FR];positivity
  have hFcap:0≤Fcap:=by dsimp [Fcap];positivity
  have hcontrol (S₁:Finset (ℕ×ℕ))(hs:S₁⊆UL∪UR):p.control S₁≤p.control (UL∪UR):= p.control_mono hs
  have hFL:FL≤Fcap:=by
    dsimp [FL,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UL
    · exact hcontrol UL Finset.subset_union_left
    · linarith
    · omega
  have hFR:FR≤Fcap:=by
    dsimp [FR,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UR
    · exact hcontrol UR Finset.subset_union_right
    · linarith
    · omega
  have hcoeff (F:ℝ)(hF:F≤Fcap)(j:Fin 4):
      (F*Z^(deficit+base))*Z^(powers j)≤Fcap*Z^(deficit+ell):=by
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul hF (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (Real.rpow_nonneg hz.le _) hFcap
    have hh:powers j+base≤ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z JL JR
        (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hleft T θ Z hZL' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.left (Or.inl rfl)
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidth v
      simpa only [Bool.false_eq_true, if_false, frontL,FL,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
    · intro innerL hLcap hLsq χ v
      let hs:=CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hright T θ Z hZR' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.right rfl
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidth v
      simpa only [if_true, frontR,FR,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=>by rw [hhiSrc] <;> rfl) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    cfg.a cfg.a K cfg.haPlain cfg.haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=>ell) (fun _=>ell)
    (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) hFcap
    (fun j=>mul_nonneg hfrontL (Real.rpow_nonneg hz.le _))
    (fun j=>mul_nonneg hfrontR (Real.rpow_nonneg hz.le _))
    (hcoeff FL hFL) (hcoeff FR hFR) (fun _=>le_rfl)
    (fun _=>le_rfl) (fun lab E _ n hne=>hcols lab E n hne)
  have hconst:Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
      CenteredMomentSecondWindowBudget.profileMoment JR≤Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
    · linarith
  have hheightProduct:(1+height)^(JL+JR)*(1+|src.t|)^(JL+JR)≤
      (1+|src.t|+height)^(2*(JL+JR)):=by
    have heq:(1+|src.t|+height)^(2*(JL+JR))=
        (1+|src.t|+height)^(JL+JR)*(1+|src.t|+height)^(JL+JR):=by
      rw [show 2*(JL+JR)=(JL+JR)+(JL+JR) by omega]
      exact pow_add _ _ _
    rw [heq]
    apply mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
          CenteredMomentSecondWindowBudget.profileMoment JR)*(C₀+C₁+1)*
          (p.control (UL∪UR))^2*((1+height)^(JL+JR)*(1+|src.t|)^(JL+JR))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalPhysical

end

end OAI
