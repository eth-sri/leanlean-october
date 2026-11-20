module

public import OAI.NumberTheory.DirichletL.Energy.ProfileFront
public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianColumns
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
public import OAI.NumberTheory.DirichletL.Energy.FrozenSourceContext
public import OAI.NumberTheory.DirichletL.Energy.CanonicalWindow
public import OAI.NumberTheory.DirichletL.Energy.SeededProfileContext
public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianContext
public import OAI.FiniteMajorant
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPower
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorUniform
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPaid
public import OAI.NumberTheory.DirichletL.Energy.CanonicalErrorContext

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
open CenteredMomentFrozenSourceContext

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

set_option maxHeartbeats 1600000 in
theorem actual_original_subsets_amplified_power
    (cfg : CanonicalEnergyWindow α)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ForSmallInternalConductors M fun η₀ Q =>
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    AcrossCanonicalBands cfg M H hH Z η₀ Q fun εchild C₀ C₁ =>
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),WithSlotBounds cfg.Lslot cfg.lo cfg.hi w σ freq height mesh <|
    ForCanonicalRaySources (cfg.reindex Subtype.val) M H hH η₀ θ w σ freq Z fun src =>
    ForFrozenSources src fun C D R0 E B τ t =>
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → cfg.a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    WithSeededProfile src w cfg.a cfg.b cfg.L cfg.κ cfg.Mcap Z K sigma Bseed fun seed p Mdecl Mwidth θclip =>
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a →
    AtGaussianScale input Z fun r =>
    let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(gaussianFront p Uprofile Jheight Cbound C₀ C₁ t height*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    AcrossCanonicalBands cfg M H hH Z η₀ Q fun εchild C₀ C₁ =>
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),WithSlotBounds cfg.Lslot cfg.lo cfg.hi w σ freq height mesh <|
    ForCanonicalRaySources (cfg.reindex Subtype.val) M H hH η₀ θ w σ freq Z fun src =>
    ForFrozenSources src fun C D R0 E B τ t =>
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → cfg.a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ t →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    WithSeededProfile src w cfg.a cfg.b cfg.L cfg.κ cfg.Mcap Z K sigma Bseed fun seed p Mdecl Mwidth θclip =>
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a →
    AtGaussianScale input Z fun r =>
    let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(gaussianFront p Uprofile Jheight Cbound C₀ C₁ t height*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) :=by
  have hfamilyM (Aorig : Finset α) :=
    CenteredMomentEnergyCanonicalMainSeparatedPower.actual_main_separated_power (α:=Aorig) M H hH
      (cfg.reindex Subtype.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  choose nM TM dcM CcM hCcM JM SpM SfM hSpM CmM CeM CdM CtM hCmM hCeM hCdM hCtM hmainM using hfamilyM
  have hfamilyE (Aorig : Finset α) :=
    CenteredMomentEnergyCanonicalErrorPower.actual_error_power_from_bands (α:=Aorig) M H hH
      (cfg.reindex Subtype.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  choose nE TE dcE CcE hCcE JE SpE SfE hSpE CmE CeE CdE CtE hCmE hCeE hCdE hCtE hmainE using hfamilyE
  have hlo:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos cfg.N cfg.lower cfg.a cfg.hlower cfg.haPlain
  have hweights (n dc J : ℕ) (Sp T Sf : Finset (ℕ×ℕ)) (Cm Ce Cd Ct Cc : ℝ)
      (hCm : 0 ≤ Cm) (hCe : 0 ≤ Ce) (hCd : 0 ≤ Cd) (hCt : 0 ≤ Ct) (hCc : 0 ≤ Cc) :=
    CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=cfg.a) (b:=cfg.b)
      cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) ((max 1 cfg.Mslot)^cfg.N)
      (CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+cfg.degree+4*n) (dc+cfg.degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans cfg.hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm hCe hCd hCt hCc (zero_le_one.trans hcost)
  choose UjM JjM hjM using fun S0 => hweights (nM S0) (dcM S0) (JM S0)
    (SpM S0) (TM S0) (SfM S0) (CmM S0) (CeM S0) (CdM S0) (CtM S0) (CcM S0)
    (hCmM S0).le (hCeM S0) (hCdM S0).le (hCtM S0).le (hCcM S0).le
  choose UjE JjE hjE using fun S0 => hweights (nE S0) (dcE S0) (JE S0)
    (SpE S0) (TE S0) (SfE S0) (CmE S0) (CeE S0) (CdE S0) (CtE S0) (CcE S0)
    (hCmE S0).le (hCeE S0) (hCdE S0).le (hCtE S0).le (hCcE S0).le
  let Uprofile := Finset.univ.biUnion (fun Aorig : Finset α => UjM Aorig ∪ UjE Aorig)
  let Jheight := ∑ Aorig : Finset α, (JjM Aorig + JjE Aorig)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose KcM hKcM ZjM hZjM hconsumeM using fun Aorig => hmainM Aorig η₀ Q hQM hQ0 hQt hQ72
  choose CjM hCjM hwboundM using fun Aorig => hjM Aorig (internalQ Q η₀) (KcM Aorig) (hKcM Aorig).le
  choose KcE hKcE ZjE hZjE hconsumeE using fun Aorig => hmainE Aorig η₀ Q hQM hQ0 hQt hQ72
  choose CjE hCjE hwboundE using fun Aorig => hjE Aorig (internalQ Q η₀) (KcE Aorig) (hKcE Aorig).le
  obtain ⟨Cbound,hCbound,hCC⟩ := exists_real_majorant 0 (fun Aorig => max (CjM Aorig) (CjE Aorig))
  obtain ⟨Z₀,hZ₀,hZZ⟩ := exists_real_majorant 1 (fun Aorig => max (ZjM Aorig) (ZjE Aorig))
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_,?_⟩
  · intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hposA:=positiveAt_subtype M H hH Aorig cfg.Wslot cfg.bslot (cfg.a/max 1 cfg.b) cfg.b 2 0 cfg.L cfg.Lslot cfg.lo cfg.hi
      cfg.Mcap εchild cfg.κ Z η₀ Q cfg.degree cfg.S C₁ hpos
    let input:=child src C R0 B τ t
    obtain ⟨family,hfamilyM,hbound⟩:=hconsumeM Aorig θ Z ((le_max_left _ _).trans ((hZZ Aorig).trans hZ)) εchild C₀ C₁ hC₀ hC₁ hzero hposA
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower _ _ rfl rfl
    have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
      r hr1 hr2 hr3 hr4
    dsimp only at hg ⊢
    have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
    have hmass:mass src≤(max 1 cfg.Mslot)^cfg.N:=
      CenteredMomentEnergyOriginalProfileControl.slot_product_le src cfg.N (max 1 cfg.Mslot)
        (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
    have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
    have hh:=hwboundM Aorig p Z t height (mass src) (seed.absNorm:ℝ) C₀ C₁
      hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
    dsimp only at hh
    have hfront := front_mono p (UjM Aorig) Uprofile
      (fun x hx => Finset.mem_biUnion.mpr ⟨Aorig, Finset.mem_univ _, Finset.mem_union_left _ hx⟩)
      (JjM Aorig) Jheight ((Nat.le_add_right _ _).trans (Finset.single_le_sum
        (f := fun A0 : Finset α => JjM A0 + JjE A0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ Aorig)))
      (CjM Aorig) Cbound C₀ C₁ t height (hCjM Aorig).le ((le_max_left _ _).trans (hCC Aorig)) hC₀ hC₁ hheight
    apply hg.trans
    refine gaussian_sum_mono (fun j => (hh j).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _)))
      ?_ (volume_pos _).le
    intro j
    fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold mainCommonRadius
    all_goals positivity
  · intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr hN hυ input hinput
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hposA:=positiveAt_subtype M H hH Aorig cfg.Wslot cfg.bslot (cfg.a/max 1 cfg.b) cfg.b 2 0 cfg.L cfg.Lslot cfg.lo cfg.hi
      cfg.Mcap εchild cfg.κ Z η₀ Q cfg.degree cfg.S C₁ hpos
    obtain ⟨family,hfamilyE,hbound⟩:=hconsumeE Aorig θ Z ((le_max_right _ _).trans ((hZZ Aorig).trans hZ)) εchild C₀ C₁ hC₀ hC₁ hzero hposA
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr t hN hυ input hinput
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower _ _ rfl rfl
    have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
      r hr1 hr2 hr3 hr4
    dsimp only at hg ⊢
    have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
    have hmass:mass src≤(max 1 cfg.Mslot)^cfg.N:=
      CenteredMomentEnergyOriginalProfileControl.slot_product_le src cfg.N (max 1 cfg.Mslot)
        (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
    have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
    have hh:=hwboundE Aorig p Z t height (mass src) (seed.absNorm:ℝ) C₀ C₁
      hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
    dsimp only at hh
    have hfront := front_mono p (UjE Aorig) Uprofile
      (fun x hx => Finset.mem_biUnion.mpr ⟨Aorig, Finset.mem_univ _, Finset.mem_union_right _ hx⟩)
      (JjE Aorig) Jheight ((Nat.le_add_left _ _).trans (Finset.single_le_sum
        (f := fun A0 : Finset α => JjM A0 + JjE A0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ Aorig)))
      (CjE Aorig) Cbound C₀ C₁ t height (hCjE Aorig).le ((le_max_right _ _).trans (hCC Aorig)) hC₀ hC₁ hheight
    apply hg.trans
    refine gaussian_sum_mono (fun j => (hh j).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _)))
      ?_ (volume_pos _).le
    intro j
    fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold errorCommonRadius
    all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform

end

end OAI
