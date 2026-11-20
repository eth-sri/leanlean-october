module
public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianFrame
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

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform
open CanonicalGaussianFrame
open CenteredMomentEnergyFirstGaussianProfileWeights
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

theorem actual_original_subsets_amplified_power
    (g : CanonicalSources.Geometry α)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    CanonicalSources.WithInternalModulus M fun η₀ Q =>
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    CanonicalSources.WithSourceFrame M H hH g η₀ Q θ (fun i => g.lows i.val) (fun i => g.highs i.val) Z
      fun εchild C₀ C₁ w σ freq height mesh src =>
    CanonicalSources.WithColumn src fun C D R0 E B τ t =>
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → g.a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    WithSeedProfile g src Z Bseed fun seed p =>
    WithWidthBudget g src Z K sigma asource w fun Mdecl _Mwidth θclip =>
    WithLowerLengths input Z fun r =>
    let paid:=(Bcap+Bcap)*g.εmask+εchild+g.εremove+(delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,profileWeight p Uprofile Jheight Cbound C₀ C₁ t height Z (seed.absNorm:ℝ) (losses εsrc δsrc θsrc Bcap j)*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    CanonicalSources.WithSourceFrame M H hH g η₀ Q θ (fun i => g.lows i.val) (fun i => g.highs i.val) Z
      fun εchild C₀ C₁ w σ freq height mesh src =>
    CanonicalSources.WithColumn src fun C D R0 E B τ t =>
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → g.a0≤asource →
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
    WithSeedProfile g src Z Bseed fun seed p =>
    WithWidthBudget g src Z K sigma asource w fun Mdecl _Mwidth θclip =>
    WithLowerLengths input Z fun r =>
    let paid:=(Bcap+Bcap)*g.εmask+εchild+g.εremove+(delta+reserve+g.θsource)/6+θclip/3+g.κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,profileWeight p Uprofile Jheight Cbound C₀ C₁ t height Z (seed.absNorm:ℝ) (losses εsrc δsrc θsrc Bcap j)*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) :=by
  obtain ⟨Um,Jm,hm⟩:=
    CenteredMomentEnergyCanonicalMainSubsets.actual_original_subsets_main_power (α:=α) M H hH g εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  obtain ⟨Ue,Je,he⟩:=
    CenteredMomentEnergyCanonicalErrorSubsets.actual_original_subsets_error_power (α:=α) M H hH g εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Um∪Ue,max Jm Je,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cm,hCm,Zm,hZm,hmain⟩:=hm η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ce,hCe,Ze,hZe,herror⟩:=he η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cm+Ce,add_pos hCm hCe,max Zm Ze,lt_of_lt_of_le hZm (le_max_left _ _),?_,?_⟩
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=hmain Aorig θ Z ((le_max_left _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    dsimp only at hg ⊢
    have hz : 0<Z := zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply weighted_energy_sum_mono (volume_pos _).le ?_ (fun j => ?_)
    · intro j
      fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
        try unfold mainCommonRadius
      all_goals positivity
    · exact profileWeight_mono p Finset.subset_union_left (le_max_left _ _) hCm.le
        (le_add_of_nonneg_right hCe.le) hC₀ hC₁ hheight hz.le (Nat.cast_nonneg _)
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr hN hυ input hinput
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=herror Aorig θ Z ((le_max_right _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr t hN hυ input hinput
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    dsimp only at hg ⊢
    have hz : 0<Z := zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply weighted_energy_sum_mono (volume_pos _).le ?_ (fun j => ?_)
    · intro j
      fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
        try unfold errorCommonRadius
      all_goals positivity
    · exact profileWeight_mono p Finset.subset_union_right (le_max_right _ _) hCe.le
        (le_add_of_nonneg_left hCm.le) hC₀ hC₁ hheight hz.le (Nat.cast_nonneg _)

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform

end

end OAI
