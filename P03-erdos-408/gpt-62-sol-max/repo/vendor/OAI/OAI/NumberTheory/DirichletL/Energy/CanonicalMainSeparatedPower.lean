module

public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianColumns

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
@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
open CenteredMomentFrozenSourceContext

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
set_option maxHeartbeats 600000 in
theorem actual_main_separated_power
    (cfg : CanonicalEnergyWindow α)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    WithGaussianConstants M fun n T dc Cc J Sp Sf Cm Ce Cd Ct η₀ Q Kc Z₀ =>
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    AcrossCanonicalBands cfg M H hH Z η₀ Q fun εchild C₀ C₁ =>
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),WithSlotBounds cfg.Lslot cfg.lo cfg.hi w σ freq height mesh <|
    ForCanonicalRaySources cfg M H hH η₀ θ w σ freq Z fun src =>
    ForFrozenSources src fun C D R0 E B τ t =>
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → cfg.a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    WithSeededProfile src w cfg.a cfg.b cfg.L cfg.κ cfg.Mcap Z K sigma Bseed fun seed p Mdecl Mwidth θclip =>
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a →
    WithGaussianColumns input (R0*C) seed fun _ _ _ _ _ =>
    AtGaussianScale input Z fun r =>
    let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+cfg.degree+4*n);
    let Hweights:=coefficients cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) (mass src) Sp p J
      (internalQ Q η₀) Kc t εsrc (seed.absNorm:ℝ)
      (fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase t
        (CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a) (seed.absNorm:ℝ)
        (dc+cfg.degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,Hweights j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    CenteredMomentEnergyCanonicalMainUniform.actual_main_uniform_child (α:=α) M H hH cfg Bcap Bcap
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_seeded_gaussian_power (κ := Finset α) (fun T => ↥T)
      (fun _ i => i.val) ∅ cfg.a cfg.b cfg.haPlain cfg.hbPlain cfg.lows cfg.highs cfg.hhighs
      CenteredMomentFirstAmplificationChoice.ballProfile (dc+cfg.degree+4*n) (dc+cfg.degree+4*n)
      cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) cfg.hupper (le_max_left _ _) (le_max_left _ _)
      εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Zm,hZm,hm⟩:=hmain η₀
  obtain ⟨Kc,hKc,hevent⟩:=hgauss (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Zg,hZg⟩:=Filter.eventually_atTop.1 hevent
  let Zi := max Zm Zg
  have hZi : 1<Zi := hZm.trans_le (le_max_left _ _)
  let Zw:=CenteredMomentEnergyAmplifiedChildWidth.threshold cfg.N cfg.upper sigma cfg.hupper hsigma
  refine ⟨Kc,hKc,max Zi Zw,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  let input:=child src C R0 B τ t
  let Km:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hZiZ : Zi≤Z := (le_max_left _ _).trans hZ
  have hZw : Zw≤Z := (le_max_right _ _).trans hZ
  have hZmZ:=(le_max_left _ _).trans hZiZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZiZ)
  have hz:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤src.P i.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤cfg.N:=
    (child_card B.val).trans hcard
  have hlowerBeta := gaussian_lower_support cfg input p hcardInput hlowerSrc hp₁ hp₂ asource hsourceLower (R0*C) seed
  have hsource:=hgZ.2 (CenteredMomentCommonProfile.liveIndices B.val) input p
    (fun i=>hloSrc i.val) (fun i=>hhiSrc i.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max (child_mass src C R0 B τ t)
    (R0*C) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input (R0*C) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 r hr1 hr2 hr3 hr4
  let Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+cfg.degree+4*n) Z
      ((Bcap+Bcap)*cfg.εmask+(εchild+cfg.εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+cfg.θsource)/6+θclip/3)+cfg.κ*mesh))
  have hEc:0≤Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+cfg.degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hz1 : input.W₁ 0 = 0 := by change src.W₁ 0 = 0; simpa only [hp₁] using profile_at_zero p cfg.haPlain 0
  have hz2 : input.W₂ 0 = 0 := by change src.W₂ 0 = 0; simpa only [hp₂] using profile_at_zero p cfg.haPlain 1
  refine (hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ))
    (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
    Ec Ec hEc hEc ?left ?right r hr1 hr2 hr3 hr4).trans ?coeff
  case coeff =>
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
        (p.control T)^2*(1+height)^(dc+cfg.degree+4*n)
    let paid:=cfg.paidLoss Bcap εchild delta reserve θclip mesh
    have hz : 0<Z := zero_lt_one.trans hgZ.1
    have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
    have hloProd:=CenteredMomentEnergyOriginalProfileControl.lower_product
      (child src C R0 B τ t) cfg.N cfg.lower cfg.hlower ((live_card_le B.val).trans hcard)
      (fun i=>hlowerSrc.trans (src.lower_le i.val))
    have hlo:CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a≤
        (∏i,(child src C R0 B τ t).lo i)*cfg.a*cfg.a:=by
      unfold CenteredMomentSecondInputCapacitySource.lowerFactor
      simpa only [pow_two, mul_assoc] using
        mul_le_mul_of_nonneg_right hloProd (sq_nonneg cfg.a)
    have hcoef:=CenteredMomentEnergyFirstGaussianCoefficients.main_coefficients
      cfg.N cfg.upper (max 1 cfg.b) (max 1 cfg.b) (mass src) Sp p J (internalQ Q η₀) Kc
      Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving
      Km
      t (τ.modulus.absNorm:ℝ) cost Ebase (sigma/3)
      (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
      (∏i,(child src C R0 B τ t).lo i) cfg.a
      (CenteredMomentSecondInputCapacitySource.lowerFactor cfg.N cfg.lower cfg.a) (seed.absNorm:ℝ)
      (dc+cfg.degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans cfg.hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
      (by unfold Km mainCommonRadius;positivity)
      (CenteredMomentSecondInputCapacitySource.lowerFactor_pos cfg.N cfg.lower cfg.a cfg.hlower cfg.haPlain) hlo
    have hexp:
        (Bcap+Bcap)*cfg.εmask+(εchild+cfg.εremove+
          (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+cfg.θsource)/6+θclip/3)+cfg.κ*mesh)=
        sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
      dsimp [paid];ring
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    have hh:=mul_le_mul_of_nonneg_right (hcoef j)
      (Real.rpow_nonneg (volume_pos (child src C R0 B τ t)).le (powers εsrc j))
    have htime : input.t = t := rfl
    simpa only [htime, Km, Ec,CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hg:=actual_common_gates input (R0*C) seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
    have hη:(src.η.modulus.absNorm:ℝ)≤Z^(Real.logb Z (src.η.modulus.absNorm:ℝ)):=by
      rw [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz)
        (norm_pos src.η.modulus src.η.modulus_ne_bot)]
    have hh:=CenteredMomentEnergyAmplifiedChildWidth.main_child_width cfg.N cfg.upper sigma cfg.hupper hsigma
      Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod K delta reserve ξ
      (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
      (activeSource _ _) _ q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
      _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
    have hwidth := hh.le.trans hdrop
    exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
        w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
        hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
        K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
        _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
        hlowerBeta hphysical (family q U) (hfamily q U) χ hwidth
        _ (R0*C) (by first | exact Or.inl rfl | exact Or.inr rfl) hready.puncture_ne hready.puncture_cap
        (by first | exact hg.2.2.2.2.2.1.trans hready.source_cap
                  | exact hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
        hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
end SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower

end

end OAI
