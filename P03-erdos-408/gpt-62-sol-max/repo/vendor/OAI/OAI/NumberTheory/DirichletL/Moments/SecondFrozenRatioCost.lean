module

public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
public import OAI.NumberTheory.DirichletL.Moments.SecondRetainedRatioScalar
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
public import OAI.NumberTheory.DirichletL.Moments.CommonLiveHeight
public import OAI.NumberTheory.DirichletL.Moments.SecondOriginalChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondFrozenRatioCost
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns
open CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound
open CenteredMomentSourceLiveColumn
open CenteredMomentSecondDivisorSupport CenteredMomentSourceRow Filter CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum
open CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren
open CenteredMomentSecondSupportedChildren CenteredMomentSourceLiveColumn
open CenteredMomentSecondNonexceptionalPhysical CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondDyadicRowSupport
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalCommonHarmonic

open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedRatioScalar

theorem actual_canonical_child_ratio_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃Ck:ℝ,0<Ck ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨Ce,hCe,hsource⟩ := CenteredMomentCommonLiveHeight.actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩ := actual_block_from_supported_envelopes W 1 J₁ J₂ B δ hB hδ
  have hfixed : 0 < (fixedFactor : ℝ) := Nat.cast_pos.mpr fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  let E:=childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)
  have hdyad:0<dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤E:=by unfold E childEnvelope;positivity
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=by
    intro I hi
    exact (original_column_norm s R0 seed I hz1 hz2 hi).2
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤Z^B:=by
    have hDN:1≤(D.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
    exact (div_le_self hH0 hDN).trans hH
  have hrows:∀z∈dyadicRows rows n,nonexceptional s.η χ₀ Q m A z:=by
    intro z hz
    have hh:=Finset.mem_filter.mp ((dyadicRows_subset rows n) hz)
    simpa only [rows,partRows,Bool.false_eq_true,ite_false] using hh.2
  have hmajor:∀z∈dyadicRows rows n,1≤(ballProfile (normValue z/dyadicScale (n 1))).re:=by
    intro z hz
    have hb:=ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z
      (dyadicRows_norm rows n z hz).2.le
    simpa only [normValue_eq_embedding] using hb
  let r := retainedRatio n
  have hr : 0 < r := div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  let F₁ := E₁*E
  let F₂ := E₂*E
  have hF₁ : 0 ≤ F₁ := mul_nonneg hE₁ hE
  have hF₂ : 0 ≤ F₂ := mul_nonneg hE₂ hE
  have hcore (G : Ideal O) (F : ℝ) (hF : 0 ≤ F) : 0 ≤ core s G Ce Z δ F := by
    have hprod := Finset.prod_nonneg (fun i (_ : i ∈ Finset.univ) => (s.P_pos i).le)
    have hx := s.X₁_pos.le
    have hy := s.X₂_pos.le
    unfold core
    positivity
  have hk := hZ.2 r hr s.η τ s.t S β C D hC hD hCD U hf.height_eq (sourceRadius s) hβ hHD
    R (dyadicRows rows n) (fun _ => Real.log (secondEffectiveScale C D A Kphys / dyadicScale (n 0)))
    (fun z => Real.log (normValue z / dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    Q m χ₀ hQ hml hm2 hrows ballProfile (dyadicScale (n 1)) (dyadicScale_pos _)
    (fun _ => ballProfile_nonneg _) hmajor (core s C Ce Z δ F₁) (core s D Ce Z δ F₂)
    (hcore C F₁ hF₁) (hcore D F₂ hF₂)
    (by
      intro L hL hcap hsf χ v
      have hh := hsource s hlo hhi
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun _ => ballProfile_nonneg _)) C hC R0 seed L hsC hsf
        F₁ Z hF₁ hZ.1 hNC (hcap.trans hHD) J₁ (τ χ) v (by
          intro b hlive a ha
          rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
          simpa only [F₁,E,mul_assoc] using hleft L hL hcap hsf χ v b hlive a ha)
      simpa only [envelope_eq_core,sourceRadial] using hh)
    (by
      intro L hL hcap hsf χ v
      have hh := hsource s hlo hhi
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun _ => ballProfile_nonneg _)) D hD R0 seed L hsD hsf
        F₂ Z hF₂ hZ.1 hND (hcap.trans hHD) J₂ (τ χ) v (by
          intro b hlive a ha
          rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
          simpa only [F₂,E,mul_assoc] using hright L hL hcap hsf χ v b hlive a ha)
      simpa only [envelope_eq_core,sourceRadial] using hh)
  change (1+r)^1*‖normalizedBlock s.η s.t S β C D hC hD U R (dyadicRows rows n) W Kphys n‖ ≤ _ at hk
  rw [paired_core_budget s C D hC hD Ce Z δ F₁ F₂ s.t hCe.le hz.le hF₁ hF₂ J₁ J₂] at hk
  have hh : ‖physicalBlock s.η s.t S β C D hC hD U R (dyadicRows rows n) W Kphys n‖ / volume s.toData ≤
      (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
        Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (F₁*F₂)*
        heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^1 := by
    have ho : 0 ≤ outerScalar C D Kphys n := by unfold outerScalar; positivity
    have hno := (normalizer_pos C D hC U).le
    rw [physicalBlock_eq s.η s.t S β C D hC hD U R (dyadicRows rows n) (fun z hz0 => (hrows z hz0).1)
        W Kphys hKphys n, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ho, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hno]
    apply (div_le_iff₀ (volume_pos s.toData)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos (by linarith) _)).mpr
    rw [show 2*δ=δ+δ by ring, Real.rpow_add hz]
    convert mul_le_mul_of_nonneg_left hk (mul_nonneg ho hno) using 1 <;> ring
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  rw [←physicalBlock_dyadic_rows, pow_one] at hh
  dsimp only [F₁, F₂, r] at hh
  rw [hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar_ratio s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero ((1:ℝ)/6) (by norm_num) (by norm_num)
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert hsc using 1 <;> dsimp only [F,E,retainedRatio] <;> ring

end SevenEighths.CenteredMomentSecondFrozenRatioCost

end

end OAI
