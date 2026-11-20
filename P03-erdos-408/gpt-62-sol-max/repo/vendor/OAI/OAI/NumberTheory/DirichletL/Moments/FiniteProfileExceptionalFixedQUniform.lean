module

public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQPair

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentSmooth CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondExceptionalKernel
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving ConcretePrimeRowBridge CenteredMomentMobiusRegroup
open CenteredMomentSupportedCorrelation CenteredMomentSupport CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondDivisorSupport
open scoped Classical BigOperators SchwartzMap
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
open CenteredMomentSecondDyadicRowSupport ConcretePrimeRowBridge CenteredMomentMobiusRegroup
open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical ConcretePrimeRowBridge
open CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation CenteredMomentSupport
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

abbrev WithFixedExceptionalRows (s : Input ι) (C D R0 seed Q : Ideal O) (Z B : ℝ)
    (P : Finset (CommonIndex C D) → O → Finset (Ideal O) → (Ideal O → ℂ) → ℝ →
      (RayCharacter → Character) → Finset O → RayCharacter → O → Prop) : Prop :=
    ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) → P U A S β r τ rows χ₀ m

set_option maxHeartbeats 600000 in
theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → WithFixedExceptionalRows s C D R0 seed Q Z B fun U A S β r τ rows χ₀ m =>
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W 1 (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  let rows' := dyadicRows rows n
  have hsub : rows' ⊆ rows := dyadicRows_subset rows n
  have hn' := dyadicRows_nonzero rows n
  have hex' z (hz : z ∈ rows') := hex z (hsub hz)
  let M := Real.logb Z (dyadicScale (n 1))
  have hN z (hz : z ∈ rows') : (Ideal.absNorm (Ideal.span {z}):ℝ)≤1*Z^M := by
    simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hrK:0<rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  let budget := sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 M
  have hnorm : (1+rK)^1*‖normalizedBlock s.η s.t S β C D hC hD U R rows' W Kphys n‖≤Ck*budget := by
    apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows'
      (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
      (fun z=>Real.log (normValue z/dyadicScale (n 1)))
      (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/dyadicScale (n 2)))
      (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/dyadicScale (n 3))) Q m χ₀ hQ72 hml hm2 hex'
      (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 M)
      (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r 1 M hK.le (zero_lt_one.trans hZ.1).le zero_le_one)
    intro χ ξ _ _ w
    have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
      hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
      (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
      (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
      rows' hn' (fun z hz=>hex₁ χ z (hsub hz)) (fun z hz=>hex₂ (ξ⁻¹) z (hsub hz))
      (fun z hz=>hcond₁ χ z (hsub hz)) (fun z hz=>hcond₂ (ξ⁻¹) z (hsub hz))
      s.η χ₀ U hη m hm hml hm2 hex' 1 M zero_le_one hN
      (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
      ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
        (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
      (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
    change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w (dyadicScale (n 2)) (dyadicScale (n 3))
      (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows'≤_
    rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w (dyadicScale (n 2)) (dyadicScale (n 3)) H _ rows' hβ]
    exact hp
  have hp : ‖F‖≤outerScalar C D Kphys n*normalizer C D U*(Ck*budget)/(1+rK) := by
    dsimp only [F]
    rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
    have ho : 0≤outerScalar C D Kphys n := by unfold outerScalar; positivity
    have hno := (normalizer_pos C D hC U).le
    rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows' hn' W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
    apply (le_div_iff₀ (by linarith : 0<1+rK)).mpr
    convert mul_le_mul_of_nonneg_left hnorm (mul_nonneg ho hno) using 1 <;> ring
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  apply (div_le_div_of_nonneg_right hp (volume_pos s.toData).le).trans
  have hsave := mul_le_mul_of_nonneg_left hs hCk
  refine (le_of_eq ?_).trans (hsave.trans ?_)
  · dsimp only [budget,M]; ring
  · have hc:1≤(C.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
    have hd:1≤(D.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
    have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
    let B₀:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
      (Ideal.absNorm (commonRadical C D):ℝ)
    have hB₀:0≤B₀:=by
      have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
      have hv:0≤volume s.toData:=(volume_pos s.toData).le
      dsimp only [B₀]
      positivity
    calc
      _=B₀*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
        ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
        dsimp only [B₀];ring
      _≤B₀*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hB₀
      _=_:=by dsimp only [B₀];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
