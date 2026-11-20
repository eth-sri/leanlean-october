module
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQPair
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost CenteredMomentExceptionalSourceShell CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalPairBound CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization CenteredMomentSecondDyadicRowSupport CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical CenteredMomentSecondExceptionalCommonSaving ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport

local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
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
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
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
  let sub := dyadicRows rows n
  have hsub : sub ⊆ rows := fun _ hz => dyadicRows_subset rows n hz
  have hsubn : ∀ z ∈ sub, z ≠ 0 := dyadicRows_nonzero rows n
  let X := dyadicScale (n 2)
  let Y := dyadicScale (n 3)
  let M := Real.logb Z (dyadicScale (n 1))
  let rK := dyadicScale (n 0)*dyadicScale (n 1)/(X*Y)
  have hrK : 0 < rK := div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hd : 0 < 1+rK := by positivity
  have hN : ∀ z ∈ sub, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ 1*Z^M := by
    intro z hz
    simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz
  let budget := sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 M
  have hb : (1+rK)^1*‖normalizedBlock s.η s.t S β C D hC hD U R sub W Kphys n‖ ≤ Ck*budget := by
    apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R sub
      (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
      (fun z=>Real.log (normValue z/dyadicScale (n 1)))
      (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
      (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y))
      Q m χ₀ hQ72 hml hm2 (fun z hz=>hex z (hsub hz)) budget
      (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r 1 M hK.le (zero_lt_one.trans hZ.1).le (by norm_num))
    intro χ ξ _ _ w
    have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
      hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
      (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
      (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
      sub hsubn (fun z hz=>hex₁ χ z (hsub hz)) (fun z hz=>hex₂ (ξ⁻¹) z (hsub hz))
      (fun z hz=>hcond₁ χ z (hsub hz)) (fun z hz=>hcond₂ (ξ⁻¹) z (hsub hz))
      s.η χ₀ U hη m hm hml hm2 (fun z hz => hex z (hsub hz)) 1 M (by norm_num) hN X Y (dyadicScale_pos _) (dyadicScale_pos _)
      ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
        (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
      (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
    change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
      (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) sub≤_
    rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ sub hβ]
    exact hp

  have hp' : ‖F‖ ≤ outerScalar C D Kphys n*normalizer C D U*(Ck*budget)/(1+rK) := by
    dsimp only [F]
    rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
    have ho : 0 ≤ outerScalar C D Kphys n := by unfold outerScalar; positivity
    have hno := (normalizer_pos C D hC U).le
    rw [physicalBlock_eq s.η s.t S β C D hC hD U R sub hsubn W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mpr (by simpa only [pow_one,mul_comm] using hb))
      (mul_nonneg ho hno)
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  have hsave := (div_le_div_of_nonneg_right hp' (volume_pos s.toData).le).trans
    (show (outerScalar C D Kphys n*normalizer C D U*(Ck*budget)/(1+rK))/volume s.toData ≤ _ from
      (show _ = Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*budget/(1+rK)) by ring).trans_le
        (mul_le_mul_of_nonneg_left hs hCk))
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hweight:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let G:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hG:0≤G:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [G]
    positivity
  apply hsave.trans
  calc
    _=G*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [G];ring
    _≤G*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hweight hG
    _=_:=by dsimp only [G];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
