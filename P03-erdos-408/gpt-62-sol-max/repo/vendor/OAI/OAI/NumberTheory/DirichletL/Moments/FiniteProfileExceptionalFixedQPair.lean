module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonHeight
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic
public import OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSymmetry
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalMass
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentSmooth CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFixedQForcingCount CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_common_better_side wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  let qcost:ℝ:=(Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)
  have hqcost:0<qcost:=by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Ideal.absNorm_pos_of_ne_bot (commonRadical_ne_zero Q Q)
  refine ⟨K*qcost,mul_pos hK hqcost,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hc:=actual_canonical_exceptional_count_fixedQ η₀ χ₀ C D hC U Q hQ hQtop hQ72 hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  let e:ℝ:=2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0
  let f:ℝ:=(M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6
  let F:=(K*qcost)*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^(f+e)*((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s)) (by positivity))
  have hb := whole_window_pair s s C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    τ₁ (reflected τ₂) s.t s.t w (-w) X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (F*mass Sprofile s s p p s.t s.t w (-w) J)
    (mul_nonneg hF (mass_nonneg Sprofile s s p p s.t s.t w (-w) J)) (by
    intro u v
    let s' := withHeight s τ₁ (s.t+2*Real.pi*(u-w))
    let v' := withHeight s (reflected τ₂) (s.t+2*Real.pi*(v-(-w)))
    have hb:=hZ.2 s' v' p p hlo hhi hlo hhi hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD
      r r hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ Ds hDs
    rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
    have hmass:=shifted_mass Sprofile s s τ₁ (reflected τ₂) p p s.t s.t w (-w) u v J
    let mass' := profileMass Sprofile s'.toData v'.toData p p J
    let frozen := frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)
    let Acount := (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))
    have hmass' : 0 ≤ mass' := profileMass_nonneg Sprofile _ _ _ _ _
    have hfrozen : 0 ≤ frozen := div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s)) (by positivity)
    apply hb.trans
    calc
      _ = K*(rows.card:ℝ)*Z^e*((C.absNorm:ℝ)*D.absNorm)^θ*(mass'*frozen) := by
        dsimp only [mass',frozen,s',v',withHeight,frozenProfile,e]
        ring
      _ ≤ K*(qcost*(Acount*Z^f))*Z^e*((C.absNorm:ℝ)*D.absNorm)^θ*(mass'*frozen) := by
        gcongr
      _ = F * mass' := by
        dsimp only [F,Acount,frozen]
        rw [Real.rpow_add hz]
        ring
      _≤F*(mass Sprofile s s p p s.t s.t w (-w) J*(1+‖u‖)^J*(1+‖v‖)^J):=
        mul_le_mul_of_nonneg_left hmass hF
      _=_:=by ring)
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  let L := ∫ u:ℝ, (1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖
  have hmass := mass_phase Sprofile s s p p w J
  have hmul := mul_le_mul_of_nonneg_left hmass
    (show 0≤volume s.toData*F*L^2 from mul_nonneg (mul_nonneg (volume_pos s.toData).le hF) (sq_nonneg _))
  have heq : f+e = f+2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0 := by
    dsimp [e]
    ring
  convert hmul using 1 <;> simp only [F,L,heq] <;> dsimp [f] <;> ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
