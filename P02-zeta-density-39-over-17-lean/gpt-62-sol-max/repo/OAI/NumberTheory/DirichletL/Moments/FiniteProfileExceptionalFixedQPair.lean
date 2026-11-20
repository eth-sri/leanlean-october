module
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalWindow
public import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricCanonical
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowHeight
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonHeight
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSymmetry
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight
public import OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost CenteredMomentExceptionalSourceShell CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows ConcretePrimeRowBridge
open CenteredMomentSecondExceptionalCount CenteredMomentCommonAllocationSum CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource CenteredMomentFixedQForcingCount CenteredMomentRankinRadical

local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
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
  obtain ⟨K₀,hK₀,hbound⟩:=hJ Q hQ
  let qcost:ℝ:=(Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)
  have hqcost:0<qcost:=by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero Q Q))
  let K := K₀*qcost
  have hK : 0<K := mul_pos hK₀ hqcost
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hc := actual_canonical_exceptional_count_fixedQ η₀ χ₀ C D hC U Q hQ hQtop hQ72 hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  let left := withHeight s τ₁ s.t
  let right := withHeight s (reflected τ₂) s.t
  let count := 768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)
  let f := (M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6
  let e := 2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0
  let pow := ((C.absNorm:ℝ)*D.absNorm)^θ
  let amp := frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)
  have hamp : 0 ≤ amp := div_nonneg (mul_nonneg (frozenProfile_nonneg _) (frozenProfile_nonneg _)) (by positivity)
  let G := K*count*Z^(f+e)*pow*amp
  have hG : 0 ≤ G := by dsimp [G,count,pow]; positivity
  let μ := mass Sprofile left right p p s.t s.t w (-w) J
  have hh := whole_window_pair left right C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    τ₁ (reflected τ₂) s.t s.t w (-w) X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (G*μ) (mul_nonneg hG (mass_nonneg Sprofile left right p p s.t s.t w (-w) J)) (by
      intro u v
      let s₁ := withHeight left τ₁ (s.t+2*Real.pi*(u-w))
      let s₂ := withHeight right (reflected τ₂) (s.t+2*Real.pi*(v-(-w)))
      have hb := hZ.2 s₁ s₂ p p hlo hhi hlo hhi hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
        hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ Ds hDs
      let pm := profileMass Sprofile s₁.toData s₂.toData p p J
      have hpm : 0 ≤ pm := profileMass_nonneg Sprofile _ _ _ _ _
      have hm := shifted_mass Sprofile left right τ₁ (reflected τ₂) p p s.t s.t w (-w) u v J
      apply hb.trans
      rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap]
      calc
        _ = K₀*(rows.card:ℝ)*Z^e*pow*(pm*amp) := by
          dsimp only [s₁,s₂,left,right,frozenProfile,withHeight,pm,e,pow,amp]
          ring
        _ ≤ K₀*(qcost*(count*Z^f))*Z^e*pow*(pm*amp) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hpm hamp)
          apply mul_le_mul_of_nonneg_right _ (by dsimp [pow]; positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hc hK₀.le
        _ = G*pm := by
          dsimp only [G,K]
          rw [Real.rpow_add hz f e]
          ring
        _ ≤ G*(μ*(1+‖u‖)^J*(1+‖v‖)^J) := mul_le_mul_of_nonneg_left hm hG
        _ = _ := by ring)
  simp only [left,right,window_withHeight] at hh
  let Int := ∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hh (volume_pos s.toData).le).trans
  let F := volume s.toData*G*Int^2
  have hF : 0 ≤ F := by unfold F; positivity [volume_pos s.toData]
  have hm := mass_phase Sprofile s s p p w J
  calc
    _ = F*mass Sprofile s s p p s.t s.t w (-w) J := by
      dsimp only [F,μ,Int,left,right,frozenProfile,withHeight,CenteredMomentFiniteProfileExceptionalCommon.mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _ ≤ F*((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*(1+‖w‖)^(2*J)) :=
      mul_le_mul_of_nonneg_left hm hF
    _ = _ := by dsimp only [F,G,Int,f,e,pow,amp,count]; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
