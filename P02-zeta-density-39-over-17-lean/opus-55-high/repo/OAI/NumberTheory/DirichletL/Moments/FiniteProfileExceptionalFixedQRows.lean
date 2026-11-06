module
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentReflectedSource
open CenteredMomentHeckeColumnWindow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open RayFourExpansion
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge
open CenteredMomentSecondCanonicalScalar
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D *nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z ^r≤ s.X₁ → Z ^r≤ s.X₂ → Z ^r≤ s.Y₁ → Z ^r≤ s.Y₂ →
      ∀τ:RayCharacter→ Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z ^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z ^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z ^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z ^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  pm_988 actual_original_exceptional_block
  pm_2917
  pm_2985
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  pm_5485 hrK rK
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  pm_6123 rK s.η s.t
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  pm_6256
  pm_5206 s.η s.t hn
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
