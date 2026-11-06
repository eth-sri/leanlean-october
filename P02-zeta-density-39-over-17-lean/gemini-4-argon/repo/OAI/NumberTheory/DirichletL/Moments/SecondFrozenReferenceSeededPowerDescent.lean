module
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenSeededPowerDescent
public import OAI.NumberTheory.DirichletL.Moments.SecondReferenceNormalization
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenUniformSubset
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalLiveSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondActivePhysicalDictionary
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson CenteredMomentLogDyadic MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondReferenceNormalization CenteredMomentSecondFrozenUniformSubset

theorem original_subsets_seeded_power_descent {κ : Type*} [Fintype κ] (t₀ : κ)
    (sub : κ → Type*) [∀ T, Fintype (sub T)] [∀ T, DecidableEq (sub T)] (valOf : ∀ T, sub T → ι)
    (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : κ, ∀(s:Input (sub T))(p:Profiles wlo whi),(∀i,s.lo i=lo (valOf T i)) → (∀i,s.hi i=hi (valOf T i)) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card (sub T)≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    ChildBound₁ s R0 Q S β τ χ₀ m W Kphys Tsec Z ξ (referenceEnvelope qref) E₁ J₁ →
    ChildBound₂ s R0 Q S β τ χ₀ m W Kphys Tsec Z ξ (referenceEnvelope qref) E₂ J₂ →
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenSeededPowerDescent.original_subsets_seeded_power_descent t₀ sub valOf
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hq:0<(s.η.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ s.η.modulus_ne_bot
  have hr:0≤qref/(s.η.modulus.absNorm:ℝ):=div_nonneg hqref.le hq.le
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap
    (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂)
    (mul_nonneg hr hE₁) (mul_nonneg hr hE₂)
  have hbound:=hh
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hleft q hq U n hn D0 hD hcap hs χ v b hb a ha)
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hright q hq U n hn D0 hD hcap hs χ v b hb a ha)
    r hX1 hX2 hY1 hY2
  rw [seededFactors_rescale Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ)
      J₁ J₂ Sf W hq hqref.le] at hbound
  exact hbound
