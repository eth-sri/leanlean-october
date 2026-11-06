module
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceSeededPowerDescent
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenUniformSubset
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalLiveSource
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns
open CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum
open CenteredMomentHeckeColumnWindow
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalChildEnergy
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open MeasureTheory

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z ^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z ^B →
      (s.η.modulus.absNorm:ℝ)≤Z ^B → (R0.absNorm:ℝ)≤Z ^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→ Finset (CommonIndex q.val.1 q.val.2)→ RayCharacter→ Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z ^B → Tsec≤Z ^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z ^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→ Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→ Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z ^r≤ s.X₁ → Z ^r≤ s.X₂ → Z ^r≤ s.Y₁ → Z ^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s ^2 := by
  pm_2931 CenteredMomentSecondFrozenUniformSubset.original_subsets_source_descent
  pm_2929
  pm_2930
  pm_2932 i.val

end SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent

end

end OAI
