module
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondBlockHarmonicMass
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma live_harmonic_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,pairWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2:= by pm_2863 CenteredMomentSecondBlockHarmonicMass.active_blocks_sum_eq pairWeight_nonneg

theorem part_energy_harmonic_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V ≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        pairWeight q.1.1.val.1 q.1.1.val.2):= by pm_2864 pairWeight live_harmonic_sum_le

theorem source_part_harmonic_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→ seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z ^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z ^L → H≤Z ^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z ^ε/(seed.absNorm:ℝ)):= by pm_2865 actual_block_harmonic_mass part_energy_harmonic_bound

end SevenEighths.CenteredMomentSecondNonexceptionalAggregate

end

end OAI
