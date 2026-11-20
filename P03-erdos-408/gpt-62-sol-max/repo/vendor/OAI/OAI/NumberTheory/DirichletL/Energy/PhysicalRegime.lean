module

public import OAI.FiniteMajorant

public import OAI.NumberTheory.DirichletL.Energy.NaturalLowSourceBound
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighSource
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
public import OAI.NumberTheory.DirichletL.Energy.LowBandEmpty

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalRegime
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentCommonRadialData
open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

section Input
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

/-- Use the balanced source in the high-volume range and the small-scale
source in the low-volume range. -/
def regimeInput (high : Bool) : Input α :=
  if high then balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂
  else zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂
end Input

def PhysicalAt (high : Bool) (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤state.width→
    (if high then 5*state.width/6≤length Z X₁+length Z X₂+(∑i,w i)
      else length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6)→
    let inp:=regimeInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ high
    (if high then Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂ else True)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ / volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

end SevenEighths.CenteredMomentEnergyPhysicalRegime

end

end OAI
