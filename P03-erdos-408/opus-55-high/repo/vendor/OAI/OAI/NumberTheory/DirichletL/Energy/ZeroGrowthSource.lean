module

public import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthHighBound

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction
open CenteredMomentSecondHeightFamily
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

def PhysicalGrowthAt (Q:Ideal HeckeFamily.O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)

end SevenEighths.CenteredMomentEnergyZeroGrowthSource

end

end OAI
