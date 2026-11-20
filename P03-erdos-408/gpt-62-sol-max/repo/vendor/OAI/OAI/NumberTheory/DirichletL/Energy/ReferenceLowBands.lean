module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles
public import OAI.NumberTheory.DirichletL.Energy.Bands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def ZeroLowAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂≤5*s.width/6→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

abbrev PositiveLowAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C true

end SevenEighths.CenteredMomentEnergyReferenceLowBands

end

end OAI
