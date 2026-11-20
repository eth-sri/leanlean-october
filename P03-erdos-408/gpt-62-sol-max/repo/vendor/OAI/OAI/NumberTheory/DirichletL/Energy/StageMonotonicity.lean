module

public import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound
public import OAI.NumberTheory.DirichletL.Energy.ZeroGrowth

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyStageMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentEnergyZeroGrowth
local notation "O"=>HeckeFamily.O

theorem zeroLowAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroLowAt Q a b radial mask L Mcap eps Z J S C):
    ZeroLowAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hlow
  have hcap:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hlow
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  exact hh.trans (energy_bound_mono p hZ (by linarith [norm_nonneg t])
    (diagonalControl_nonneg _) hC hCC hS hJ he)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveLowAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveLowAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveLowAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  have hcap:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlow
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  exact hh.trans (energy_bound_mono p hZ (by linarith [abs_nonneg t])
    (diagonalControl_nonneg _) hC hCC hS hJ he)

omit [Fintype α] [DecidableEq α] in
theorem positiveHighAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi rho Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' rho' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(hrho:rho≤rho')(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveHighAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi rho Mcap eps κ Z η₀ Q J S C):
    PositiveHighAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi rho' Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hcap:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hrho.trans hwidthLo) (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlarge
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  exact hh.trans (energy_bound_mono p hZ (by linarith [abs_nonneg t])
    (diagonalControl_nonneg _) hC hCC hS hJ he)

end SevenEighths.CenteredMomentEnergyStageMonotonicity

end

end OAI
