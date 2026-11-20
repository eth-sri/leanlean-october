module
public import OAI.NumberTheory.DirichletL.Energy.Bands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def widenState {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    NaturalState Z B' b':=
  {s with
    puncture_bound:=s.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hB)
    radial_support:=fun _x hx=>le_trans (s.radial_support hx) hb}

def widenProfiles {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b'):Profiles a' b' where
  profile:=p.profile
  support:=fun i _x hx=>⟨ha.trans (p.support i hx).1,(p.support i hx).2.trans hb⟩

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

/-- Increase the coefficient, seminorms, and exponents of a transported energy bound. -/
theorem energy_coefficient_mono {a b C C' D t Z w eps eps' : ℝ} {S T : Finset (ℕ × ℕ)}
    {J J' : ℕ} (p : Profiles a b) (hC : 0 ≤ C) (hCC : C ≤ C') (hD : 0 ≤ D)
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hS : S ⊆ T) (hJ : J ≤ J') (he : eps ≤ eps') :
    C*D*(p.control S)^2*t^J*Z^(w+eps) ≤ C'*D*(p.control T)^2*t^J'*Z^(w+eps') := by
  have := p.control_nonneg S
  have := p.control_nonneg T
  have := hC.trans hCC
  have := zero_le_one.trans ht
  have := profile_control_mono p hS
  have := pow_le_pow_right₀ ht hJ
  have := Real.rpow_le_rpow_of_exponent_le hZ (add_le_add_left he w)
  gcongr

theorem zeroAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b radial mask L Mcap eps Z J S C):
    ZeroAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  exact hh.trans (energy_coefficient_mono p hC hCC (diagonalControl_nonneg _) 
    (by linarith [norm_nonneg t]) hZ hS hJ he)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity
  exact hh.trans (energy_coefficient_mono p hC hCC (diagonalControl_nonneg _) 
    (by linarith [abs_nonneg t]) hZ hS hJ he)

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI
