module

public import OAI.NumberTheory.DirichletL.Energy.ZeroBalancedDictionary
public import OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentEnergyZeroBalancedAdmission
open CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyReferenceState
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "inp"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem four_upper_scales (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    (inp).X₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).X₂≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₂≤Z^(max Mcap (2*Lgoal)) := by
  have hLg:Lgoal≤max Mcap (2*Lgoal):=by linarith [le_max_right Mcap (2*Lgoal)]
  have hp:0<Z:=zero_lt_one.trans hZ
  have hquarter:0≤s.width/4:=div_nonneg s.width_nonneg (by norm_num)
  have hY₁:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le hquarter
  refine ⟨hc₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),
    hc₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),?_,?_⟩
  · change Z^(s.width/4)≤_
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    grind
  · change X₁*X₂/comparisonFirst Z s.width≤_
    calc
      _≤X₁*X₂:=div_le_self (by positivity) hY₁
      _≤Z^Lgoal*Z^Lgoal:=mul_le_mul hc₁ hc₂ hX₂.le (by positivity)
      _=Z^(2*Lgoal):=by rw [←Real.rpow_add hp];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by simp)

end SevenEighths.CenteredMomentEnergyZeroBalancedAdmission

end

end OAI
