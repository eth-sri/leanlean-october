module

public import OAI.NumberTheory.DirichletL.Energy.ZeroUnbalancedOriginalPower

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound CenteredMomentEnergyState
open CenteredMomentEnergyBands CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroUnbalancedOriginalPower
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hpos:=comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans hZ.1) hX₁ hX₂
  apply hZ.2 e Q degree K he hK hlow s hQ hslo hs p t _ _ hpos.1 hpos.2
  · rw [comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ.1) hZ.1.ne']
  · rw [comparison_second_power Z s.width X₁ X₂ hZ.1 hX₁ hX₂]
    exact Real.one_le_rpow hZ.1.le (sub_nonneg.mpr hlarge)

end SevenEighths.CenteredMomentEnergyZeroReferenceBounded

end

end OAI
