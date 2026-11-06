module
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
public import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
public import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetricBounded
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

open CenteredMomentEnergyPositiveHighAssemblyBounded CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤e→0≤K→0≤Cmass→ e+ε≤efinal→ emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      ((Z ^(s.width/4)≤ inp.X₁ ∧ Z ^(s.width/4)≤ inp.X₂ ∧
        Z ^(s.width/4)≤ inp.Y₁ ∧ Z ^(s.width/4)≤ inp.Y₂) →
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤
          Cmass*(p.control Smass)^2*(1+|t|+height)^Jmass*Z ^(s.width+emass)) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|+height)^Jout*Z ^(s.width+efinal) :=by
  obtain ⟨d,L,hd,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hstage⟩:=
    actual_high_source_split (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  pm_211 L hL hLupper Ψ hsΨ hnΨ
  intro degree S Jmass Smass
  obtain ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,hbound⟩:=hstage degree S
  pm_557
  pm_8814 Wslot hcSlot hsSlot α
  pm_406 D Cdiag Sdiag.sup
  pm_406 T Ctail Stail.sup
  have hP:0≤P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  pm_100 hD D
  pm_100 hT T
  pm_5841
  pm_3592 hCfixed Cfixed
  pm_119 Jout U Cfixed hCfixed
  pm_168 hbound
  intro e emass efinal Lslot κ η₀ Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ s hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  pm_761 hbase
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z ^(s.width+efinal)
  pm_100 hF F
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z ^(s.width+ej)≤F:=by
    pm_6113 hSj Sj hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej≤ s.width+efinal by linarith)
    dsimp [F]
    gcongr
  pm_159
  pm_183
  pm_488 hju Ju Jout
  pm_488 hjr Jr Jout
  pm_488 hjm Jmass Jout
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced|⟨hfour,hsource⟩
  · change _≤Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z ^(s.width+e+ε) at hunbalanced
    pm_197
  · have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        CenteredMomentAmplificationChildInput.volume inp≤Cmass*F:=by
      pm_8364
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
        (Fintype.card α) le_rfl U
      pm_7225
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z ^x≤Z ^(s.width+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z ^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z ^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z ^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          calc
            _ = (c*P*A*(p.control U)^2*Z ^(s.width+efinal))*1 := by ring
            _ ≤ (c*P*A*(p.control U)^2*Z ^(s.width+efinal))*
                (1+|t|+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
            _ = c*P*A*F := by dsimp [F]; ring
    pm_144
    have hcoeff:2*Cmass+2*D +2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    pm_7807
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|+height)^Jout*Z ^(s.width+efinal)
    pm_6274
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|+height)^Jr*Z ^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|+height)^Jr*Z ^(s.width+e+ε)≤_
    pm_575

end SevenEighths.CenteredMomentEnergyPositiveHighBound

end

end OAI
