module

public import OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters
public import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
public import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetricBounded
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly
public import OAI.NumberTheory.DirichletL.Energy.PositiveHighSource
public import OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
public import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
public import OAI.NumberTheory.DirichletL.Energy.ReferenceRobustBounded
public import OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
public import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource (balancedInput balanced_volume_bound)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyLiveClippingDefect
open CenteredMomentEnergyPhysicalEntry (natural_inverse_scale)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) →
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤
          Cmass*(p.control Smass)^2*(1+|t|+height)^Jmass*Z^(s.width+emass)) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|+height)^Jout*Z^(s.width+efinal) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hLuUpper,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,hLrUpper,hrstage⟩ :=
    CenteredMomentEnergyReferenceRobustBounded.reference_power
      (α:=α) M H hH true Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩ := actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving (fun _=>hbslot) ha (by linarith) hM hεdiag hξ
  obtain ⟨Z₀,_,hendpoint⟩ := endpoint_threshold b (rho/100) (by positivity)
  refine ⟨max Lu Lr, (show 0 ≤ Lu by linarith).trans (le_max_left _ _),
    max_le hLuUpper hLrUpper, Ψ, hsΨ, hnΨ, ?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩ := hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩ := hrstage degree S
  let U:=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=(profileBound Wslot hcSlot aslot bslot lo hi haslot hsSlot)^(2*Fintype.card α)
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hu, hr, hred, eventually_ge_atTop Z₀] with Z hzu hzr hredZ hZZ
  refine ⟨hzu.1,?_⟩
  intro e emass efinal Lslot κ η₀ Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hz:=zero_lt_one.trans hzu.1
  have hscale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z^(s.width+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z^(s.width+ej)≤F:=by
    have hp:=p.control_mono hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hzu.1.le (show s.width+ej≤s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by omega
  have hjr:Jr≤Jout:=by omega
  have hjm:Jmass≤Jout:=by omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) le_rfl hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤s.width/4
  · have hunbalanced := hzu.2 e Lslot κ η₀ Q K he hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hwidthLo hwidth (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
    change _≤Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z^(s.width+e+ε) at hunbalanced
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
      Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) le_rfl hK hlow
    have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hwidthLo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases energy_zero_or_defect s.character s.mask 1 t p inp.slots inp.toData.coefficient
      inp.P X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hzu.1 hX₁ hX₂ with hzero | hdft
    · rw [hzero]
      positivity
    · have hg := raw_gates_of_defect Z s.width X₁ X₂ (∑ i,w i) κ (rho/100) hzu.1 hX₁ hX₂
        (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
      have hreference := hzr.2 e Lslot κ η₀ Q K he hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
        s hQ hwidthLo hwidth (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂ hg
      have hred' := hredZ.2 inp (p.profile 0) (p.profile 1) rfl rfl
        (p.support 0) (p.support 1) (fun _=>le_rfl) s.puncture s.radial s.radial_support
        (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
          w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hzu.1 hw hκ hcap hwidth)
        (natural_inverse_scale s Mcap hM)
      have hmass := hphysical ⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩
      have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
      have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤Cmass*F:=by
        apply hmass.trans
        convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
      have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
        have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
          w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
          (Fintype.card α) le_rfl U
        have h00:(0,0)∈U:=Finset.mem_insert_self _ _
        simpa only [Finset.insert_eq_of_mem h00] using hc
      have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
      have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(s.width+efinal):=by
        rw [s.scale_eq,←Real.rpow_add hz]
        exact Real.rpow_le_rpow_of_exponent_le hzu.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
      have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤efinal):
          c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤c*P*A*F:=by
        calc
          _≤c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
          _≤c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
          _≤c*P*A*F:=by
            calc
              _ = (c*P*A*(p.control U)^2*Z^(s.width+efinal))*1 := by ring
              _ ≤ (c*P*A*(p.control U)^2*Z^(s.width+efinal))*
                  (1+|t|+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
              _ = c*P*A*F := by ring
      have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
      have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
      have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
      have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
      have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
        (show 0≤2*diagonalControl s.radial.profile by positivity)
      have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
        dsimp [Cfixed]
        nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
          mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
      have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
      change energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale ≤ _ at hreference
      have hsplit := mul_le_mul_of_nonneg_left hreference (by norm_num : (0:ℝ)≤2)
      apply hred'.trans
      change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
        (1+|t|+height)^Jout*Z^(s.width+efinal)
      dsimp [D,T,F] at hsum href hfinish
      change _≤_ at hsum
      change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
        (1+|t|+height)^Jr*Z^(s.width+(e+ε)))≤_ at href
      rw [show s.width+e+ε=s.width+(e+ε) by ring] at hsplit
      change _ ≤ 2*(Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
        (1+|t|+height)^Jr*Z^(s.width+(e+ε))) at hsplit
      exact (add_le_add hsum hsplit).trans (by nlinarith only [href, hfinish])

end SevenEighths.CenteredMomentEnergyPositiveHighBound

end

end OAI
