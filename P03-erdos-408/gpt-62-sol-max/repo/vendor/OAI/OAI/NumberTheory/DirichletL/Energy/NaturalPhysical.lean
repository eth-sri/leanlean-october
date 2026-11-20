module

public import OAI.NumberTheory.DirichletL.Energy.CanonicalPhysical
public import OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission
public import OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters

public import OAI.NumberTheory.DirichletL.Energy.PhysicalRegime

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentEnergyState
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentEnergyNaturalLowSourceBound
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
open CenteredMomentAllocatedRayDictionary (Matches)
open CenteredMomentEnergyCanonicalSourceColumn (WidthAdmissible)
open CenteredMomentEnergyPhysicalRegime
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_natural_physical (high : Bool)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    let L := if high then max Lgoal Mparent else 2*max Lgoal Mparent+reserve Mglobal B ε/4
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ForSmallInternalConductors M fun η₀ Q =>
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalAt (α:=α) M H hH high W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  intro L
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0<lp:=by positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLbase:0≤max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤L:=by dsimp only [L]; split <;> positivity
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalPhysical.actual_physical (α:=α)
    M H hH ⟨W, aslot, bslot, Mchild, Lslot, (r/4), lo, hi, κ,
      a, b, Mslot, (maskEpsilon Mglobal B ε), (zero_le_one.trans hMslot), hem, ha, hb,
      L, hLphys, degree, S, haslot, hWs, hW, hMc, hLs, hr, hκsmall, hbeta, hκbeta,
      N, aslot, (max 1 bslot), a0, (r/4), haslot, (le_max_left _ _), ha0, hr, (fun _=>aslot),
      (fun _=>bslot), (fun _=>hbslot)⟩
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp high
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0<max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  dsimp only
  intro hfour
  let inp:=regimeInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ high
  have hN:Fintype.card T≤N:=Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hm : Matches M H hH inp η₀ θ w σ freq W bslot Z := by
    cases high <;> constructor <;> intros <;> rfl
  have hu : inp.X₁≤Z^L ∧ inp.X₂≤Z^L ∧ inp.Y₁≤Z^L ∧ inp.Y₂≤Z^L := by
    have hs : state.width≤max Lgoal Mparent := hstate.trans (le_max_right _ _)
    cases high
    · have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
        hw hκsmall hs hcapacity
      have hg:max Lgoal Mparent≤L:=by dsimp [L]; linarith
      have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le hg
      exact ⟨hu.2.2.2.2.1.trans hp,hu.2.2.2.2.2.1.trans hp,
        hu.2.2.2.2.2.2.1,hu.2.2.2.2.2.2.2⟩
    · exact four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
        hZ hw hκ hcapacity hs
  have hp:lp≤(∏i,inp.lo i)*a*a:=by
    have hp:=lower_product inp N aslot haslot hN (fun i => by cases high <;> exact le_rfl)
    dsimp only [lp]
    gcongr
  have hadm : WidthAdmissible high inp Z state.width state.width := by
    cases high
    · exact (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
    · exact ⟨le_rfl,hfour⟩
  have hhi : ∀ i, inp.hi i ≤ bslot := fun i => by cases high <;> exact le_rfl
  have hMs : ∀ i, inp.M i ≤ Mslot := fun i => by cases high <;> exact le_rfl
  have hlo : ∀ i, inp.lo i = aslot := fun i => by cases high <;> rfl
  have hhi' : ∀ i, inp.hi i = bslot := fun i => by cases high <;> rfl
  have hL' : aslot ≤ inp.lower := by cases high <;> exact le_rfl
  have hU' : inp.upper ≤ max 1 bslot := by cases high <;> exact le_max_right _ _
  have hb₁ : 0≤ inp.b₁ := by cases high <;> exact hb
  have hb₂ : 0≤ inp.b₂ := by cases high <;> exact hb
  have hb₁' : inp.b₁≤max 1 b := by cases high <;> exact le_max_right _ _
  have hb₂' : inp.b₂≤max 1 b := by cases high <;> exact le_max_right _ _
  have hw₁ : p.profile 0 = inp.W₁ := by cases high <;> rfl
  have hw₂ : p.profile 1 = inp.W₂ := by cases high <;> rfl
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm hhi hMs hlo hhi' hN hL' hU'
    hb₁ hb₂ hb₁' hb₂' hp state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p hw₁ hw₂
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) (by cases high <;> exact hcapacity)
    (by cases high <;> exact hwidth) (by cases high <;> exact hwidth) (by linarith only [hstate,hdrop])
    hclip (by cases high <;> exact le_rfl) hadm (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=by cases high <;> rfl
  rw [ht] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyNaturalPhysical

end

end OAI
