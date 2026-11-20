module

public import OAI.FiniteMajorant

public import OAI.NumberTheory.DirichletL.Energy.NaturalLowSourceBound
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
public import OAI.NumberTheory.DirichletL.Energy.LowBandEmpty

public import OAI.NumberTheory.DirichletL.Energy.PhysicalRegime

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentEnergyPhysicalRegime
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical:ℝ),
      1/6≤κ→0≤Cphysical→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1))→
      PhysicalAt (α:=α) M H hH false W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)):=by
  have hfixed (T:Finset α):=natural_low_source_bound (ι:=T) W hW aslot bslot lo hi
    a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ hMcap hεdiag hξ
  choose Ψ hΨs hΨn Cj hCj hbound using hfixed
  obtain ⟨Cfixed, hCfixed, hCC⟩ := exists_real_majorant 0 Cj
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical hκ hCphysical he hsave hold hmass
  have hpositive:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cphysical+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidth
      p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    by_cases hsmall:state.width≤ rho
    · exact hold T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        state hQ hsmall p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
    have hp:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      state hQ (le_of_not_ge hsmall) hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow trivial
    have hh:=(hZ T).2 M H hH η₀ θ w σ freq hw (fun i=>⟨hσlo i,hσhi i⟩)
      Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ (hcapacity.trans hwidth)
      S J Cphysical height e hCphysical hheight he hsave hp
    have hc:=hCC T
    have hd:=diagonalControl_nonneg state.radial.profile
    apply hh.trans
    gcongr
  exact ⟨hpositive,CenteredMomentEnergyLowBandEmpty.positive_low_zero (α:=α) M H hH
    W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J (insert (0,0) S)
    (Cfixed*(Cphysical+1)) hpositive⟩

end SevenEighths.CenteredMomentEnergyPositiveLowBandSource

end

end OAI
