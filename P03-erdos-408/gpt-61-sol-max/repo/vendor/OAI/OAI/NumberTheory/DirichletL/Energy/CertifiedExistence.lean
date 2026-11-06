module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor
public import OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistence
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCappedAnalyticSuccessor CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

section
variable (W : ℝ→ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (haslot : 0<aslot) (hWs : Function.support W⊆Set.Icc aslot bslot) (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hrad : 2≤radial) (_hrad : 0<radial) (hmask : 0≤Bmask) (hMcap : 0<Mcap) (hκ0 : (3/4:ℝ)≤κ) (hε : 0<ε) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)


include haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ in
theorem certified_bands   
       
         
        
      :
    ∀k:ℕ,k≤count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k<count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious

include haslot hWs hW hbslot ha haUpper hb _hrad hmask hMcap hκ0 hε hbeta hκ in
theorem terminal_certificate   
       
         
        
      :
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=OAI.SevenEighths.CenteredMomentEnergyCappedRadialTransport.certified_from_max_two M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.count Mcap ε) (OAI.SevenEighths.CenteredMomentEnergyCertifiedExistence.certified_bands M H hH W aslot bslot a b (Max.max 2 radial) Bmask L lo hi Mcap κ ε haslot hWs hW hbslot ha haUpper hb (le_max_left 2 radial) hmask hMcap hκ0 hε hbeta hκ (OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.count Mcap ε) le_rfl)

end

end SevenEighths.CenteredMomentEnergyCertifiedExistence

end

end OAI
