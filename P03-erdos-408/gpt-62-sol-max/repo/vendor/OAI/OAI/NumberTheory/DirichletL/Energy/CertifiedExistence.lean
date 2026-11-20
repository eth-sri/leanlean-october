module

public import OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport
public import OAI.NumberTheory.DirichletL.Energy.CappedLowStage
public import OAI.NumberTheory.DirichletL.Energy.NaturalHighStage
public import OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage
public import OAI.NumberTheory.DirichletL.Energy.CappedSuccessorPacking
public import OAI.NumberTheory.DirichletL.Energy.CappedRequests
public import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistence
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCappedRadialTransport CenteredMomentEnergyWidthSchedule
open Filter
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighBound CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyFirstLiveAdmission
open CenteredMomentEnergyCappedRequests CenteredMomentEnergySourceCapSchedule
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(_hrad:0<radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  let R := max 2 radial
  have hrad2 : 2≤R := le_max_left _ _
  suffices ∀ k≤count Mcap ε, CertifiedBand (α:=α) M H hH W bslot a b R Bmask L lo hi Mcap κ ε k from
    this _ le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b R Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk1
    have hk : k<count Mcap ε := by omega
    have hold := ih hk.le
    let Bs:=finalSourceCap Mcap Bmask L ε
    let Mp:=bandWidth Mcap Bs ε (k+1)
    let Mc:=bandWidth Mcap Bs ε k
    let ac:=lowerAt a b Mcap ε (k+1)
    let Lc:=lengthAt Mcap Bmask L ε (k+1)
    let Lp:=lengthAt Mcap Bmask L ε k
    let Lreq:=requestLength Mcap Bmask Lc
    let A:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
    let r:=reserve Mcap Bs ε
    have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
    have hκnn:0≤κ:=by linarith
    have hr:=(bounds Mcap Bs κ ε hMcap.le hBs hκnn hε).2.2.2.1
    have hr1:r/4≤1:=by
      have hh:=bounds Mcap Bs κ ε hMcap.le hBs hκnn hε
      have hrs:r≤amplification ε/100:=min_le_left _ _
      linarith [hh.2.1]
    have hMp:0≤Mp:=bandWidth_nonneg Mcap Bs ε hMcap.le hBs hε _
    have hMc:=band_positive Mcap Bs ε hMcap hBs hε k
    have hMpM:Mp≤Mcap:=bandWidth_le _ _ _ _
    have hMcM:Mc≤Mcap:=bandWidth_le _ _ _ _
    have hac:0<ac:=lowerAt_pos a b Mcap ε ha _
    have haca:ac≤a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
    have haclo:=haca.trans haUpper
    have hLc:0≤Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
    have hLp:0≤Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
    have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask
    have hreqFinal:=
      request_le_final Mcap Bmask L ε hMcap.le hmask k hk
    have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)
    have hA:0≤A:=by dsimp [A];positivity
    have hMA:Mp≤A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)]
    have hready:=
      readyBudget_le_schedule Mcap Bmask L ε A Bmask hMcap.le hmask le_rfl le_rfl
    have hdrop:=parent_drop Mcap Bs ε hε k
    have hmesh:=
      (fineMesh_pos Mcap Bmask L κ ε hMcap.le hmask hκnn hε).le
    have hsupport:=child_support a b Mcap ε k hk
    have hrequest:=previous_admits Mcap Bmask L ε Mp (r/4)
      hMcap.le hmask hMpM hr1 k hk
    have hhighL:max Lc Mp≤Lp:=by
      have hh:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
      have hx:=le_max_left Lreq Mp
      linarith
    have href:Mp+Bmask+Mc/100≤Lreq:=by
      have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hMpM hMcM (by norm_num)
      exact (le_max_right _ _).trans hh
    obtain ⟨Jold,Sold,hprev⟩:=hold
    obtain ⟨Slow,Jlow,hlow⟩:=CenteredMomentEnergyCappedLowStage.actual_capped_low (α:=α) M H hH
      W aslot bslot a b R Bmask L lo hi Mcap κ ε hW haslot hWs hbslot ha (by linarith) hrad2
      hmask hMcap.le hκ0 hε hbeta hκ k hk ⟨Jold,Sold,hprev⟩
    obtain ⟨Uhigh,Jhigh,hhigh⟩:=CenteredMomentEnergyNaturalHighStage.actual_high_stage (α:=α) M H hH
      W hW aslot bslot lo hi ac b R haslot hWs hbslot hac haclo hb (by linarith)
      Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L κ ε) Mc κ ε k hMc hMcap.le hA hBs hmask
      hMp hMc.le hLc hmesh hMA hready hκ0 hbeta hκ hε le_rfl hdrop Jold Sold Jlow Slow
    obtain ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,hLlow,hLupper,hzeroStage⟩:=
      CenteredMomentEnergyNaturalZeroStage.actual_zero_stage (α:=α) M H hH
        W aslot bslot (fineMesh Mcap Bmask L κ ε) lo hi κ ac b R Bmask Lc Mp Mc Mcap Bs ε Mc k
        haslot hWs hW hmesh hκ0 hbeta hκ hac haclo hb hrad2 hmask hMp hMc.le hMcap.le hBs
        hε hMc le_rfl hdrop
    have hLlowReq:Llow≤Lreq:=by
      rw [hLlow,hLexact]
      exact actual_contours Mcap Bmask Lc Mp Mc d hMcap.le hMpM hMcM hd1
    have hLgrowLow:Lgrow≤Llow:=by rw [hLlow];exact le_max_left _ _
    have hzeroCap:max Mp (2*Lgrow)≤Lp:=by
      have hh:=le_max_left Lreq Mp
      apply max_le <;> linarith
    have hzeroReady:readyBudget (max Mp (2*Lgrow)) Bmask≤Bs:=by
      have hc:max Mp (2*Lgrow)≤A:=by
        apply max_le
        · exact hMA
        · dsimp [A];linarith
      apply le_trans _ hready
      unfold readyBudget
      linarith
    obtain ⟨Jzero,Uzero,hzero⟩:=hzeroStage Lp hLp hzeroCap hzeroReady Jold Jlow Sold Slow
    have hmarg:=margins Mcap Bs κ ε hMcap.le hBs hκnn hε k
    apply CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages (α:=α) M H hH
      W bslot a b R Bmask L lo hi Mcap κ ε ha hmask hMcap.le hκnn hε k
      (stageLoss Mcap Bs ε (k+1)) (physicalLoss Mcap Bs ε k) (reflectedLoss Mcap Bs ε k)
      le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 ⟨Jold,Sold,hprev⟩
    · refine ⟨Jzero,Uzero,?_⟩
      intro η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨Cz,hCz,hzeroZ⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
      refine ⟨Cz*(Clow+C₀+C₁+1),by positivity,?_⟩
      filter_upwards [hprevZ,hlowZ,hzeroZ] with Z hp hl hz
      have hzz:=hp.2.1
      have hpp:=hp.2.2
      rw [hsupport] at hzz hpp
      have hlowRestricted:=zeroLowAt_transport (internalQ Q η₀)
        ac b R Bmask Lreq Mp (physicalLoss Mcap Bs ε k) Z
        ac b R Bmask Llow Mp (physicalLoss Mcap Bs ε k) Jlow Jlow Slow Slow Clow Clow
        hp.1.le le_rfl le_rfl le_rfl le_rfl hLlowReq le_rfl le_rfl le_rfl
        (Finset.Subset.refl _) hClow.le le_rfl hl.2.2
      exact hz.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzz hpp hlowRestricted
    · refine ⟨Jlow,Slow,?_⟩
      intro η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
      refine ⟨Clow,hClow,?_⟩
      filter_upwards [hlowZ] with Z hl
      exact positiveLowAt_transport (α:=α) M H hH W bslot
        ac b R Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
        ac b R Bmask Lc Mp (physicalLoss Mcap Bs ε k) η₀ Q Jlow Jlow Slow Slow Clow Clow
        hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
        (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    · refine ⟨Jhigh,Uhigh,?_⟩
      intro η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
      obtain ⟨Ch,hCh,hhighZ⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
      refine ⟨Ch*(C₀+C₁+Clow+1),by positivity,?_⟩
      filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
      have hzz:=hp.2.1
      have hpp:=hp.2.2
      rw [hsupport] at hzz hpp
      have hzSmall:=zeroAt_transport (internalQ Q η₀)
        (ac/max 1 b) b R Bmask Lp Mc (stageLoss Mcap Bs ε k) Z
        (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k)
        Jold Jold Sold Sold C₀ C₀ hp.1.le le_rfl le_rfl hrad2 hmask hhighL le_rfl le_rfl le_rfl
        (Finset.Subset.refl _) hC₀.le le_rfl hzz
      have hpSmall:=positiveAt_transport (α:=α) M H hH W bslot
        (ac/max 1 b) b R Bmask Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k) κ Z
        (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k) η₀ Q
        Jold Jold Sold Sold C₁ C₁ hp.1.le le_rfl le_rfl hrad2 hmask hhighL le_rfl le_rfl le_rfl
        (Finset.Subset.refl _) hC₁.le le_rfl hpp
      have hlRestricted:=positiveLowAt_transport (α:=α) M H hH W bslot
        ac b R Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
        ac b R Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs ε k) η₀ Q
        Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
        (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
      exact hh.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.CenteredMomentEnergyCertifiedExistence

end

end OAI
