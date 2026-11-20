module

public import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData
public import OAI.NumberTheory.DirichletL.Descent.CanonicalRankFamilyGates

public import OAI.NumberTheory.DirichletL.Descent.CanonicalRankDepthParameters
public import OAI.NumberTheory.DirichletL.Descent.CanonicalEnergyExistenceData
public import OAI.NumberTheory.DirichletL.Inversion.CanonicalReferenceThreshold

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase InverseTerminalWidths
open CanonicalCubeSeparation CompletedHeight InverseMomentFirstSecondHeightCost

theorem canonical_marked_energy_exists
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W := by
  obtain ⟨n,cutoff,eta,_,_,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,_,hmargin,_,hloss⟩ :=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  let L := Fcap+1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  refine canonical_energy_of_rank n L c cutoff eta Mcap Fcap c eps K W hrow hcap hmargin hloss.le ?_
  suffices ∀ n (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ), 0<lo → 0≤hi →
      Function.support (W : ℝ → ℂ) ⊆ Set.Icc lo hi → RankEnergyExists n L c cutoff eta K W from
    this n W lo hi hlo hhi hsW
  intro n
  induction n with
  | zero => intro W; exact fun _ _ _ _ _ => rank_energy_exists_zero L c cutoff eta hcut K W
  | succ n hIH =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,_,_,_,_,hbox,hone,_⟩ := exists_canonical_reference_cutoff lo hi
      have hL0:0≤L:=by linarith
      have heF:0<firstPassEpsilon L eta:=by unfold firstPassEpsilon;positivity
      have hem:0<sourceMassEpsilon L eta:=by unfold sourceMassEpsilon;positivity
      obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
        hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
        actual_complete_normalized_rank_step lo hi hlo hhi W hsW (W.smooth ⊤) Vlog Alog hbox hone
          L c eta eta 1 (sourceMassEpsilon L eta) (sourceMassEpsilon L eta) eta
          hL hc heta heta1 hetac heta heta1 hem hem heta K
      let child : Fin 4 → 𝓢(ℝ,ℂ) := ![w11,w12,w21,w22]
      have hex (i : Fin 4) : RankEnergyExists n L c cutoff eta K (child i) := by
        fin_cases i
        · exact hIH _ af1 bf1 ha1 (by linarith) (subset_closure.trans hs11)
        · exact hIH _ af1 bf1 ha1 (by linarith) (subset_closure.trans hs12)
        · exact hIH _ af2 bf2 ha2 (by linarith) (subset_closure.trans hs21)
        · exact hIH _ af2 bf2 ha2 (by linarith) (subset_closure.trans hs22)
      choose Jsub Bsub hBsub ih using hex
      let J := ∑ i, Jsub i
      have hj (i) : Jsub i ≤ J := Finset.single_le_sum (fun j _ => Nat.zero_le (Jsub j)) (Finset.mem_univ i)
      let dl:=2*(InverseClippingProfiles.momentOrder (firstDegree J)+(volume:Measure ℝ).integrablePower)
      let Jout:=max ds dl
      let B := 1+hi+∑ i, Bsub i
      have hsumB : 0 ≤ ∑ i, Bsub i := Finset.sum_nonneg (fun i _ => by linarith [hBsub i])
      have hB : 1 ≤ B := by dsimp [B]; linarith
      have hb0 : 0 ≤ B := by linarith
      have hhiB : hi ≤ B := by dsimp [B]; linarith
      have hBB (i) : Bsub i ≤ B := by
        have := Finset.single_le_sum (fun j _ => show 0 ≤ Bsub j by linarith [hBsub j]) (Finset.mem_univ i)
        dsimp [B]; linarith
      obtain ⟨Zt,hZt,hlarge⟩ := eventually_canonical_reference_gates hi Alog window eta heta
      refine ⟨Jout,B,hB,?_⟩
      intro q hq
      choose Csub Zsub hCsub hZsub hsub using fun i => ih i q hq
      obtain ⟨Cs,Cb,Zs,hCs,hCb,hZs,hstep⟩:=hstep (firstPassEpsilon L eta) eta heF heta J q hq
      let A := ∑ i, Csub i
      have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => (hCsub i).le)
      have hCA (i) : Csub i ≤ A := Finset.single_le_sum (fun j _ => (hCsub j).le) (Finset.mem_univ i)
      let C := (Cs+Cb)*(1+A)
      let Z₀ := Zs+Zt+∑ i, Zsub i
      have hsumZ : 0 ≤ ∑ i, Zsub i := Finset.sum_nonneg (fun i _ => by linarith [hZsub i])
      have hC : 0 < C := by dsimp [C]; positivity
      have hZ₀ : 1 < Z₀ := by dsimp [Z₀]; linarith
      refine ⟨C,Z₀,hC,hZ₀,?_⟩
      intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
      have hZs' : Zs ≤ Z := by dsimp [Z₀] at hZ; linarith
      have hZt' : Zt ≤ Z := by dsimp [Z₀] at hZ; linarith
      have hZchild (i) : Zsub i ≤ Z := by
        have := Finset.single_le_sum (fun j _ => show 0 ≤ Zsub j by linarith [hZsub j]) (Finset.mem_univ i)
        dsimp [Z₀] at hZ; linarith
      obtain ⟨hZ2,h2,hExp,hlog,hhiZ,hAZ,hwin⟩:=hlarge Z hZt'
      have hZ1:1<Z:=by linarith
      have hZ0:0<Z:=by linarith
      have mchild (i) := hsub i Z (hZchild i) D
        ((mul_le_mul_of_nonneg_right (hBB i) (Real.rpow_nonneg hZ0.le _)).trans hD)
        slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
      let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
      have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
      let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=poolPrimary_maximal F hF
      dsimp only [CompletePoolRankMoments] at mchild ⊢
      intro Ψ hΨ m hm N V M Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels theta
      have hcap:N+V≤L:=by
        unfold rankTotalCap at hFc
        have hh:0≤15*((n+1:ℕ):ℝ)*eta:=by positivity
        linarith
      have hcm:0≤rankMargin (n+1) c eta:=by unfold rankMargin;positivity
      obtain ⟨hNL,hVL,hMF,hQL,hzL,hwidth,hmargin',hmL,hpuncture⟩:=
        actual_rank_state_gates m hm Z N V M Qwidth z (rankMargin (n+1) c eta) L
          hZ1 hN hV hM hQ hz hcm hcap hmargin hnorm
      obtain ⟨hΨnorm,hΨperiod⟩:=actual_rank_family_gates q base hbase hperiod Ψ hΨ
      have hDparent:hi*Z^N≤D:=by
        calc
          _≤B*Z^L:=mul_le_mul hhiB (Real.rpow_le_rpow_of_exponent_le hZ1.le hNL)
            (Real.rpow_nonneg hZ0.le _) hb0
          _≤D:=hD
      have hsscard:=(Finset.card_le_card hss).trans hslots
      have hssdis:(ss:Set σ).PairwiseDisjoint lists:=by
        intro i hi j hj hij
        exact hdis (hss hi) (hss hj) hij
      have hssH:=fun i hi=>hH i (hss hi)
      have hssP:=fun i hi=>hP i (hss hi)
      have hssa:=fun i hi=>ha i (hss hi)
      have hssprod:=canonical_rank_subslot_cap slots ss H Z z hss hH hprod
      obtain ⟨hsmallM,hsmallF,hsmallc⟩:=actual_rank_successor_caps n L c cutoff eta M (N+V)
        (rankMargin (n+1) c eta) hMc hFc le_rfl
      have lift (w:𝓢(ℝ,ℂ))(Cw:ℝ)(Jw:ℕ)(hCw:0≤Cw)(hCwA:Cw≤A)(hJw:Jw≤J)
          (mw:CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ base slots lists a w Z (rankRowCap n cutoff)
            (rankTotalCap n L eta) z (rankMargin n c eta) (rankLoss n eta) Cw K Jw):
          CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ base ss lists a w Z (M-3*(cutoff/2)/2)
            (N+V+15*eta) z (rankMargin (n+1) c eta-7*eta) (rankLoss n eta) A K J:=by
        apply canonical_rank_subslots (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) Finset.univ base slots ss lists a w Z _ _ z _ _ A K J hss
        apply canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) Finset.univ base slots lists a w Z
          (M-3*(cutoff/2)/2) (rankRowCap n cutoff) (N+V+15*eta) (rankTotalCap n L eta)
          z (rankMargin (n+1) c eta-7*eta) (rankMargin n c eta) (rankLoss n eta) A K J
          (by linarith) hsmallF hsmallc
        exact canonical_rank_height_constant (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) Finset.univ base slots lists a w Z _ _ z _ _ Cw A K Jw J
          hZ0 hCw hCwA hJw mw
      have mlift (i) := lift (child i) (Csub i) (Jsub i) (hCsub i).le (hCA i) (hj i) (mchild i)
      have hechild:0≤rankLoss n eta:=by unfold rankLoss;positivity
      obtain ⟨_,_,hpieta,hmass,hret,hprincipal0,hcost⟩:=actual_step_parameters L eta 0 0 (rankLoss n eta)
        hL0 heta heta1 (by linarith) (by linarith) hechild
      obtain ⟨hprincipal,hFirst,hFinal⟩:=actual_complete_step_cost L eta (rankLoss n eta) hL0 heta heta1 hechild
      have hreserve:c/2≤rankMargin (n+1) c eta:=by
        unfold rankMargin
        exact le_add_of_nonneg_right (by positivity)
      have hbound:=hstep m hm Z N V M z (rankMargin (n+1) c eta) cutoff (8*eta)
        (rankLoss n eta) A (rankLoss n eta+58*eta) (rankLoss n eta+60*eta) theta
        hZs' hZ2 h2 hExp hlog hN hV hM hcap hMF hzL hhiZ hAZ hwin hcut hcutL hcutc hetad hmL hmargin'
        hreserve (by simpa only [hwidth] using hpuncture) (by positivity) hpieta hmass hmass hechild
        (by linarith) hret hprincipal hcost (by linarith) hA
        labels (fun I hI=>⟨⟨(hlabels I hI).1.1,(hlabels I hI).1.2.2⟩,(hlabels I hI).1.2.1,(hlabels I hI).2⟩)
        D hDparent ss hsscard lists H hssdis hssH hssP hssprod base Ψ hΨ hΨnorm hΨperiod a hssa
        (mlift 0) (mlift 1) (mlift 2) (mlift 3)
      have hnextLoss:rankLoss n eta+62*eta=rankLoss (n+1) eta:=by unfold rankLoss;push_cast;ring
      have hloss0:0≤rankLoss (n+1) eta:=by unfold rankLoss;positivity
      have hlong:Cb*(1+A)*(1+‖theta‖)^dl*
          Z^(N+V+(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta)≤
          Cb*(1+A)*(1+‖theta‖)^dl*Z^(N+V+rankLoss (n+1) eta):=by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hZ1.le
        linarith
      have hh:=hbound.trans (add_le_add le_rfl hlong)
      have hmrg:=actual_complete_height_merge ds dl Z (N+V) c (rankLoss (n+1) eta) Cs Cb A theta
        hZ1.le hc.le hloss0 hCs.le hCb hA
      have hpow:(1+‖theta‖)^Jout≤(1+‖theta‖)^(2*Jout):=
        pow_le_pow_right₀ (by linarith [norm_nonneg theta]) (by omega)
      have hf:childLogTest W theta=normTwistedSource W theta:=by
        funext y
        simp only [childLogTest,normTwistedSource,mul_comm]
      rw [hf]
      apply (hh.trans hmrg).trans
      dsimp only [C,Jout]
      have hx:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (show 0≤(Cs+Cb)*(1+A) by positivity))
        (Real.rpow_nonneg hZ0.le (N+V+rankLoss (n+1) eta))
      convert hx using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
