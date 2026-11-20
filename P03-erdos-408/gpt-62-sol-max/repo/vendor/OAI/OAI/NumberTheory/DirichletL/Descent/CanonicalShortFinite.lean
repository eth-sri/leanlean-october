module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Inversion.CanonicalShortAttachment
public import OAI.NumberTheory.DirichletL.Descent.ShortReflectedEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CubeCompletedEnergyUniformDegree
public import OAI.NumberTheory.DirichletL.Descent.ShortReflectedPower
public import OAI.NumberTheory.DirichletL.Inversion.ShortCanonicalNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseCanonicalShortAttachment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
open InverseShortCanonicalNormalization
local notation "Eis"=>ActualEisensteinCubic.O
universe u v
set_option maxHeartbeats 1200000 in
theorem actual_complete_short_finite_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q:ℕ)(_hq:q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,Supported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
    ∀ D : ℕ,hi*Z^N≤D → ∀ slots : Finset σ,slots.card≤rmax →
    ∀ (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) →
      (∏j∈slots,H j)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      Z^(-V)*(∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  let := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
  obtain ⟨degree, hu⟩ := canonical_cube_shifted_completed_energy_uniform_degree
    lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax
  obtain ⟨B, hB, hbound⟩ := short_harmonic_small_power L (cstar/128) hL (by positivity)
  obtain ⟨A, hA, hmass⟩ := divisor_weight_sum K L (cstar/256) hL (by positivity)
  refine ⟨degree, ?_⟩
  intro q hq
  obtain ⟨C, Z₀, hC, hZ₀, he⟩ := hu q hq
  refine ⟨A*(6*(C*B)), Z₀, by positivity, hZ₀, ?_⟩
  intro σ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabels T hT D hD slots hcard lists H hdis hH1 hH hprod
    Ψ hΨ hperiod θ a ha
  dsimp only
  let S:=reflectionExcludedPrimes q
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF :=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
  let ilists:slots→Finset (Ideal Eis):=fun j=>idealLists F lists j.val
  let iw:∀j,ilists j→ℂ:=fun j=>idealWeights F lists a j.val
  have hp (j:slots) (P:Ideal Eis) (hP:P∈ilists j) := idealLists_prime_data F hF lists j.val P hP
  have hcap : ∀j:slots,∀P∈ilists j,(Ideal.absNorm P:ℝ)≤H j.val := by
    intro j P hP
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
    exact hH j.val j.property i hi
  have hw : ∀j:slots,∀P:ilists j,‖iw j P‖≤1 := by
    intro j P
    obtain ⟨i,hi,hh⟩:=Finset.mem_image.mp P.property
    change ‖transportCoeff F a j.val P.val‖≤1
    rw [←hh,transportCoeff_val]
    exact ha j.val j.property i hi
  have hZ1 := hZ₀.trans_le hZ
  have hz := zero_lt_one.trans hZ1
  have hpN (f : Ideal Eis) (hf : f ∈ labels) := (hlabels f hf).2
  have hcard' : Fintype.card slots ≤ rmax := by simpa using hcard
  have hprod' : (∏ j : slots,H j.val) ≤ Z^z₀ := by simpa only [Finset.prod_coe_sort] using hprod
  have htw := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((normTwistedSource_support W θ).trans hWs)
  let rows := T.image (fun k => Ideal.span {k})
  have hrows := CompletedUnitRows.image_span_nonzero_norm T (Z^M) hT
  let mark := tupleDivisibilityMark ilists iw
  let r (f : Ideal Eis) k := rowTwist Ψ (ActualFiber.maskElement q m) (idealGenerator f) k
  let G := C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)
  let E := (C*B)*(1+‖θ‖)^degree*Z^(N+V-cstar/128)
  have hf (f : Ideal Eis) (hfl : f∈labels) :
      (∑ k∈T, ‖markedShortCompletedSum (r f k) (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2) ≤ 6*E := by
    apply (CompletedUnitRows.sum_nonzero_element_le_units T (fun k hk => (hT k hk).1) _
      (fun k => sq_nonneg _)).trans
    have hb (u : Eisˣ) : (∑ I∈rows, ‖markedShortCompletedSum (r f (u.val*idealGenerator I))
        (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2) ≤ E := by
      let χ (I : Ideal Eis) := r f (u.val*idealGenerator I)
      have hcompleted (J : Ideal Eis) (hJ : J∈shortCubeRange (Z^hcut)) :
          (∑ I∈rows, ‖markedCompletedT (χ I) (normTwistedSource W θ)
            (Z^N/(Ideal.absNorm J:ℝ)^3) (fun R=>mark (J^3*R))‖^2) ≤ G := by
        obtain ⟨hJ0,hJnorm⟩ := (mem_shortCubeRange _ J).mp hJ
        have hn : 0<(Ideal.absNorm J:ℝ) := by
          exact_mod_cast Ideal.absNorm_pos_of_ne_bot (hJ0)
        have hc := (Real.logb_le_iff_le_rpow hZ1 hn).mpr hJnorm.le
        have hjpow := (Real.rpow_logb hz (ne_of_gt hZ1) hn).ge
        have h := he f (hpN f hfl).1 m hm Z N V M z₀ margin (Real.logb Z (Ideal.absNorm J:ℝ)) d
          hZ hN hM hMc hVc hzc (hc.trans hcutc) (hpN f hfl).2 hRn hmargin hreserve hVd
          (hc.trans hcutd) hd rows hrows hcard' ilists (fun j : slots=>H j.val)
          (idealLists_disjoint F slots lists hdis) (fun j P hP=>(hp j P hP).1) (fun j P hP=>(hp j P hP).2.1)
          (fun j P hP=>(hp j P hP).2.2.1) (fun j P hP=>(hp j P hP).2.2.2)
          (fun j=>hH1 j.val j.property) hcap hprod' Ψ hΨ hperiod J hJ0 hjpow u θ iw hw
        rw [short_cube_exact_scale Z N hZ1 J hJ0] at h
        simpa only [← completed_tuple_mark ilists iw _ _ htw _
          (div_pos (Real.rpow_pos_of_pos hz _) (pow_pos hn _)) J] using h
      have hh := marked_short_completed_energy (fun I : rows => χ I.val)
        (fun I n=>rowTwist_norm Ψ hΨ _ _ _ n) (fun _=>mark)
        (normTwistedSource W θ) (Z^N) (Z^hcut) G (by dsimp [G]; positivity)
        (fun J hJ=>by
          rw [Finset.sum_coe_sort rows (fun I => ‖markedCompletedT (χ I) (normTwistedSource W θ)
            (Z^N/(Ideal.absNorm J:ℝ)^3) (fun R => mark (J^3*R))‖^2)]
          exact hcompleted J hJ)
      rw [Finset.sum_coe_sort rows (fun I => ‖markedShortCompletedSum (χ I)
        (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2)] at hh
      apply hh.trans
      calc
        _ ≤ G*(B*Z^(cstar/128)) := mul_le_mul_of_nonneg_left (hbound Z hcut hZ1.le hcut0 hcutc)
          (by dsimp [G]; positivity)
        _ = E := by
          dsimp [G,E]
          rw [show N+V-cstar/128=(N+V-cstar/64)+cstar/128 by ring, Real.rpow_add hz]
          ring
    exact (Finset.sum_le_sum (fun u _ => hb u)).trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,CompletedUnitRows.unit_card,nsmul_eq_mul,Nat.cast_ofNat])
  rw [funext (indexed_mark_eq_tuple F slots lists a)]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ f∈labels, secondLabelWeight K f*(Z^(-V)*(6*E)) := by
      refine Finset.sum_le_sum (fun f hfl => ?_)
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf f hfl) (by positivity))
        (by unfold secondLabelWeight; positivity)
    _ ≤ (A*Z^(V+cstar/256))*(Z^(-V)*(6*E)) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hmass Z V hZ1.le hV hVc labels
        (fun f hf=>⟨(hpN f hf).1.ne_zero,(hpN f hf).2⟩)) (by dsimp [E]; positivity)
    _ = _ := by
      dsimp only [E]
      have hr : Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)=Z^(N+V-cstar/256) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
      rw [←hr]
      ring

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI
