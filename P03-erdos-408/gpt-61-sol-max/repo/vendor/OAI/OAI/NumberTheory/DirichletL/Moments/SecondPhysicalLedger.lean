module

public import OAI.NumberTheory.DirichletL.Moments.SourceBlockWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSourceBlockWindows CenteredMomentSecondPhysicalCost
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing
open CenteredMomentSecondSectorFrequency CenteredMomentFirstWholeKernel
open CenteredMomentSmooth


section
variable (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset ActualEisensteinCubic.O) (W : 𝓢(ℝ,ℂ)) (Z x c d g u v f p K H a k₀ h₀ A B : ℝ) (hZ : 1<Z)

theorem physicalBlock_effective_window    
             
              (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K
      <dyadicScale (n 0) := by
  unfold physicalBlock at hne
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  split_ifs at hz with hpart
  · obtain ⟨I,hI,hIs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨J,hJ,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hIs
    have hk: ((_:ℂ)*((_:ℝ):ℂ))≠0:=(mul_ne_zero_iff.mp hterm).2
    have hw: (_:ℝ)≠0:=Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).2
    exact (dyadicWeight_support (n 0)
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).1).1).2
  · exact False.elim (hz rfl)

include hZ in
lemma logb_one_add_sixth     (hx:0<x) :
    Real.logb Z x/6≤Real.logb Z (1+x) := by
  have hp:0≤Real.logb Z (1+x):=Real.logb_nonneg hZ (by linarith)
  have hm:=Real.logb_le_logb_of_le hZ hx (show x≤1+x by linarith)
  linarith

include hZ in
theorem scalar_log_ledger  
      (hc:0<c) (hd:0<d) (hg:0<g) (hu:0<u) (hv:0<v)
    (hf:0<f) (hp:0<p) (hK:0<K) (hH:0<H) (ha:0<a)
    (hk₀:0<k₀) (hh₀:0<h₀) (hA:0<A) (hB:0<B)
    (hk:K*g*v/(c*d)≤k₀) (hleft:a*H/c≤A) (hright:a*H/d≤B) :
    Real.logb Z (K*g/(Real.sqrt c*Real.sqrt d*u*Real.sqrt A*Real.sqrt B)*
      h₀^(1/6:ℝ)/(1+k₀*h₀/(A*B))*H/(c*d)*p/f^(1/3:ℝ))≤
      Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-
      (Real.logb Z c+Real.logb Z d-5*Real.logb Z g/6-Real.logb Z p+
        Real.logb Z u+Real.logb Z v/6+Real.logb Z f/3) := by
  have hklog:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos (mul_pos hK hg) hv) (mul_pos hc hd)) hk
  have hl:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hc) hleft
  have hr:=Real.logb_le_logb_of_le hZ (div_pos (mul_pos ha hH) hd) hright
  have hdec:=logb_one_add_sixth Z (k₀*h₀/(A*B)) hZ (by positivity)
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) hv.ne',Real.logb_mul hK.ne' hg.ne',
    Real.logb_mul hc.ne' hd.ne'] at hklog
  rw [Real.logb_div (by positivity) hc.ne',Real.logb_mul ha.ne' hH.ne'] at hl
  rw [Real.logb_div (by positivity) hd.ne',Real.logb_mul ha.ne' hH.ne'] at hr
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul hk₀.ne' hh₀.ne',Real.logb_mul hA.ne' hB.ne'] at hdec
  simp (disch := positivity) only [Real.logb_div,
    Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos hh₀,
    Real.logb_rpow_eq_mul_logb_of_pos hf,
    logb_sqrt Z c hc,logb_sqrt Z d hd,logb_sqrt Z A hA,logb_sqrt Z B hB]
  linarith

end

def forcingNorm (C D) (U:Finset (CommonIndex C D)) : ℝ :=
  Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U))

def saving (C D) (U:Finset (CommonIndex C D)) (Z:ℝ)  :=
  Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
    5*Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/6-
    Real.logb Z (Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (∏ P∈U,P.val):ℝ)+
    Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)/6+
    Real.logb Z (forcingNorm C D U)/3

def centralPhysicalCost (C D) (U:Finset (CommonIndex C D))
    (K H:ℝ) (n:Fin 4→ℤ)  :=
  (1/H)*outerScalar C D K n*normalizer C D U*
    (dyadicScale (n 1))^(1/6:ℝ)/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
    (H^2/((C.absNorm:ℝ)*D.absNorm))*(Ideal.absNorm (∏ P:CommonIndex C D,P.val):ℝ)/
    (forcingNorm C D U)^(1/3:ℝ)

section
variable (η : Character) (t : ℝ) (S : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→ℂ) (C D : Ideal ActualEisensteinCubic.O) (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) (w : ActualEisensteinCubic.O) (hpart : canonicalPartition C D U w) (hcorr : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) (R : ℝ) (rows : Finset ActualEisensteinCubic.O) (hrows : ∀z∈rows,z≠0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) (hK : 0<K) (H a Z : ℝ) (hH : 0<H)

include hC in
lemma common_product_pos     (V:Finset (CommonIndex C D)) :
    (0:ℝ)<Ideal.absNorm (∏P∈V,P.val) := by
  rw [map_prod,Nat.cast_prod]
  apply Finset.prod_pos
  intro P hP
  rw [←commonPrime_span C D hC P]
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (commonPrime_supported C D hC P).1)

include hK hH in
theorem actual_physical_log_ledger    
             
               
          (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal ActualEisensteinCubic.O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.logb Z (centralPhysicalCost C D U K H n)≤
      Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-saving C D U Z := by
  have hc:(0:ℝ)<C.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg:(0:ℝ)<Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hv:(0:ℝ)<Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using nonunitFrequencyGenerator_ne_zero C D hC U))
  have hu:=common_product_pos C D hC U
  have hp:=common_product_pos C D hC Finset.univ
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hw:=physicalBlock_scale_lower η t S β C D hC hD U R rows W K n a H ha hlower hne
  have hl:a*H/(C.absNorm:ℝ)≤dyadicScale (n 2):=by
    have hh: H/(C.absNorm:ℝ)*a≤dyadicScale (n 2):=(le_div_iff₀ ha).mp hw.1
    convert hh using 1; ring
  have hr:a*H/(D.absNorm:ℝ)≤dyadicScale (n 3):=by
    have hh: H/(D.absNorm:ℝ)*a≤dyadicScale (n 3):=(le_div_iff₀ ha).mp hw.2
    convert hh using 1; ring
  have hk:=physicalBlock_effective_window η t S β C D hC hD U R rows W K n hne
  have he:secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)*
        Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U})/((C.absNorm:ℝ)*D.absNorm):=by
    simp only [secondEffectiveScale,map_mul,norm_mul,mul_pow,
      ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    ring
  rw [he] at hk
  have hb:=scalar_log_ledger Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)
    (Ideal.absNorm (∏P∈U,P.val):ℝ)
    (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ)
    (forcingNorm C D U) (Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)
    K H a (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
    hZ hc hd hg hu hv hf hp hK hH ha (dyadicScale_pos _) (dyadicScale_pos _)
    (dyadicScale_pos _) (dyadicScale_pos _) hk.le hl hr
  change _≤Real.logb Z H/3+5*Real.logb Z K/6-2*Real.logb Z a/3-saving C D U Z at hb
  convert hb using 1
  congr 1
  rw [centralPhysicalCost,normalizer,actual_partitionNormalizer C D hC,outerScalar]
  field_simp

include hC hD in
lemma centralPhysicalCost_pos      
        (hK:0<K) (hH:0<H)  n  :
    0<centralPhysicalCost C D U K H n := by
  have hc:(0:ℝ)<C.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hu:=normalizer_pos C D hC U
  have hn0:=dyadicScale_pos (n 0)
  have hn1:=dyadicScale_pos (n 1)
  have hn2:=dyadicScale_pos (n 2)
  have hn3:=dyadicScale_pos (n 3)
  unfold centralPhysicalCost outerScalar
  positivity

include hK hH in
theorem actual_physical_cost_bound    
             
               
          (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal ActualEisensteinCubic.O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*Z^(-saving C D U Z) := by
  have hh:=actual_physical_log_ledger η t S β C D hC hD U R rows W K n hK H a Z hH ha hZ hlower hne
  apply (Real.logb_le_logb hZ (centralPhysicalCost_pos C D hC hD U K H hK hH n)
    (show 0<H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*Z^(-saving C D U Z) by positivity)).mp
  simp (disch := positivity) only [Real.logb_mul,
    Real.logb_rpow_eq_mul_logb_of_pos hH,Real.logb_rpow_eq_mul_logb_of_pos hK,
    Real.logb_rpow_eq_mul_logb_of_pos ha,Real.logb_rpow (by linarith : 0<Z) hZ.ne']
  linarith

include hCD hpart hcorr in
theorem actual_canonical_physical_cost    
             
       
       
     
             n 
    (hK:0<K)  H a Z  (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal ActualEisensteinCubic.O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  have hs:=actual_second_ledger_lower C D hC hD hCD U w hpart Z hZ hcorr
  change (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3≤saving C D U Z at hs
  exact (actual_physical_cost_bound η t S β C D hC hD U R rows W K n hK H a Z hH ha hZ hlower hne).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity))

include hCD hrows hK in
theorem physicalBlock_canonical_witness    
             
       
           
        (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) ∧
      idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  have hn:=right_ne_zero_of_mul hne
  unfold normalizedBlock at hn
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  have hr:=left_ne_zero_of_mul hz
  have hpart:canonicalPartition C D U (nonunitFrequencyGenerator C D U*z):=by
    by_contra hp
    simp only [retainedScalar,canonicalPartitionScalar,hp,ite_false,zero_mul] at hr
    exact hr rfl
  refine ⟨z,hzr,hpart,?_⟩
  intro hc
  let F:ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>CenteredMomentLogDyadic.logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)
    (by simpa only [mul_assoc] using hc)
  exact (right_ne_zero_of_mul hz) (by simpa only [sectorFrequency,F] using he)

include hCD hrows hK in
theorem original_block_physical_cost    
             
       
               
       H a Z  (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal ActualEisensteinCubic.O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  obtain ⟨z,hz,hpart,hcorr⟩:=physicalBlock_canonical_witness η t S β C D hC hD hCD U R rows hrows W K hK n hne
  exact actual_canonical_physical_cost η t S β C D hC hD hCD U _ hpart hcorr R rows W K n
    hK H a Z hH ha hZ hlower hne

end

end SevenEighths.CenteredMomentSecondPhysicalLedger

end

end OAI
