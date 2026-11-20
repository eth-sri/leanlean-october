module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveHeightStep
public import OAI.NumberTheory.DirichletL.Descent.TwoPassScalar
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCoefficient
public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicOriginalBranches
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveParents
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks InverseMomentFirstChildWindows InverseMomentFirstOriginalProfile
open InverseMomentFirstProfileUniform InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

set_option maxHeartbeats 800000 in
theorem actual_long_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[OAI.PrincipalFamily.Maximal p]
      (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:OAI.PrincipalFamily.Coprime p)
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hbinExp:Real.exp 1≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖eisEmbedding (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*Z^ell)
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hparent:M-ell≤r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
      (_htail: -saving≤r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) := by
  let g₁:=priorityLogWindow om a b ha hs true
  let g₂:=priorityLogWindow om a b ha hs false
  let M₀:=|Real.log a|+|Real.log b|
  have hm:0≤M₀:=by dsimp [M₀];positivity
  obtain ⟨om₁,om₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_refined_cell_physical_budget
    g₁ g₂ rowMajorant M₀ M₀ hm hm (priorityLogWindow_support om a b ha hs true) (priorityLogWindow_support om a b ha hs false)
  let bw:=max 1 (max hi b)
  have hbw:1≤bw:=le_max_left _ _
  have hbwb: b≤bw:=(le_max_right hi b).trans (le_max_right 1 _)
  have hbwh:hi≤bw:=(le_max_left hi b).trans (le_max_right 1 _)
  have hbwp:0<bw:=by linarith
  let window:=Real.log bw
  have hew:Real.exp window=bw:=Real.exp_log hbwp
  have hsold:∀y,om y≠0→y≤b:=fun y hy=>(hs hy).2
  obtain ⟨w₁₁,w₁₂,af₁,bf₁,haf₁,hab₁,hw₁₁,hw₁₂,hs₁₁,hs₁₂,hleft⟩:=actual_live_first_height
    om b hsold om₁ lo hi hlo (subset_closure.trans hs₁) true
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  obtain ⟨w₂₁,w₂₂,af₂,bf₂,haf₂,hab₂,hw₂₁,hw₂₂,hs₂₁,hs₂₂,hright⟩:=actual_live_first_height
    om b hsold om₂ lo hi hlo (subset_closure.trans hs₂) false
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew.symm,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform epsFirst hepsF
  obtain ⟨Cp,Kp,hCp,hKp,hcell⟩:=he epsFirst hepsF 0 (firstDegree degree)
  obtain ⟨Cc,hCc,hcount⟩:=original_live_joint_small_power b Lcap epsFirst hb hcap hepsF
  obtain ⟨Cz,Ct,hCz,hCt,hbranches⟩:=original_dyadic_zero_tail om b Lcap Lcap eta tau (saving+eta) epsFirst
    (fun y hy=>(hs hy).2) hcap hcap heta htau hepsF
  let Cf := Cp*Kp*Cc
  have hCf : 0 ≤ Cf := by dsimp [Cf]; positivity
  obtain ⟨Cl,hCl,hleft⟩:=hleft degree epsSecond hepsS
  obtain ⟨Cr,hCr,hright⟩:=hright degree epsSecond hepsS
  let C := Cf*(Cl+Cr)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Ccoef,C+Cz+Ct,hCcoef,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ pi epschild A loss lossFinal hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights mark Y cutoff W source keys hl hr'
  have hz:0<Z:=by linarith
  have hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  let theta := ξ
  let Γ := Ccoef*(Real.exp 1*Z^ell)^epsFirst
  let β := actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ
  have hΓ : 0 ≤ Γ := by dsimp [Γ]; positivity
  have hβ : ∀ I ∈ labels, ∀ v ∈ Q, ‖β I v‖ ≤ Γ := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  let Be:ℝ:=(Cl+Cr)*(1+A)*Z^(r+3*ell+V+loss)
  have hBe:0≤Be:=by dsimp[Be];positivity
  have fit (c : ℝ) (hc' : c ≤ Cl+Cr) (z : Frequency × (Fin 9 → ℝ)) :
      c*(1+A)*Z^(r+3*ell+V+loss)*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) ≤
      Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    have hwgt := le_trans zero_le_one (first_weight_one_le (firstDegree degree) z)
    dsimp [Be]
    gcongr
  have hZ1 : 1 < Z := by linarith
  have hleftCell k hk (z : Frequency × (Fin 9 → ℝ)) := by
    have he:=hleft p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A theta (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hl k hk) z
    rw [columnScale_physical Z r (by linarith)] at he
    exact he.trans (fit Cl (by linarith) z)
  have hrightCell k hk (z : Frequency × (Fin 9 → ℝ)) := by
    have he:=hright p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A theta (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hr' k hk) z
    rw [columnScale_physical Z r (by linarith)] at he
    exact he.trans (fit Cr (by linarith) z)
  have hK : 0 < Z^M := Real.rpow_pos_of_pos hz _
  have hret' : (Z^(-r-2*ell-V)*Z^M)*
      ‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant (Z^M) Y cutoff (fun _=>1)‖ ≤
        Cf*Γ^2*Be*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst) := by
    dsimp only [Cf]
    have hsum:=original_retained_joint_profile_bound p hp hcop hg pool Q labels β cutoff Ψ m mark
      om a b ha hs rowMajorant (Z^M) Y (Z^r) theta (Real.rpow_pos_of_pos hz _) (fun _=>1) (by intro i;norm_num)
    have hnrm:0≤Z^(-r-2*ell-V)*Z^M:=mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)
    apply (mul_le_mul_of_nonneg_left hsum hnrm).trans
    rw [Finset.mul_sum]
    let budget := (Cp*Kp)*Γ^2*Be*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*Z^((2*Lcap+15*eta+tau)*epsFirst)
    refine (Finset.sum_le_sum (g := fun _ => budget) ?_).trans ?_
    · intro k hk
      let T₁:=(physicalScales (Z^r) k.1 k.2.1) 7
      let T₂:=(physicalScales (Z^r) k.1 k.2.1) 8
      have hT₁:0<T₁:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 7
      have hT₂:0<T₂:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 8
      have hY:0<firstCellRadius Z M r ell V eta tau k.1 k.2.2:=Real.rpow_pos_of_pos hz _
      have hL:0≤eta*Real.log Z:=mul_nonneg heta (Real.log_nonneg hZ1.le)
      have hleftRefined (z : Frequency × (Fin 9 → ℝ)) := (mul_le_mul_of_nonneg_left
        (refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights om₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _))
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hleftCell k hk z)
      have hrightRefined (z : Frequency × (Fin 9 → ℝ)) := (mul_le_mul_of_nonneg_left
        (refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights om₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _))
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hrightCell k hk z)
      have he' := hcell p hp hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y
        (firstCellRadius Z M r ell V eta tau k.1 k.2.2) hΨ hΓ hY hsf hn hβ k.1 k.2.1 (labelGate p k.2.2)
        (fun x hx I _=>first_dyadic_refined_cutoff p pool Q k.1 k.2.2 Z M r ell V eta tau x hx I)
        T₁ T₂ (Z^M) theta (eta*Real.log Z) hT₁ hT₂ hK hL Be Z M r ell V (dyadicExponent Z (k.1 3))
        (dyadicExponent Z (k.1 0)) (dyadicExponent Z (k.1 1)) (dyadicExponent Z (k.1 2))
        (dyadicExponent Z (k.1 4)) (dyadicExponent Z k.2.1) (dyadicExponent Z (k.1 5)) eta
        hBe hz (physicalScales_rpow Z r hZ1 k.1 k.2.1) rfl hleftRefined hrightRefined
      have hrad:=first_live_cell_radius_cap p hp pool Q labels Y _ Z M r ell V eta tau Lcap hZ1 hbin hM hF hQ k hk
      have hpow:=Real.rpow_le_rpow hY.le hrad hepsF.le
      rw [←Real.rpow_mul hz.le] at hpow
      simp only [pow_zero,div_one,norm_neg] at he'
      calc
        _≤(Γ^2*Kp*(firstCellRadius Z M r ell V eta tau k.1 k.2.2)^epsFirst*Be)*
            (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder (firstDegree degree)*(1+‖theta‖)^InverseClippingProfiles.momentOrder (firstDegree degree))):=he'
        _≤(Γ^2*Kp*Z^((2*Lcap+15*eta+tau)*epsFirst)*Be)*
            (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder (firstDegree degree)*(1+‖theta‖)^InverseClippingProfiles.momentOrder (firstDegree degree))):=by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hBe
        _=budget:=by dsimp only [budget]; rw [show 2*InverseClippingProfiles.momentOrder (firstDegree degree)=InverseClippingProfiles.momentOrder (firstDegree degree)+InverseClippingProfiles.momentOrder (firstDegree degree) by omega,pow_add];ring
    · have hnkey:=hcount p hp hcop hg pool Q labels β cutoff Ψ m mark om rowMajorant (Z^M) Z r ell Lcap eta tau theta
        hZ hrcap hellcap hcap le_rfl heta heta1 htau.le htau1 hQ hn (fun y hy=>(hs hy).2)
      change (∑ _k ∈ keys, budget) ≤ _
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm (keys.card : ℝ)]
      calc
        budget * (keys.card : ℝ) ≤ budget * (Cc*Z^epsFirst) :=
          mul_le_mul_of_nonneg_left hnkey (by dsimp [budget]; positivity)
        _ = _ := by dsimp only [budget]; rw [Real.rpow_add hz] <;> ring
  have hfull : Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
        Cf*Γ^2*Be*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ct*Γ^2*Z^(-saving) := by
    have he':=original_global_physical_energy p hp hcop hg hinj hc hpr pool Q hQpool labels hn β Ψ m mark W
      (Z^M) Y hK cutoff (fun _ _ _ _ _ _ _=>Real.rpow_nonneg hz.le _)
      (fun x hx _ _=>first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Lcap hZ1 hbin hM hF hQ x hx)
      (fun _=>1) (by norm_num)
    obtain ⟨hz',ht'⟩:=hbranches p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
      hZ1 hbin hM hMcap hell hV hr hF hΓ hbZ hΨ hQ hn hlabels hβ hslots hweights
    have hfactor:Z^(-r-2*ell-V)≤Z^eta:=Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
    have htail:Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q D I=>
          canonicalCubeDualTail p hp hcop hg pool q D Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
            (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
            (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
            (reopenedPhysicalCutoff p q I (cutoff q D I)))‖≤Ct*Γ^2*Z^(-saving):=by
      have ht'':=ht'
      apply (mul_le_mul hfactor ht'' (norm_nonneg _) (Real.rpow_nonneg hz.le _)).trans
      apply le_of_eq
      rw [show Z^eta*(Ct*Γ^2*Z^(-(saving+eta)))=(Ct*Γ^2)*(Z^eta*Z^(-(saving+eta))) by ring,
        ←Real.rpow_add hz]
      congr 2
      ring
    have hall:=mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg hz.le (-r-2*ell-V))
    simp only [mul_add] at hall
    apply hall.trans
    refine add_le_add (add_le_add hz' ?_) htail
    simpa only [mul_assoc] using hret'
  apply hfull.trans
  convert (two_pass_scalar C Cz Ct Γ A Z (r+3*ell+V) M r ell eta tau pi epsFirst loss Lcap saving lossFinal
  ((1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))) hC hCz hCt hA (by linarith)
  (one_le_pow₀ (by linarith [norm_nonneg theta])) hparent hprincipal hretained htail) using 1 <;> dsimp [Be, C, Γ, theta] <;> ring

end SevenEighths.InverseMoment

end

end OAI
