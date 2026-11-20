module
public import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCoefficient
public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicFullEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstDyadicOriginalBranches
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
public import OAI.NumberTheory.DirichletL.Descent.FirstLiveHeightStep
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy
public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveParents
public import OAI.NumberTheory.DirichletL.Descent.TwoPassScalar

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

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
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
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
          Z^(r+3*ell+V+lossFinal)  := by
  obtain ⟨om₁,om₂,lo,hi,hlo,hlh,hom₁,hom₂,hs₁,hs₂,hfull⟩:=original_dyadic_full_energy om a b ha hs Lcap Lcap eta tau saving hcap hcap hb heta heta1 htau htau1
  let bw:=max 1 (max hi b)
  have hbw:1≤bw:=le_max_left _ _
  have hbwb: b≤bw:=(le_max_right hi b).trans (le_max_right 1 _)
  have hbwh:hi≤bw:=(le_max_left hi b).trans (le_max_right 1 _)
  have hbwp : 0<bw := zero_lt_one.trans_le hbw
  let window:=Real.log bw
  have hew:Real.exp window=bw:=Real.exp_log hbwp
  have hsold:∀y,om y≠0→y≤b:=fun y hy=>(hs hy).2
  obtain ⟨w₁₁,w₁₂,af₁,bf₁,haf₁,hab₁,hw₁₁,hw₁₂,hs₁₁,hs₁₂,hLeftHeight⟩:=actual_live_first_height
    om b hsold om₁ lo hi hlo (subset_closure.trans hs₁) true
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  obtain ⟨w₂₁,w₂₂,af₂,bf₂,haf₂,hab₂,hw₂₁,hw₂₂,hs₂₁,hs₂₂,hRightHeight⟩:=actual_live_first_height
    om b hsold om₂ lo hi hlo (subset_closure.trans hs₂) false
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew.symm,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Cf,Cz,Ct,hCf,hCz,hCt,hfull⟩:=hfull epsFirst hepsF (firstDegree degree)
  obtain ⟨Cl,hCl,hLeftHeight⟩:=hLeftHeight degree epsSecond hepsS
  obtain ⟨Cr,hCr,hRightHeight⟩:=hRightHeight degree epsSecond hepsS
  obtain ⟨Ccoef,hCcoef,hcoef⟩ := actualLongCoefficient_uniform epsFirst hepsF
  let C := Cf*(Cl+Cr)
  have hC : 0 ≤ C := mul_nonneg hCf (add_nonneg hCl.le hCr.le)
  refine ⟨Ccoef,C+Cz+Ct,hCcoef,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ pi epschild A loss lossFinal hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith only [hZ]
  have hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤Ccoef*(Real.exp 1*Z^ell)^epsFirst := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  let Γ := Ccoef*(Real.exp 1*Z^ell)^epsFirst
  have hΓ : 0 ≤ Γ := by dsimp [Γ]; positivity
  let β := actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ
  let Be:ℝ:=(Cl+Cr)*(1+A)*Z^(r+3*ell+V+loss)
  have hBe:0≤Be:=by dsimp[Be];positivity
  have left : ∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights om₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    intro k hk z
    have he:=hLeftHeight p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A ξ (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hleft k hk) z
    rw [columnScale_physical Z r (by linarith only [hZ])] at he
    apply he.trans
    change (Cl*(1+A)*Z^(r+3*ell+V+loss))*_ ≤ Be*_
    have hwgt:0≤tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := le_trans zero_le_one (first_weight_one_le _ z)
    dsimp[Be]
    gcongr
    linarith
  have right : ∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights om₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    intro k hk z
    have he:=hRightHeight p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A ξ (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hright k hk) z
    rw [columnScale_physical Z r (by linarith only [hZ])] at he
    apply he.trans
    change (Cr*(1+A)*Z^(r+3*ell+V+loss))*_ ≤ Be*_
    have hwgt:0≤tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := le_trans zero_le_one (first_weight_one_le _ z)
    dsimp[Be]
    gcongr
    linarith
  have hall:=hfull p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ ξ Be
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hBe hsf hn hβ hlabels hslots hweights left right
  refine hall.trans ?_
  convert two_pass_scalar C Cz Ct Γ A Z (r+3*ell+V) M r ell eta tau pi epsFirst loss Lcap saving lossFinal
    ((1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))) hC hCz hCt hA (by linarith only [hZ])
    (one_le_pow₀ (by linarith [norm_nonneg ξ])) hparent hprincipal hretained htail using 1 <;> dsimp only [Be,C,Γ] <;> ring

end SevenEighths.InverseMoment

end

end OAI
