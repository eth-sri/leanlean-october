module

public import OAI.NumberTheory.DirichletL.Descent.SecondCellColumnBounds
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityAggregate
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows
public import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
public import OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
public import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesGeometry
public import OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource
public import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityPhysical
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullAggregate
public import OAI.NumberTheory.DirichletL.Descent.SecondCellColumnBounds
public import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredEnergyUniform

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondPrincipalCaller InverseSecondProfileUniform FourierBridge CompletedHeight
open SecondPassIntegration JointLogSeparation InverseInitialClippedColumns InverseSecondFibers
open InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentGlobalPriorityTail InverseWholePriorityRetainedSource RayFourExpansion
open FirstCauchyArithmetic
open InverseInitialArithmetic InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
set_option maxHeartbeats 1200000 in
theorem global_priority_filtered_physical_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [OAI.PrincipalFamily.Maximal p]
    (hcop : OAI.PrincipalFamily.Coprime p)
    (hg : OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z : SecondRayIndex, WithSecondCellEnergy p hp hcop hg pool source (secondRayMinus Ψ₀ z) m
        (slots\assigned) lists a (labels assigned) (R assigned) Vlabel Z X εchild A K
        (fun d (t : Frequency × (Fin 6 → ℝ)) => clippedTest ω₁
          (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) (fun t => tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z : SecondRayIndex, WithSecondCellEnergy p hp hcop hg pool source (secondRayPlus Ψ₀ z) m
        (slots\assigned) lists a (labels assigned) (R assigned) Vlabel Z X εchild A K
        (fun d (t : Frequency × (Fin 6 → ℝ)) => clippedTest ω₂
          (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (fun t => tripleHeight J t.1*coordinateHeight J t.2))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_moving_radius_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨Cr,Cbin,hCr,hCbin,he⟩:=hordered J
  let Csum := Cr * (512*32^2)
  let C := (32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*Csum
  have hCsum : 0 ≤ Csum := by dsimp [Csum]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound :
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w negative Ψ m slots lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
    let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
    let H:=Csum*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
          (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
    have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
      P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
          globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
            wholeRow p hp hcop hg extra pool negative
              (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
              (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤H:=by
      obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
        ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
      let originalSource := unifiedSource p pool
        (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x => extra x.cube) original negative assigned lists)
        (fun _ => cutoff)
      let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
      let Hray := A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild)
      let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
          ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
            wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
              (principalWindow om lo hi hlo hsupport negative t) X Y z x
      have hP:0≤P:=by dsimp [P]; positivity
      have hz (z:SecondRayIndex):P*‖S z‖≤Cr*Hray*‖secondRayCoefficient z‖:=by
        have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw
          Ψ m ray core slots assigned lists a (fun _ => cutoff) z
          Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
          hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
          ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
          (hleft z) (hright z)
        convert h using 1 ; ring
      calc
        _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
        _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
        _≤∑z:SecondRayIndex,Cr*Hray*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
        _=Cr*Hray*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
        _≤Cr*Hray*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
        _= _:=by dsimp only [H,Csum,Hray]; ring
    have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
    let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
          globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
            wholeRow p hp hcop hg extra pool negative
              (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
              (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
    change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤H at hb
    change P*((32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
    calc
      _=(32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ray hr
        apply Finset.sum_congr rfl
        intro core hc
        apply Finset.sum_congr rfl
        intro assigned ha
        ring
      _≤(32*512)*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
      _=(32*512)*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
        simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
        ring
      _≤(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
      _= _:=by dsimp [C,Csum,H];ring
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add (hzn.trans (by dsimp [Cz'];gcongr)) hrbound) htbound)
end SevenEighths.InverseMoment

end

end OAI
