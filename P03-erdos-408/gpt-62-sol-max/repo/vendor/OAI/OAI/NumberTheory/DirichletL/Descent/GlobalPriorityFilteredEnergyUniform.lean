module

public import OAI.NumberTheory.DirichletL.Descent.SecondCellColumnBounds
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows
public import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
public import OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
public import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesGeometry
public import OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource
public import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource
public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedAllIntegral
public import OAI.NumberTheory.DirichletL.Descent.SecondVaryingPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource
public import OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy
public import OAI.NumberTheory.DirichletL.Descent.SecondOriginalMass

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondPrincipalCaller InverseSecondProfileUniform FourierBridge CompletedHeight
open SecondPassIntegration JointLogSeparation InverseInitialClippedColumns InverseSecondFibers
open InverseInitialArithmetic InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic JointLogSeparation
open MeasureTheory InverseInitialClippedColumns InverseSecondProfileUniform InverseAmbientProfileTower
open MeasureTheory SchwartzMap
local notation "Eis"=>ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

set_option maxHeartbeats 1000000 in
theorem global_priority_filtered_moving_radius_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [OAI.PrincipalFamily.Maximal p]
    (hcop : OAI.PrincipalFamily.Coprime p)
    (hg : OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (WithSecondCellEnergy p hp hcop hg pool source (secondRayMinus Ψ₀ z) m
        (slots\assigned) lists a labels R Vlabel Z X εchild A K
        (fun d (t : Frequency × (Fin 6 → ℝ)) => clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) (fun t => (tripleHeight J t.1*coordinateHeight J t.2))) →
      (WithSecondCellEnergy p hp hcop hg pool source (secondRayPlus Ψ₀ z) m
        (slots\assigned) lists a labels R Vlabel Z X εchild A K
        (fun d (t : Frequency × (Fin 6 → ℝ)) => clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (fun t => (tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  let g₂:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg₂:Function.support g₂⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  let g₁ := conjugateProfile g₂
  have hcg : Function.support g₁ ⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg₂
    simpa only [g₁,Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  let loCell : Fin 4 → ℝ := fun _ => 1
  let hiCell : Fin 4 → ℝ := fun _ => 2
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ g₂ mg mg 1 loCell hiCell B₀
      hm le_rfl hcg hg₂ (fun _ => zero_lt_one) (fun _ => by norm_num [loCell,hiCell]) hB₀
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨Cp,hCp,hmeasure⟩ := second_profile_common_measure
    U₀ g₁ g₂ rowMajorant M₀ B₀ mg mg 1 hM hB₀ hUs hcg hg₂ 0 J
  obtain ⟨Cm,hCm,hmassCell⟩ := actual_second_original_mass K εmass hεmass
  let C := Cp*Cm
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨coefficientBound*(36*(2:ℝ)^(2*K)*C),Cbin,mul_nonneg coefficientBound_pos.le (by dsimp [C]; positivity),hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsub:source⊆originalSource:=InverseMomentGlobalRetainedGates.geometrySource_subset p originalSource b X
  have hsource:ActualSecondSourceConditions p source:=
    ActualSecondSourceConditions.mono p (unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff) hsub
  have hdeleted:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    fun x hx=>unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff x (hsub hx)
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x (hsub hx)
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have hrow (x : MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0) :=
    wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hupper:∀y,principalWindow om lo hi hlo hsupport negative t y≠0 → y≤b:=by
    intro y hy
    have hy':y∈Function.support om:=by
      rw [←principalWindow_support om lo hi hlo hsupport negative t]
      exact hy
    exact (hsupport hy').2.trans hhib
  rw [InverseMomentGlobalRetainedGates.original_retained_geometry_sum p hp hcop hg extra pool originalSource
    (globalPriorityWeight p hg negative Ψ m ray core w assigned a) negative Ψ₀ m slots assigned lists a
    (principalWindow om lo hi hlo hsupport negative t) X Y b hX hupper z]
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [mul_left_comm ((Y:ℂ)*secondRayCoefficient z) (coefficientBound:ℂ),
    norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  let slots₁ := slots \ assigned
  let w' := normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a
  let deleted := InverseMomentWholeRetainedSource.deleted (Jo := Jo+(assigned.card+assigned.card)) p extra negative
  let bound := (36*(2:ℝ)^(2*K)*C)*A*‖secondRayCoefficient z‖*
    (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  rw [mul_right_comm _ coefficientBound, mul_comm _ coefficientBound]
  refine (mul_le_mul_of_nonneg_left (c := bound) ?_ coefficientBound_pos.le).trans_eq
    (by dsimp [bound] <;> ring)
  rw [mul_assoc (9/2 : ℝ) eta (Real.log Z)]
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₁.card*A*C*H
  have hD:0≤D:=by dsimp [D,H,C];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₁.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=by
      apply mul_le_mul_of_nonneg_left _ hP
      rw [←hfactor]
      have hz:0<Z:=zero_lt_one.trans hZ
      have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
      rw [physical_source_partition p hp hcop hg source pool Ψ₀ m z slots₁ slots₁ lists lists a a
        deleted deleted w']
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      have hin : cell p source d⊆source:=cell_subset p source d
      have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
        intro x hx
        have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
          (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
        apply hr.trans
        rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤scales d 0 from (dyadScale_pos _).le)
      have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
        intro x hx
        have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
          simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
        have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
          Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
        rw [second_cell_scale_rpow Z d 1 hZ] at hh
        exact hh.trans hr
      let Q := cell p source d
      have hQ : ∀ x∈Q,index p x=d := fun x hx=>(mem_cell p source d x).mp hx |>.2
      have hblock := actual_source_block_ratios p hp Q d hQ (fun x hx=>hk x (hin hx))
      let Ncell := secondCellColumnExponent Z X d
      let Xcell := Z^Ncell
      let Gcell := scales d 0
      let Ecell := scales d 1
      let Vcell := scales d 2
      let Bcell := scales d 3
      let Rc := R d
      let θ := priorityHeight negative t
      have hG : 0 < Gcell := dyadScale_pos _
      have hE : 0 < Ecell := dyadScale_pos _
      have hV : 0 < Vcell := dyadScale_pos _
      have hB : 0 < Bcell := dyadScale_pos _
      have hXcell : 0 < Xcell := Real.rpow_pos_of_pos hz _
      have hrowsCell : ∀ x ∈ Q, x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) Rc :=
        fun x hx => by simpa only [hQ x hx] using hrows x (hin hx)
      have hsCell := cell_conditions p source hsource d
      have hdel := fun x (hx : x ∈ Q) => hdeleted x (hin hx)
      obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp Q pool Ψ₀ m z Gcell Ecell Vcell Bcell (Z^Ncell) ρ (1 : ℝ) (1 : ℝ) (-θ) θ
        hG hE hV hB hXcell hρ le_rfl le_rfl le_rfl le_rfl hblock
      have hRad : 0 < Y*Bcell/(Ecell*Vcell^2*(Z^Ncell)^2) := by positivity
      obtain ⟨b₃,hb₃⟩ := hmeasure (Y*Bcell/(Ecell*Vcell^2*(Z^Ncell)^2)) hRad
      obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ (1 : ℝ) (1 : ℝ) (-θ) θ L hρ le_rfl le_rfl le_rfl le_rfl hL
      let gRoot := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.secondBalancedSlope i) (hUs i)
      let f₁ := rooted g₁ mg (-(1/2:ℝ)) hcg
      let f₂ := rooted g₂ mg (-(1/2:ℝ)) hg₂
      let den := density gRoot f₁ f₂ b₃ ρ (1 : ℝ) (1 : ℝ) (-θ) θ L
      have hDensity : Integrable den := balanced_density_integrable gRoot f₁ f₂ b₃ ρ (1 : ℝ) (1 : ℝ) (-θ) θ L
      let W₁ := fun x => star (positiveSource g₁ (1 : ℝ) (-θ) x)
      let W₂ := positiveSource g₂ (1 : ℝ) θ
      have hsep' : ∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ rowMajorant
          (fun i y => U₀ i (y+ρ i)) (Y*Bcell/(Ecell*Vcell^2*Xcell^2)) y =
            ∫ t : Frequency × (Fin 6 → ℝ),den t*pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2 := by
        simpa only [Xcell,W₁,W₂,star_star] using hsep
      obtain ⟨sector,hsector⟩ := actual_second_varying_balanced_profile_children p hp hcop hg hpr (σ:=σ) Q hsCell
      have he := hsector pool Ψ₀ m z slots₁ slots₁ (fun x i=>lists i\deleted x) (fun x i=>lists i\deleted x) a a W₁ W₂ ω₁ ω₂ rowMajorant Gcell Ecell Vcell Bcell Xcell Y Rc L
        (fun i y => U₀ i (y+ρ i)) den w' hG hE hV hB hXcell hDensity hsep' hrowsCell hω₁ hω₂ hcut
      have hpow (H : ℝ) : Z^(max 0 Ncell+(Vlabel d))*(A*Z^(max 0 Ncell+(Vlabel d)+εchild)*H) =
          (A*Z^(2*(max 0 Ncell+(Vlabel d))+εchild))*H := by
        calc
          _ = A*(Z^(max 0 Ncell+(Vlabel d))*Z^(max 0 Ncell+(Vlabel d)+εchild))*H := by ring
          _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring_nf
      have hb := actual_second_deleted_all_modes_integral p hp hcop hg hpr hinj hc Q hsCell sector pool Ψ₀ hΨ₀ m z
        slots₁ slots₁ lists lists a a deleted deleted hdel hdel ha₁ ha₂ ω₁ ω₂ Gcell Ecell Vcell Bcell Xcell Rc (labels d) (hlabels d hd) hrowsCell
        K ho hslots₁ hslots₁ w' (fun x hx => hw x (hin hx)) (A*Z^(2*(max 0 Ncell+(Vlabel d))+εchild)) (by positivity) J den hWeighted
        (by
          intro t J₁ hJ₁ γ hγ
          rw [second_left_normalized_energy p hp hcop hg K ((labels d).filter Squarefree)
            (nonzeroChildFrequencyBall 1 Rc) γ pool Ψ₀ m z (slots₁\J₁) lists a ω₁ Z Ncell (Vlabel d) hz t]
          rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayMinus Ψ₀ z)
            (actualSecondInheritedPuncture m γ)]
          exact (mul_le_mul_of_nonneg_left ((hleft d hd) t J₁ hJ₁ γ hγ) (Real.rpow_pos_of_pos hz _).le).trans_eq (hpow _))
        (by
          intro t J₂ hJ₂ γ hγ
          rw [second_right_normalized_energy p hp hcop hg K ((labels d).filter Squarefree)
            Rc γ pool Ψ₀ m z (slots₁\J₂) lists a ω₂ Z Ncell (Vlabel d) hz t]
          rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayPlus Ψ₀ z)
            (actualSecondInheritedPuncture m γ)]
          exact (mul_le_mul_of_nonneg_left ((hright d hd) t J₂ hJ₂ γ hγ) (Real.rpow_pos_of_pos hz _).le).trans_eq (hpow _))
      have hIntegral : (∫ t : Frequency × (Fin 6 → ℝ),den t *
          ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector Q sector uv,
            (w' x*actualSecondSignedWeight p hp hcop hg Ψ₀
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
              ∑ J₁∈slots₁.powerset,∑ J₂∈slots₁.powerset,
                secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ₀ m z slots₁ slots₁ J₁ J₂ (fun i=>lists i\deleted x) (fun i=>lists i\deleted x) a a
                  ω₁ ω₂ Gcell Ecell Vcell Bcell Xcell t) =
          ∫ t : Frequency × (Fin 6 → ℝ),den t*secondDeletedFullModeSum p hp hcop hg Q sector pool Ψ₀ m z
            slots₁ slots₁ lists lists a a deleted deleted ω₁ ω₂ Gcell Ecell Vcell Bcell Xcell w' t := by
        apply integral_congr_ae
        filter_upwards with t
        rw [secondDeletedFullModeSum_physical]
      rw [hIntegral] at he
      have hexp : Real.exp (6*L)*Real.exp (-6*L) = 1 := by
        rw [←Real.exp_add]
        ring_nf
        exact Real.exp_zero
      have hn := congrArg norm he
      conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      conv_rhs at hn => rw [norm_mul]
      have hn' := congrArg (fun a : ℝ => Real.exp (6*L)*a) hn
      rw [←mul_assoc,hexp,one_mul] at hn'
      rw [←mul_assoc] at hn'
      have hpref : 0 ≤ Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((Ecell*Vcell*Xcell : ℝ):ℂ)⁻¹‖ := by positivity
      have henergy := mul_le_mul_of_nonneg_left hb hpref
      have hMomentBound := (show (∫ t : Frequency × (Fin 6 → ℝ),
          tripleHeight J t.1*coordinateHeight J t.2*‖den t‖) ≤
          Cp*((1+‖-θ‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ‖)^InverseClippingProfiles.momentOrder J) from by
        simpa only [pow_zero,one_mul,den,gRoot,f₁,f₂,ambientWeight,tripleHeight,coordinateHeight] using hMoment)
      have hm := hmassCell p hp Q 1 1 Z ell Ractive j tcount (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hz
        hsCell.quotient_nonzero hsCell.second_divisor (fun x hx => hcube₁ x (hin hx)) (fun x hx => hcube₂ x (hin hx)) (fun x hx => hactive x (hin hx)) (fun x hx => hj x (hin hx)) (fun x hx => hquot x (hin hx)) hcommon hdiv
      have hfac : 0 ≤ 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₁.card*(A*Z^(2*(max 0 Ncell+(Vlabel d))+εchild)) := by positivity
      have hb := mul_le_mul (mul_le_mul_of_nonneg_left hm hfac) hMomentBound
        (integral_nonneg (fun _ => by unfold tripleHeight coordinateHeight; positivity)) (by positivity)
    
      have hest := (le_of_eq hn').trans (henergy.trans (mul_le_mul_of_nonneg_left hb hpref))
      dsimp only [Gcell,Ecell,Vcell,Bcell,Xcell,Ncell] at hest
      rw [second_cell_physical_scale Z X d hZ hX] at hest
      refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_))
        (hest.trans_eq (by dsimp only [C,θ,Rc]; ring))
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      exact actual_priority_profile_common p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        slots₁ slots₁ _ _ a a om lo hi hlo hsupport negative t rowMajorant Y X hX
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
