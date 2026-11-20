module
public import OAI.NumberTheory.DirichletL.Descent.PriorityCellEnergy
public import OAI.NumberTheory.DirichletL.Descent.PriorityCellEnergyWindowOrder
public import OAI.NumberTheory.DirichletL.Descent.PriorityMovingRadius
public import OAI.NumberTheory.DirichletL.Descent.PriorityMovingRadiusWindowOrder
public import OAI.NumberTheory.DirichletL.Descent.PriorityRetainedMovingRadiusWindowOrder
public import OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
public import OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource
public import OAI.NumberTheory.DirichletL.Descent.SecondBlockEnergyWindowOrder
public import OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
public import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingEnergy
public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingMass
public import OAI.NumberTheory.DirichletL.Descent.SecondDeletedPhysicalRecursive
public import OAI.NumberTheory.DirichletL.Descent.SecondOriginalMass
public import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation InverseInitialClippedColumns InverseSecondFibers
open JointLogSeparation MeasureTheory InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_retained_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
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
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  let gwin:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hmg:0≤mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hgwin:Function.support gwin⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile gwin)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hgwin
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  let g₁ := conjugateProfile gwin
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ gwin mg mg 1 (fun _=>1) (fun _=>2) B₀
      hmg hmg (le_refl 1) hcg hgwin (fun _=>zero_lt_one) (fun _=>by norm_num) hB₀
  refine ⟨ω₁,ω₂,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,?_⟩
  intro J
  obtain ⟨Cp,hCp,hmeasure⟩ := InverseSecondProfileUniform.second_profile_common_measure
    U₀ g₁ gwin Φ M₀ B₀ mg mg 1 hM hB₀ hUs hcg hgwin 0 J
  obtain ⟨Cm,hCm,hdivisorMass⟩ := actual_second_original_mass K εmass hεmass
  let C := Cp*Cm
  have hC : 0 ≤ C := mul_nonneg hCp hCm.le
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have he :
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤ D*S := by
    dsimp only [S]
    have hz:0<Z:=zero_lt_one.trans hZ
    have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
    rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      deleted₁ deleted₂ w]
    rw [Finset.mul_sum]
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
    let rows := cell p source d
    have hrows' : ∀ x ∈ rows, x.second.frequency ∈
        nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R d) := by
      intro x hx
      simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)
    have hcut' : ∀ x∈rows, index p x=d := fun x hx=>(mem_cell p source d x).mp hx |>.2
    have hblock:=actual_source_block_ratios p hp rows d hcut'
      (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows' x hx))
    let N := secondCellColumnExponent Z X d
    let G := scales d 0
    let E := scales d 1
    let Vcell := scales d 2
    let B := scales d 3
    let Xcell := Z^N
    let θ := priorityHeight negative t
    have hG : 0 < G := dyadScale_pos _
    have hE : 0 < E := dyadScale_pos _
    have hV : 0 < Vcell := dyadScale_pos _
    have hB : 0 < B := dyadScale_pos _
    have hXcell : 0 < Xcell := Real.rpow_pos_of_pos hz _
    obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp rows pool Ψ m z G E Vcell B (Z^N) ρ 1 1 (-θ) θ
      hG hE hV hB hXcell hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hblock
    have hRad : 0 < Y*B/(E*Vcell^2*(Z^N)^2) := by positivity
    obtain ⟨b₃,hb₃⟩ := hmeasure (Y*B/(E*Vcell^2*(Z^N)^2)) hRad
    obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ 1 1 (-θ) θ L hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL
    let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.secondBalancedSlope i) (hUs i)
    let f₁ := rooted g₁ mg (-(1/2:ℝ)) hcg
    let f₂ := rooted gwin mg (-(1/2:ℝ)) hgwin
    let den := density g f₁ f₂ b₃ ρ 1 1 (-θ) θ L
    have hden : Integrable den := balanced_density_integrable g f₁ f₂ b₃ ρ 1 1 (-θ) θ L
    have hphysical := actual_second_deleted_physical_recursive p hp hcop hg hpr hinj hc rows (cell_conditions p source hs d)
      pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      (fun x => star (positiveSource g₁ 1 (-θ) x)) (positiveSource gwin 1 θ) ω₁ ω₂ Φ
      G E Vcell B Y (R d) L Z N (Vlabel d) εchild (fun i y => U₀ i (y+ρ i)) den w (labels d) K J A
      (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hz hG hE hV hB hXcell hden (by simpa only [star_star] using hsep)
      hrows' hω₁ hω₂ hcut hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA hWeighted (hleft d hd) (hright d hd)
    have hdMoment : (∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖den t‖) ≤
        Cp*((1+‖(-θ)‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ‖)^InverseClippingProfiles.momentOrder J) /
            (1+Y*B/(E*Vcell^2*(Z^N)^2))^0 := by
      apply (le_div_iff₀ (by positivity)).mpr
      exact (mul_comm _ _).le.trans hMoment
    have he := hphysical.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdMoment (mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))) (by positivity))
    have hsCell := cell_conditions p source hs d
    have hm := hdivisorMass p hp rows 1 1 Z ell Ractive j tcount (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hz
      hsCell.quotient_nonzero hsCell.second_divisor (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx)) (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx)) hcommon hdiv
    have hfac : 0 ≤ 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+(Vlabel d))+εchild)) := by positivity
    have hh : 0 ≤ Cp*((1+‖(-θ)‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ‖)^InverseClippingProfiles.momentOrder J) /
          (1+Y*B/(E*Vcell^2*(Z^N)^2))^0 := by positivity
    have hpref : 0 ≤ Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*Vcell*(Z^N):ℝ):ℂ)⁻¹‖ := by positivity
    have hb := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hh) hpref
    have hcell := he.trans hb
    rw [second_cell_physical_scale Z X d hZ hX] at hcell
    refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) (hcell.trans_eq ?_)
    · apply Finset.sum_congr rfl
      intro x _hx
      exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m * ConcretePrimeRowBridge.idealGenerator x.quotient) z x) * v)
        (actual_priority_profile_common p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
          slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)
    · dsimp only [Vcell,E,N,θ]
      simp only [pow_zero,div_one,hheight,hVe d]
      dsimp only [D,C,priorityCellScalar,secondCount]
      ring
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
