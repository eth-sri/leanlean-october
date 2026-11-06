module
public import OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenLiveDescent
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenLiveSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter SevenEighths.CenteredMomentSecondUniformSubsetSource SevenEighths.CenteredMomentSecondNonexceptionalScalar

namespace SevenEighths.CenteredMomentSecondFrozenUniformSubset
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondActivePhysicalDictionary CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson CenteredMomentLogDyadic MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost


abbrev ChildBound₁ {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R0 Q : Ideal O) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (τ : (q : ActiveLabel S β) → Finset (CommonIndex q.val.1 q.val.2) → RayCharacter → Character)
    (χ₀ : RayCharacter) (m : O) (W : 𝓢(ℝ, ℂ)) (Kphys Tsec Z ξ : ℝ)
    (env : ∀ q₁ q₂ : Ideal O, Finset (CommonIndex q₁ q₂) → (Fin 4 → ℤ) → ℝ)
    (E₁ : ℝ) (J₁ : ℕ) : Prop :=
  ∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
    ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
    physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
      (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
      (fun i=>(n i:ℤ))≠0→
    ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
    (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
    ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
    frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
    ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
    childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
      (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
        E₁*env q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
        (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁)

abbrev ChildBound₂ {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R0 Q : Ideal O) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (τ : (q : ActiveLabel S β) → Finset (CommonIndex q.val.1 q.val.2) → RayCharacter → Character)
    (χ₀ : RayCharacter) (m : O) (W : 𝓢(ℝ, ℂ)) (Kphys Tsec Z ξ : ℝ)
    (env : ∀ q₁ q₂ : Ideal O, Finset (CommonIndex q₁ q₂) → (Fin 4 → ℤ) → ℝ)
    (E₂ : ℝ) (J₂ : ℕ) : Prop :=
  ∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
    ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
    physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
      (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
      (fun i=>(n i:ℤ))≠0→
    ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
    (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
    ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
    frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
    ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
    childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
      (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
        E₂*env q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
        (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂)

theorem original_subsets_source_descent {κ : Type*} [Fintype κ] (t₀ : κ)
    (sub : κ → Type*) [∀ T, Fintype (sub T)] [∀ T, DecidableEq (sub T)] (valOf : ∀ T, sub T → ι)
    (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : κ, ∀(s:Input (sub T))(p:Profiles wlo whi),(∀i,s.lo i=lo (valOf T i)) → (∀i,s.hi i=hi (valOf T i)) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    ChildBound₁ s R0 Q S β τ χ₀ m W Kphys Tsec Z ξ (childEnvelope s.η) E₁ J₁ →
    ChildBound₂ s R0 Q S β τ χ₀ m W Kphys Tsec Z ξ (childEnvelope s.η) E₂ J₂ →
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i:sub T,hi (valOf T i))*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving) := by
  have hall (T : κ) := CenteredMomentSecondFrozenLiveDescent.original_source_descent
    wlo whi hwlo hwhi (fun i:sub T=>lo (valOf T i)) (fun i:sub T=>hi (valOf T i)) (fun i=>hhi (valOf T i))
    W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  choose J Sp Sf hSp Cm Ce Cd Ct hCm hCe hCd hCt hbound using hall
  let J0 : ℕ := ∑T:κ,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  let Cm0 : ℝ := 1+∑T:κ,Cm T
  let Ce0 : ℝ := 1+∑T:κ,Ce T
  let Cd0 : ℝ := 1+∑T:κ,Cd T
  let Ct0 : ℝ := 1+∑T:κ,Ct T
  have sum_pos (f : κ→ℝ) (hf : ∀T,0≤f T) : 0<1+∑T:κ,f T := by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset κ))=>hf T)
    linarith
  have sum_le (f : κ→ℝ) (hf : ∀T,0≤f T) (T : κ) : f T≤1+∑U:κ,f U := by
    have hh:=Finset.single_le_sum (fun U (_:U∈(Finset.univ:Finset κ))=>hf U) (Finset.mem_univ T)
    linarith
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨t₀,Finset.mem_univ _,hSp t₀⟩,
    Cm0,Ce0,Cd0,Ct0,sum_pos Cm (fun T=>(hCm T).le),(sum_pos Ce hCe).le,
    sum_pos Cd (fun T=>(hCd T).le),sum_pos Ct (fun T=>(hCt T).le),?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T=>hbound T Q hQ hQt hQ72
  let K0 : ℝ := 1+∑T:κ,K T
  refine ⟨K0,sum_pos K (fun T=>(hK T).le),?_⟩
  have heall : ∀ᶠ Z : ℝ in atTop, ∀T:κ,_ := Filter.eventually_all.mpr hev
  filter_upwards [heall] with Z hZ
  refine ⟨(hZ t₀).1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=(hZ T).2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hsp : Sp T⊆Sp0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hsf : Sf T⊆Sf0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hj : J T≤J0 := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcm:=sum_le Cm (fun T=>(hCm T).le) T
  have hce:=sum_le Ce hCe T
  have hcd:=sum_le Cd (fun T=>(hCd T).le) T
  have hct:=sum_le Ct (fun T=>(hCt T).le) T
  have hfactor:=factor_mono hsp s p hj Q (hK T).le (sum_le K (fun T=>(hK T).le) T)
  have hfn:=profileFactor_nonneg (Sp T) s p (J T) Q (K T) (hK T).le
  have hphi : (Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤Sf0.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := Seminorm.le_def.mp (Finset.sup_mono hsf) W
  have hz : 0≤Z := (hZ T).1.le.trans' zero_le_one
  have hp:=profileCost_nonneg s
  have hm1:=profileMoment_nonneg J₁
  have hm2:=profileMoment_nonneg J₂
  have he:=heightEnvelope_pos s.t
  have hsn : 0≤(seed.absNorm:ℝ) := by positivity
  have hvol:=CenteredMomentSourceInputTailUniform.volume_pos s
  have hc : 0≤(Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hCm0 : 0≤Cm0 := (sum_pos Cm (fun T=>(hCm T).le)).le
  have hCe0 : 0≤Ce0 := (sum_pos Ce hCe).le
  have hCd0 : 0≤Cd0 := (sum_pos Cd (fun T=>(hCd T).le)).le
  have hCt0 : 0≤Ct0 := (sum_pos Ct (fun T=>(hCt T).le)).le
  have hprodhi : 0≤∏i:sub T,hi (valOf T i) := Finset.prod_nonneg (fun i _=>hhi (valOf T i))
  have hprodlo : 0≤∏i:sub T,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  apply hh.trans
  gcongr
