module

public import OAI.NumberTheory.DirichletL.Moments.FirstSecondActiveErrorGates
public import OAI.NumberTheory.DirichletL.Moments.SecondReferenceNormalization
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalScalar
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
public import OAI.NumberTheory.DirichletL.Moments.SecondUniformSubsetSource
public import OAI.FiniteMajorant
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenLiveSource
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceSeededPowerDescent
public import OAI.NumberTheory.DirichletL.Moments.SecondSourcePowerDescent
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalUniformSource
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceDiagonal
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform
public import OAI.NumberTheory.DirichletL.Moments.SecondLocalization
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSeededGaussianPower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondNonexceptionalAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit
open CenteredMomentActiveSource CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentExceptionalAmplitudePair CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondWindowBudget CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondFrozenLiveSource
open Filter MeasureTheory
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentSmooth CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentForcing
open CenteredMomentChildRows CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondDyadicRowSupport
open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving ConcretePrimeRowBridge CenteredMomentMobiusRegroup
open CenteredMomentSupportedCorrelation CenteredMomentSupport CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondDivisorSupport
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource
open CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic MeasureTheory UniqueFactorizationMonoid
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

open CenteredMomentAmplificationChildInput CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput

open CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondUniformSubsetSource

/-- A two-level family of finite slot sets, used for the error terms. -/
abbrev NestedIndex (ι : Type*) := Σ T : Finset ι, Finset T

lemma normalized_source_le_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource s R seed W K≤
      ‖sourceGaussEnergy (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) (heightCoeff s.η s.t) W K‖/
          CenteredMomentAmplificationChildInput.volume s := by
  exact div_le_div_of_nonneg_right (Complex.re_le_norm _)
    (CenteredMomentAmplificationChildInput.volume_pos s).le

section Family

variable {ι κ : Type*} [Fintype κ]
variable (slots : κ → Type*) [∀ T, Fintype (slots T)] [∀ T, DecidableEq (slots T)]
variable (label : ∀ T, slots T → ι) (base : κ)

include base in
set_option maxHeartbeats 600000 in
theorem source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    WithFrozenGaussianConstants fun J Sprofile SΦ Cmain Cexc Cdiag Ctail Q Kc Z =>
      ∀T : κ, ∀(s:Input (slots T))(p:Profiles wlo whi),(∀i,s.lo i=lo (label T i)) → (∀i,s.hi i=hi (label T i)) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      WithFrozenCharacters s R0 seed fun S β τ =>
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    FrozenColumnBound s S β τ χ₀ Q R0 m W Kphys Tsec Z ξ Prod.fst (childEnvelope s.η) E₁ J₁→
    FrozenColumnBound s S β τ χ₀ Q R0 m W Kphys Tsec Z ξ Prod.snd (childEnvelope s.η) E₂ J₂→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i:slots T,hi (label T i))*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving)  := by
  choose Cm hCm hmain using fun T : κ =>
    CenteredMomentSecondFrozenLiveSource.original_nonexceptional_energy
      (fun i : slots T => lo (label T i)) (fun i => hi (label T i)) W J₁ J₂
      B B 1 δ ε hB hB zero_lt_one hδ hε
  choose J Sp hSp Ce hCe hexc using fun T : κ =>
    CenteredMomentSecondExceptionalUniformSource.original_exceptional_energy wlo whi hwlo hwhi
      (fun i : slots T => lo (label T i)) (fun i => hi (label T i)) W ε δ θ B hε hδ hθ hB
  choose Sf Ct hCt htail using fun T : κ =>
    second_input_tail_arbitrary_saving (fun i : slots T => hi (label T i)) wlo whi B ξ saving
      (fun i => hhi (label T i)) hwlo hwhi hB hξ
  let N : ℕ := ∑T : κ, Fintype.card (slots T)
  obtain ⟨Cd0,hCd0,hdiag⟩ := CenteredMomentSecondSourceDiagonal.actual_second_zero N ε hε
  let J0 : ℕ := ∑T:κ,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  obtain ⟨Cm0, hCm0, hcm⟩ := exists_real_majorant 0 Cm
  obtain ⟨Ce0, hCe0, hce⟩ := exists_real_majorant 0 Ce
  obtain ⟨Ct0, hCt0, hct⟩ := exists_real_majorant 0 Ct
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨base,Finset.mem_univ _,hSp base⟩,
    Cm0,Ce0,Cd0,Ct0,hCm0,hCe0.le,hCd0,hCt0,?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T => hexc T Q hQ hQt hQ72
  obtain ⟨K0,hK0,hKK⟩ := exists_real_majorant 0 K
  refine ⟨K0,hK0,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmain, Filter.eventually_all.mpr hev, Filter.eventually_all.mpr htail] with Z hmZ heZ htZ
  refine ⟨(hmZ base).1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  let S := finiteColumns (Fintype.piFinset s.pools)
  let β := coefficient s R0 seed
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  obtain ⟨τ,hfamily,hchild⟩:=(hmZ T).2 s hlo hhis hz1 hz2 hH0 hH R0 seed hseed hseed0
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂
    hleft hright r hX1 hX2 hY1 hY2
  have hn:=hchild χ₀ Q m hQ72 hm hml hm2 Kphys Tsec ξ hKphys
    (by simpa only [one_mul] using hRcap) E₁ E₂ hE₁ hE₂ hleft hright
  have he:=sourceGaussEnergy_localized s.η s.t S β W Kphys Tsec Z ξ hKphys
  rw [original_energy_split s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s) hKphys (fun I _ hn=>(original_column_norm s R0 seed I hz1 hz2 hn).2)] at he
  have hd:=hdiag (Finset.single_le_sum (f := fun U : κ => Fintype.card (slots U)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ T) : Fintype.card (slots T) ≤ N) wlo whi hwlo hwhi s p hw1 hw2 R0 seed hseed0
    ((Kphys:ℂ)*paperRadialFourier W 0)
  have hhiEq:(∏i,max 0 (s.hi i))=∏i:slots T,hi (label T i):=by
    apply Finset.prod_congr rfl
    intro i _
    rw [hhis i,max_eq_right (hhi (label T i))]
  rw [hhiEq] at hd
  have hex:=(heZ T).2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap r hX1 hX2 hY1 hY2
  have ht:=(htZ T).2 s (p.profile 0) (p.profile 1) hw1 hw2 (p.support 0) (p.support 1)
    (fun i=>(hhis i).le) R0 seed W Kphys Tsec hKphys hVcap hTcap hnom
  have hsp : Sp T⊆Sp0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hsf : Sf T⊆Sf0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hj : J T≤J0 := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hfactor:=factor_mono hsp s p hj Q (hK T).le (hKK T)
  have hfn:=profileFactor_nonneg (Sp T) s p (J T) Q (K T) (hK T).le
  have hphi : (Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤Sf0.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := Seminorm.le_def.mp (Finset.sup_mono hsf) W
  have hz : 0≤Z := (hmZ T).1.le.trans' zero_le_one
  have hp:=profileCost_nonneg s
  have hm1:=profileMoment_nonneg J₁
  have hm2:=profileMoment_nonneg J₂
  have hheight:=heightEnvelope_pos s.t
  have hsn : 0≤(seed.absNorm:ℝ) := by positivity
  have hvol:=CenteredMomentSourceInputTailUniform.volume_pos s
  have hc : 0≤(Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hprodhi : 0≤∏i:slots T,hi (label T i) := Finset.prod_nonneg (fun i _=>hhi (label T i))
  have hprodlo : 0≤∏i:slots T,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  have hCm0' := hCm0.le
  have hCe0' := hCe0.le
  have hCd0' := hCd0.le
  have hCt0' := hCt0.le
  have htri (a b c d : ℂ) : ‖a+(c+b)+d‖ ≤ ‖b‖+‖a‖+‖c‖+‖d‖ :=
    (norm_add_le (a+(c+b)) d).trans (by linarith only [norm_add_le a (c+b), norm_add_le c b])
  have hs := div_le_div_of_nonneg_right
    (htri (((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t)
      (partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
      (partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
      (secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ)) hvol.le
  rw [←he] at hs
  simp only [add_div] at hs
  have hh := hs.trans (add_le_add (add_le_add (add_le_add hn hd) hex) ht)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hKphys, ←mul_assoc] at hh
  apply hh.trans
  simp only [add_assoc, ←mul_assoc]
  gcongr <;> first | exact hcm T | exact hce T | exact hct T

/-- Admissible input profiles, support bounds and seeds for the Gaussian descent. -/
abbrev AcrossSeededInputs (lo hi : ι → ℝ) (N : ℕ)
    (b b₁ b₂ wlo whi Z B Bseed : ℝ)
    (Goal : (T : κ) → Input (slots T) → Profiles wlo whi → ℝ → Ideal O → Ideal O → Prop) : Prop :=
  ∀T : κ, ∀(s:Input (slots T))(p:Profiles wlo whi),(∀i,s.lo i=lo (label T i)) → (∀i,s.hi i=hi (label T i)) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card (slots T)≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B → Goal T s p A R0 seed

include base in
theorem actual_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    WithFrozenGaussianConstants fun J Sprofile SΦ Cmain Cexc Cdiag Ctail Q Kc Z =>
      AcrossSeededInputs slots label lo hi N b b₁ b₂ wlo whi Z B Bseed fun T s p A R0 seed =>
      WithFrozenCharacters s R0 seed fun S β τ =>
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    FrozenColumnBound s S β τ χ₀ Q R0 m W Kphys Tsec Z ξ Prod.fst (referenceEnvelope qref) E₁ J₁ →
    FrozenColumnBound s S β τ χ₀ Q R0 m W Kphys Tsec Z ξ Prod.snd (referenceEnvelope qref) E₂ J₂ →
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    normalizedGaussSource s R0 seed W Kphys≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    source_descent slots label base
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  let S := finiteColumns (Fintype.piFinset s.pools)
  let β := coefficient s R0 seed
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hq:0<(s.η.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ s.η.modulus_ne_bot
  have hr:0≤qref/(s.η.modulus.absNorm:ℝ):=div_nonneg hqref.le hq.le
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap
    (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂)
    (mul_nonneg hr hE₁) (mul_nonneg hr hE₂)
  have hh := hh
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hleft q hq U n hn D0 hD hcap hs χ v b hb a ha)
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hright q hq U n hn D0 hD hcap hs χ v b hb a ha)
    r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂) r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂) r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [CenteredMomentFirstChildProfileControl.mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  apply (normalized_source_le_norm s R0 seed W Kphys).trans
  apply hh'.trans
  have h := source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi (label T i)) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha
  simpa only [a, seededFactors_rescale Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ)
    J₁ J₂ Sf W hq hqref.le] using h

end Family

end SevenEighths.CenteredMomentSeededGaussianPower

end

end OAI
