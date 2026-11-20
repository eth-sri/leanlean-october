module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUnits
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerBranch
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerMass
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUniform

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerReference
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource InverseInitialEnergyCallerCanonical
open InverseInitialEnergyCallerOpposite InverseInitialProfile InverseInitialEnergyCallerAllocation
open InverseInitialEnergyCallerAssigned InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialEnergyCallerBranch InverseInitialEnergyCallerUnits InverseInitialEnergyCallerAllSlots
local notation "Eis"=>ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

set_option maxHeartbeats 1000000 in
theorem actual_physical_reference_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂) :
    ∃(fresh₁ fresh₂:𝓢(ℝ,ℂ)),
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₁:ℝ→ℂ) ∧
        tsupport (fresh₁:ℝ→ℂ)⊆Set.Icc af bf) ∧
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₂:ℝ→ℂ) ∧
        tsupport (fresh₂:ℝ→ℂ)⊆Set.Icc af bf) ∧
    ∀(J N:ℕ)(U π:ℝ),0≤U→0<π→∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[OAI.PrincipalFamily.Maximal p]
      (hcop:OAI.PrincipalFamily.Coprime p)
      (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (Z D B v θ H R m η:ℝ)(_hZ:1<Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A ε:ℝ)(_hA:0≤A)
      (_hδ:max 0 (columnCenter D B v)-columnCenter D B v≤3*η)
      (_hF:F=D-B+θ+(max 0 (columnCenter D B v)-columnCenter D B v))
      (_hReq:R=B-θ+2*η)
      (_hmoment:∀s:ℝ,∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₁ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₂ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+11*η+π+ε)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
  obtain ⟨fresh₁,af₁,bf₁,haf₁,hab₁,hc₁,hsf₁,hu₁⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₁ lo b hlo hb hω₁ hd₁
  obtain ⟨fresh₂,af₂,bf₂,haf₂,hab₂,hc₂,hsf₂,hu₂⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₂ lo b hlo hb hω₂ hd₂
  refine ⟨fresh₁,fresh₂,⟨af₁,bf₁,haf₁,hab₁,hc₁,hsf₁⟩,⟨af₂,bf₂,haf₂,hab₂,hc₂,hsf₂⟩,?_⟩
  intro J N U π hU hπ
  obtain ⟨C₁,hC₁,hh₁⟩ := hu₁ J
  obtain ⟨C₂,hC₂,hh₂⟩ := hu₂ J
  obtain ⟨Cq,hCq,hmass⟩ := InverseInitialEnergyCallerMass.assigned_quotient_mass (2*N) U π hU hπ
  let rayMass : ℝ := ∑ρ:SecondRayIndex,‖secondRayCoefficient ρ‖
  let Ce : ℝ := (6 * (Cq*4^N)) * (1+rayMass)
  have hCe : 0 < Ce := by dsimp [Ce,rayMass]; positivity
  obtain ⟨Cp,hCp,hprofile⟩ := initial_physical_family_common_measure
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox 0 (4*J)
  refine ⟨Ce*(Cp+1)*(C₁+C₂),by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A ε hA hδ hF hReq hmoment
  have hZp : 0<Z := zero_lt_one.trans hZ
  let A' := (C₁+C₂)*(A*Z^(F+ε))
  have hrawMom : ∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,
      ∀J₁∈slots.powerset,∀J₂∈slots.powerset,∀t∈quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤A'*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) ∧
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤A'*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
    intro z ρ J₁ hJ₁ J₂ hJ₂ t ht
    have hb₁ := hh₁ p hp hcop hg hpr pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
      (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (-leftHeight z)
      hZ (by positivity) (Or.inl rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).1)
    have hb₂ := hh₂ p hp hcop hg hpr pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
      (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (rightHeight z)
      hZ (by positivity) (Or.inr rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [leftHeight_eq] at hb₁
    rw [rightHeight_eq] at hb₂
    have hh : 0≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
      dsimp [tripleHeight,coordinateHeight];positivity
    constructor
    · apply hb₁.trans
      dsimp only [A']
      gcongr <;> linarith
    · apply hb₂.trans
      dsimp only [A']
      gcongr <;> linarith
  let Jphys := 4*J
  obtain ⟨b₃,hb₃⟩ := hprofile Z D B v m θ H η hZp hη
  obtain ⟨hid,hint,hprofileBound⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  let g := secondRootSchwartz V hV hS
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a₀ b₀ ha₀ hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a₀ b₀ ha₀ hs₂ hW₂
  let L := η*Real.log Z
  let E (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) := A'*(tripleHeight Jphys z.1*coordinateHeight Jphys z.2)
  have hE (z) : 0 ≤ E z := by dsimp [E,tripleHeight,coordinateHeight]; positivity
  have hmode (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) (ρ : SecondRayIndex) (u : Eisˣ) :
      ‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤(Cq*4^N)*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E z := by
    have hEz := hE z
    let S' := sourceSector p hp hpr S u
    have hs : S' ⊆ S := Finset.filter_subset _ _
    have hu (x) (hx : x ∈ S') := (Finset.mem_filter.mp hx).2
    have hdiv' x (hx : x ∈ S') := hdiv x (hs hx)
    have hw' x (hx : x ∈ S') := hw x (hs hx)
    have hn' t (ht : t ∈ quotientSet p S') := hn t (quotientSet_mono p hs ht)
    have hchild' x (hx : x ∈ S') := by
      have hh := hchild x (hs hx)
      rw [hu x hx] at hh
      exact hh
    have hmoment' J₁ hJ₁ J₂ hJ₂ t ht  := hrawMom z ρ J₁ hJ₁ J₂ hJ₂ t
      (quotientSet_mono p hs (InverseInitialEnergyCallerMass.assigned_quotient_subset
        p S' J₁ J₂ lists lists ht))
    let bound := Cq*‖secondRayCoefficient ρ‖*Z^(F+R+π)*(E z)
    have hb (J₁:Finset σ)(hJ₁:J₁∈slots.powerset)(J₂:Finset σ)(hJ₂:J₂∈slots.powerset) :
        ‖∑x∈S',w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z‖≤bound := by
      have h₁ := Finset.mem_powerset.mp hJ₁
      have h₂ := Finset.mem_powerset.mp hJ₂
      have he := actual_allocated_mode_bound p hp hcop hg hinj hpr hc S' u hdiv' pool Ψ hΨ j
        slots J₁ J₂ lists a (fun i hi=>ha i (h₁ hi)) (fun i hi=>ha i (h₂ hi)) ω₁ ω₂
        Z D B v θ H hZp ρ z w hw' labels rows hlabels hneg hchild' F (E z) (E z)
        (fun t ht=>(hmoment' J₁ hJ₁ J₂ hJ₂ t ht).1)
        (fun t ht=>(hmoment' J₁ hJ₁ J₂ hJ₂ t ht).2)
      rw [Real.mul_self_sqrt (hE z)] at he
      have hJ : J₁.card+J₂.card≤2*N := by
        have := (Finset.card_le_card h₁).trans hslots
        have := (Finset.card_le_card h₂).trans hslots
        omega
      have hm := hmass p hp S' J₁ J₂ lists lists hJ Z R hZ.le hR hn'
      apply he.trans
      calc
        _≤‖secondRayCoefficient ρ‖*(Z^F*(Cq*Z^(R+π)))*(E z) := by gcongr
        _=bound := by dsimp only [bound];rw [add_assoc F R π,Real.rpow_add hZp F (R+π)];ring
    rw [rowMode_sum_allocations p hp hcop hg hpr S' hdiv' u hu]
    calc
      _≤∑J₁∈slots.powerset,∑J₂∈slots.powerset,
          ‖∑x∈S',w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
            Z D B v θ H x ρ z‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun Jphys hJ=>norm_sum_le _ _)
      _≤∑_J₁∈slots.powerset,∑_J₂∈slots.powerset,bound :=
        Finset.sum_le_sum fun J₁ hJ₁=>Finset.sum_le_sum fun J₂ hJ₂=>hb J₁ hJ₁ J₂ hJ₂
      _=(4:ℝ)^slots.card*bound := by
        simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
        ring
      _≤(4:ℝ)^N*bound := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hslots) (by dsimp [bound];positivity)
      _=_ := by ring
  have hunit (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) (ρ : SecondRayIndex) :
      ‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤(6*(Cq*4^N))*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E z := by
    rw [sourceSector_partition p hp hpr S]
    calc
      _≤∑u:Eisˣ,‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H x ρ z‖ := norm_sum_le _ _
      _≤∑_u:Eisˣ,(Cq*4^N)*‖secondRayCoefficient ρ‖*Z^(F+R+π)*(E z) := Finset.sum_le_sum fun u _=>hmode z ρ u
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,unit_sector_card,nsmul_eq_mul];norm_num;ring
  have hray (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) :
      ‖∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤Ce*Z^(F+R+π)*E z := by
    have hEz := hE z
    rw [Finset.sum_comm]
    calc
      _≤∑ρ:SecondRayIndex,‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
          Z D B v θ H x ρ z‖ := norm_sum_le _ _
      _≤∑ρ:SecondRayIndex,(6*(Cq*4^N))*‖secondRayCoefficient ρ‖*Z^(F+R+π)*(E z) := Finset.sum_le_sum fun ρ _=>hunit z ρ
      _=(6*(Cq*4^N))*rayMass*Z^(F+R+π)*(E z) := by simp only [←Finset.sum_mul,←Finset.mul_sum,rayMass]
      _≤Ce*Z^(F+R+π)*(E z) := by
        dsimp only [Ce]
        gcongr
        linarith
  have hb : ‖∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
        familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z*
        (∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
          Z D B v θ H x ρ z)‖≤
        Ce*Z^(F+R+π)*A'*(∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
          tripleHeight Jphys z.1*coordinateHeight Jphys z.2*‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
    calc
      _≤∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
        (Ce*Z^(F+R+π)*A')*(tripleHeight Jphys z.1*coordinateHeight Jphys z.2*
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
        apply norm_integral_le_of_norm_le
          ((familyDensity_weighted_integrable g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L Jphys).const_mul _)
        filter_upwards with z
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hray z) (norm_nonneg _)).trans_eq (by ring)
      _=_ := integral_const_mul _ _
  have hprof : (∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      tripleHeight Jphys z.1*coordinateHeight Jphys z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖)≤
      (Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder Jphys*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder Jphys) := by
    simp only [pow_zero,one_mul] at hprofileBound
    exact hprofileBound.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  rw [physicalBlock_rectangular_common_measure p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid pool S hdiv hf w Ψ j slots lists a ω₁ ω₂ hsupport]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZp _)]
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZp.le _)).trans
  calc
    _≤Z^(prefactorCenter m D B θ+3*η)*
      (Ce*Z^(F+R+π)*A'*((Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder Jphys*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder Jphys))) := by gcongr
    _ = Ce*(Cp+1)*(C₁+C₂)*Z^(prefactorCenter m D B θ+3*η+(F+R+π)+(F+ε))*A*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder Jphys*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder Jphys) := by
      rw [Real.rpow_add hZp _ (F+ε), Real.rpow_add hZp (prefactorCenter m D B θ+3*η) (F+R+π)]
      dsimp only [A']
      ring
    _ ≤ _ := by
      have he : prefactorCenter m D B θ+3*η+(F+R+π)+(F+ε) ≤ m+11*η+π+ε := by
        rw [hF,hReq]
        unfold prefactorCenter
        linarith
      have hp := Real.rpow_le_rpow_of_exponent_le hZ.le he
      gcongr

end SevenEighths.InverseInitialEnergyCallerReference

end

end OAI
