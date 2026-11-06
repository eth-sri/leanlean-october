module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def activeGcdColumns (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → Ideal O :=
  fun j => idealQuotient D j.val.val

def activeGcdCoefficient (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → ℂ := fun j => a j.val

theorem originalHigh_gcd_eq_maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀j, Admissible (cols j))
    (hdiv : ∀j, D∣cols j) (hproper : ∀j, cols j≠D)
    (hray : ∀j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑j, ∑k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
    maskedPoissonDifference (commonMaskIdeal D) W (fun j => idealQuotient D (cols j)) a M K := by
  rw [originalHigh_gcd_principal_assembly D hD cols hcols hdiv hproper hray a W M K hM,
    maskedPoissonDifference,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

theorem annularRayGcdBlock_eq_active_difference (M N X K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (ha : CoefficientOnShell N X a)
    (D : Ideal O) (hD : D≠0) (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (c : EisensteinEPrimaryPhase.Coord) :
    annularRayGcdBlock M N K D c a =
      maskedPoissonDifference (commonMaskIdeal D) QuadraticInitialBound.annularSieveCutoff
        (activeGcdColumns N a D c) (activeGcdCoefficient N a D c) M K := by
  classical
  rw [annularRayGcdBlock_eq_pair_high M N K hM D c a]
  simp only [rayPairCoefficient,ite_mul,zero_mul]
  rw [gcd_ray_pair_sum_restrict]
  let S := gcdRaySupport (fun I : idealRange N => I.val) a D c
  have hdiv (j : S) : D∣j.val.val :=
    ((mem_gcdRaySupport _ a D c j.val).mp j.property).1
  have hray (j k : S) : columnRay j.val.val=columnRay k.val.val := by
    have hj := ((mem_gcdRaySupport _ a D c j.val).mp j.property).2.1
    have hk := ((mem_gcdRaySupport _ a D c k.val).mp k.property).2.1
    exact hj.trans hk.symm
  exact originalHigh_gcd_eq_maskedPoissonDifference D hD
    (fun j : S => j.val.val) (fun j => (mem_idealRange.mp j.val.property).1) hdiv
    (gcdRaySupport_proper N X a ha D c hsmall) hray (fun j : S => a j.val)
    QuadraticInitialBound.annularSieveCutoff M K hM

theorem HasSieveExponent.annular_small_gcd_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N X K T : ℝ), 1≤M → 1≤K → 4≤T →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N X a →
      ∀ (D : Ideal O), D≠0 → (Ideal.absNorm D:ℝ)≤X/2 →
      ∀ (c : EisensteinEPrimaryPhase.Coord),
        ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
            (commonMaskIdeal D) K (X/(Ideal.absNorm D:ℝ)) M T
            (activeGcdCoefficient N a D c) QuadraticInitialBound.annularSieveCutoff := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hbound⟩ :=
    hexp.masked_poisson_complete hα deltaLoss hδ l A
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro ε hε M N X K T hM hK hT a ha D hD hsmall c
  classical
  have hDn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤X/(Ideal.absNorm D:ℝ) := (le_div_iff₀ hDn).mpr (by linarith)
  have hp := gcdRaySupport_quotient_properties N X a ha D hD c
  rw [annularRayGcdBlock_eq_active_difference M N X K (by linarith) a ha D hD hsmall c]
  apply hbound ε hε (commonMaskIdeal D) (commonMaskIdeal_squarefree D)
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)
    K (X/(Ideal.absNorm D:ℝ)) M T hK hscale hM hT
    (activeGcdColumns N a D c) hp.1
    (fun j => ⟨(hp.2.1 j).1,(hp.2.1 j).2.1,(hp.2.1 j).2.2.1⟩)
    hp.2.2 (fun j => (hp.2.1 j).2.2.2) (activeGcdCoefficient N a D c)
    QuadraticInitialBound.annularSieveCutoff QuadraticInitialBound.annularSieveCutoff_zero

end

def selectedPoissonT (C M X η : ℝ) : ℝ := C*(M*X)^η
def selectedPoissonK (C M X η : ℝ) : ℝ := selectedPoissonT C M X η*X^2/M

theorem selectedPoisson_bounds (C M X η : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hMX : M≤X^2) (hη : 0≤η) :
    4≤selectedPoissonT C M X η ∧ 1≤selectedPoissonK C M X η ∧
      selectedPoissonK C M X η≤C*(M*X)^(η+2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hprod : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hprod hη
  have hT : 4≤selectedPoissonT C M X η := by
    unfold selectedPoissonT
    nlinarith
  have hfrac : 1≤X^2/M := (le_div_iff₀ hM0).mpr (by simpa using hMX)
  have hK : 1≤selectedPoissonK C M X η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    nlinarith
  refine ⟨hT,hK,?_⟩
  have hXprod : X≤M*X := by nlinarith
  have hfracup : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg X) hM).trans (pow_le_pow_left₀ hX0.le hXprod 2)
  unfold selectedPoissonK selectedPoissonT
  rw [mul_div_assoc,Real.rpow_add (by positivity : 0<M*X),Real.rpow_two]
  calc
    _ ≤ (C*(M*X)^η)*(M*X)^2 := mul_le_mul_of_nonneg_left hfracup (by positivity)
    _ = _ := by ring

theorem selectedPoisson_radial_identity (C B M X q η : ℝ)
    (hM : 0<M) (hX : 0<X) (hq : 0<q) (hB : 0<B) :
    (M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η =
      selectedPoissonT C M X η*q/B := by
  unfold selectedPoissonK
  field_simp

theorem cutoff_middle_identity (M X T α : ℝ) (hM : 0<M) (hX : 0<X) (hT : 0<T) :
    T*Real.sqrt M*(T*X^2/M)^(α-1/2) =
      T^(α+1/2)*X^(2*α-1)*M^(1-α) := by
  rw [Real.div_rpow (by positivity : 0≤T*X^2) hM.le,
    Real.mul_rpow hT.le (sq_nonneg X),←Real.rpow_two,←Real.rpow_mul hX.le]
  have hx : 2*(α-1/2)=2*α-1 := by ring
  have hm : 1-α=1/2-(α-1/2) := by ring
  have ht : α+1/2=1+(α-1/2) := by ring
  have hmPow : M^(1-α)=M^(1/2:ℝ)/M^(α-1/2) := by
    calc
      _ = M^((1/2:ℝ)-(α-1/2)) := by rw [hm]
      _ = _ := Real.rpow_sub hM _ _
  have htPow : T^(α+1/2)=T*T^(α-1/2) := by
    calc
      _ = T^(1+(α-1/2)) := by rw [ht]
      _ = _ := by rw [Real.rpow_add hT,Real.rpow_one]
  rw [hx,hmPow,htPow,Real.sqrt_eq_rpow]
  ring

theorem selectedPoisson_middle_bound (C M X η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hη : 0≤η) (hα : α≤2) :
    selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C^3*(M*X)^(3*η)*(X^(2*α-1)*M^(1-α)) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 0<M*X := by positivity
  have hP1 : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP1 hη
  have hT : 1≤selectedPoissonT C M X η := by unfold selectedPoissonT; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have htwo : (2:ℝ)^(α-1/2)≤4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : ((M*X)^η)^3 = (M*X)^(3*η) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP.le]
    congr 1
    ring
  have hT3 : (selectedPoissonT C M X η)^(α+1/2)≤C^3*(M*X)^(3*η) := by
    calc
      _ ≤ (selectedPoissonT C M X η)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = C^3*(M*X)^(3*η) := by norm_num only [selectedPoissonT,Real.rpow_ofNat,mul_pow,hp3]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hK0.le]
  calc
    _ ≤ 4*(selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)) := by
      have hh := mul_le_mul_of_nonneg_right htwo
        (show 0≤selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) by positivity)
      nlinarith [hh]
    _ = 4*((selectedPoissonT C M X η)^(α+1/2)*X^(2*α-1)*M^(1-α)) := by
      rw [selectedPoissonK,cutoff_middle_identity M X _ α hM0 hX0 hT0]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hT3
        (show 0≤X^(2*α-1)*M^(1-α) by positivity)
      nlinarith [hh]

end CanonicalQuadraticSieve

open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

namespace CubicEisenstein

abbrev EuclideanSpatial := EuclideanSpace ℝ (Fin 3)

def euclideanUpperHalf : Set EuclideanSpatial := {p | 0<p 2}
def hyperbolicDensity (p : EuclideanSpatial) : ℝ≥0∞ := ENNReal.ofReal ((p 2)^3)⁻¹

def hyperbolicEuclideanVolume : Measure EuclideanSpatial :=
  (volume.restrict euclideanUpperHalf).withDensity hyperbolicDensity

lemma euclideanUpperHalf_measurable : MeasurableSet euclideanUpperHalf := by
  exact measurableSet_lt measurable_const (by fun_prop)

lemma hyperbolicDensity_measurable : Measurable hyperbolicDensity := by
  unfold hyperbolicDensity
  fun_prop

lemma hyperbolic_volume_map_of_jacobian
    (f : EuclideanSpatial → EuclideanSpatial)
    (df : EuclideanSpatial → EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (hf : Measurable f) (hderiv : ∀p∈euclideanUpperHalf,HasFDerivAt f (df p) p)
    (hinj : Set.InjOn f euclideanUpperHalf) (himage : f '' euclideanUpperHalf=euclideanUpperHalf)
    (hjac : ∀p∈euclideanUpperHalf,
      ENNReal.ofReal |(df p).det| *hyperbolicDensity (f p)=hyperbolicDensity p) :
    Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs]
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (hs.preimage hf),withDensity_apply _ hs]
  rw [←lintegral_indicator (hs.preimage hf),←lintegral_indicator hs]
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    euclideanUpperHalf_measurable (fun p hp => (hderiv p hp).hasFDerivWithinAt) hinj
    (s.indicator hyperbolicDensity)
  rw [himage] at hc
  rw [hc]
  apply setLIntegral_congr_fun euclideanUpperHalf_measurable
  intro p hp
  by_cases hsfp : f p∈s
  · simp only [Set.indicator_of_mem hsfp,Set.mem_preimage,hsfp,Set.indicator_of_mem]
    exact (hjac p hp).symm
  · simp only [Set.indicator_of_notMem hsfp,mul_zero]
    have hpnot : p∉f ⁻¹' s := hsfp
    exact Set.indicator_of_notMem hpnot hyperbolicDensity

def euclideanInversion : EuclideanSpatial → EuclideanSpatial := inversion 0 1

def euclideanInversionDeriv (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  (1/‖p‖)^2 • (((ℝ ∙ p)ᗮ).reflection : EuclideanSpatial →L[ℝ] EuclideanSpatial)

lemma euclideanInversion_apply (p : EuclideanSpatial) (j : Fin 3) :
    euclideanInversion p j=(1/‖p‖)^2*p j := by
  simp [euclideanInversion,inversion,dist_zero_right]

lemma euclideanInversion_measurable : Measurable euclideanInversion := by
  simp +unfoldPartialApp only [euclideanInversion,inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero]
  fun_prop

lemma euclideanUpperHalf_ne_zero (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) : p≠0 := by
  intro he
  simp [euclideanUpperHalf,he] at hp

lemma euclideanInversion_mem (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    euclideanInversion p∈euclideanUpperHalf := by
  change 0<euclideanInversion p 2
  rw [euclideanInversion_apply]
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (norm_pos_iff.mpr (euclideanUpperHalf_ne_zero p hp)))) hp

lemma euclideanInversion_image : euclideanInversion '' euclideanUpperHalf=euclideanUpperHalf := by
  apply Set.Subset.antisymm
  · rintro p ⟨q,hq,rfl⟩
    exact euclideanInversion_mem q hq
  · intro p hp
    exact ⟨euclideanInversion p,euclideanInversion_mem p hp,
      inversion_inversion 0 (by norm_num) p⟩

lemma euclideanInversion_hasFDerivAt (p : EuclideanSpatial) (hp : p≠0) :
    HasFDerivAt euclideanInversion (euclideanInversionDeriv p) p := by
  simpa [euclideanInversion,euclideanInversionDeriv,dist_zero_right] using
    (hasFDerivAt_inversion (R := (1:ℝ)) hp)

lemma euclideanInversion_abs_det (p : EuclideanSpatial) :
    |(euclideanInversionDeriv p).det|=((1/‖p‖)^2)^3 := by
  unfold euclideanInversionDeriv
  change |LinearMap.det ((1/‖p‖)^2 • ((ℝ ∙ p)ᗮ).reflection.toLinearMap)|=_
  rw [LinearMap.det_smul]
  rw [Submodule.det_reflection]
  simp only [finrank_euclideanSpace,Fintype.card_fin,abs_mul,abs_pow,abs_neg,abs_one,
    one_pow,mul_one]
  rw [abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg p))]

lemma euclideanInversion_jacobian_density (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    ENNReal.ofReal |(euclideanInversionDeriv p).det| *
      hyperbolicDensity (euclideanInversion p)=hyperbolicDensity p := by
  rw [euclideanInversion_abs_det,hyperbolicDensity,hyperbolicDensity,euclideanInversion_apply]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  field_simp

theorem euclideanInversion_preserves_hyperbolicVolume :
    Measure.map euclideanInversion hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian euclideanInversion euclideanInversionDeriv
    euclideanInversion_measurable
  · exact fun p hp => euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp)
  · exact (inversion_injective 0 (by norm_num : (1:ℝ)≠0)).injOn
  · exact euclideanInversion_image
  · exact euclideanInversion_jacobian_density

end CubicEisenstein

end

end OAI
