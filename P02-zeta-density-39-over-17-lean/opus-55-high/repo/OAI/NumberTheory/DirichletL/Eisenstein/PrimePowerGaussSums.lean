module
public import OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped Classical SchwartzMap

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma cubicUnitGaussSum_one (h:Eis):cubicUnitGaussSum h 1=1:=by
  let:Subsingleton (Eis⧸Ideal.span {(1:Eis)}):=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let r:CubicUnitResidue (1:Eis):=⟨1,isUnit_one⟩
  rw [cubicUnitGaussSum,tsum_eq_single r (fun b hb=>False.elim (hb (Subsingleton.elim b r)))]
  rw [symbol_one,map_one,one_mul,
    residueAdditive_three_congr h 1 _ 0 one_ne_zero (one_dvd _)]
  pm_94 residueAdditive map_zero mul_zero zero_div AddChar.map_zero_eq_one

lemma cubicUnitGaussSum_frequency_dvd (h c:Eis) (hc:c≠0) (hch:c∣h):
    cubicUnitGaussSum h c=cubicUnitGaussSum 0 c:=
  cubicUnitGaussSum_frequency_congr h 0 c hc (by simp_all)

section
variable (p:Eis) (hp:Prime p)
include p hp
lemma cubicUnitGaussSum_prime_power_zero (hprimary:lambda^2∣p-1) (n:ℕ):
    cubicUnitGaussSum 0 (p^(n+1))=
      if 3∣n+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^n*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)-1) else 0:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary n 0
  simp only [mul_zero] at he
  rw [he,primeCubicGauss_of_dvd p hp hprimary (n+1) 0 (dvd_zero _)]
  grind

lemma cubicUnitGaussSum_prime_power_too_large
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a k:ℕ) (hk:a+1<k):
    cubicUnitGaussSum (h*p^a) (p^k)=0:=by
  by_contra hG
  cases k with
  | zero=>omega
  | succ n=>
    have hd:=cubicUnitGaussSum_prime_power_support p hp hprimary n (h*p^a) hG
    have hd':p^(a+1)∣p^a*h:=by
      rw [mul_comm]
      exact (pow_dvd_pow p (by omega:a+1≤n)).trans hd
    rw [pow_succ] at hd'
    exact hph ((mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hd')

lemma unramifiedPrimeDeletedSeries_pow_mod (s:ℂ) (h:Eis) (n:ℕ):
    unramifiedPrimeDeletedSeries p s (h*p^n)=
      unramifiedPrimeDeletedSeries p s (h*p^(n%3)):=by
  apply tsum_congr
  intro I
  congr 1
  pm_3640 p
  exact cubicUnitGaussSum_cube_shift _ _ _ I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2
    (primeDeleted_generator_coprime p hp I).symm.pow_right

theorem unramifiedCubicGaussSeries_prime_finite
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2< s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^a)=
      ∑k∈Finset.range (a+2),((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*
        cubicUnitGaussSum (h*p^a) (p^k)*unramifiedPrimeDeletedSeries p s (h*p^a*p^k):=by
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs]
  apply tsum_eq_sum
  intro k hk
  have hk':a+1<k:=by
    have hh: a+2≤k:=by simpa only [Finset.mem_range,not_lt] using hk
    omega
  rw [cubicUnitGaussSum_prime_power_too_large p hp hprimary h hph a k hk',mul_zero,zero_mul]

lemma unramifiedCubicGaussSeries_prime_zero_power
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2< s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s h=unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 0
  simpa only [pow_zero,pow_one,mul_one,cubicUnitGaussSum_one,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,one_mul,
    primeCubicGauss_one_eq] using he

lemma unramifiedCubicGaussSeries_prime_one_power
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2< s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p)=unramifiedPrimeDeletedSeries p s (h*p)+
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^2*(Ideal.absNorm (Ideal.span {p}):ℂ)*
        primeCubicGauss p hp hprimary 2 h*unramifiedPrimeDeletedSeries p s h:=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 1
  have hg1:cubicUnitGaussSum (h*p) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero (dvd_mul_left p h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p) (p^2)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)*primeCubicGauss p hp hprimary 2 h:=by
    simpa only [pow_one,mul_comm p h] using cubicUnitGaussSum_prime_power_lift p hp hprimary 1 h
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,mul_zero,zero_mul,add_zero,hg2] at he
  have hr:h*p*p^2=h*p^3:=by ring
  rw [hr,unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_prime_three_power
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2< s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+((Ideal.absNorm (Ideal.span {p}):ℂ)^3-(Ideal.absNorm (Ideal.span {p}):ℂ)^2)*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^4*
        primeCubicGauss p hp hprimary 1 h*unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 3
  have hg0 (k:ℕ) (hk:k≤3):cubicUnitGaussSum (h*p^3) (p^k)=cubicUnitGaussSum 0 (p^k):=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p^3) h))
  have hg1:cubicUnitGaussSum (h*p^3) p=0:=by
    have hh:=hg0 1 (by omega)
    simp only [pow_one] at hh
    rw [hh]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^3) (p^2)=0:=by
    rw [hg0 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^3) (p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1):=by
    rw [hg0 3 le_rfl]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 2
  have hg4:cubicUnitGaussSum (h*p^3) (p^4)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*primeCubicGauss p hp hprimary 1 h:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 3 h
    rw [primeCubicGauss_mod_three p hp hprimary 4] at hh
    simpa only [mul_comm (p^3) h,Nat.reduceMod] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,hg4,mul_zero,zero_mul,add_zero] at he
  have hr6:h*p^3*p^3=h*p^6:=by ring
  have hr7:h*p^3*p^4=h*p^7:=by ring
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,hr6,hr7,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 6,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 7] at he
  norm_num only [Nat.reduceMod,pow_zero,pow_one,mul_one] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_prime_recurrence
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2< s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedCubicGaussSeries s (h*p):=by
  rw [unramifiedCubicGaussSeries_prime_three_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_zero_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_one_power p hp hprimary s hs h hph]
  have hg:=primeCubicGauss_one_mul_two p hp hprimary h hph
  linear_combination ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
    (Ideal.absNorm (Ideal.span {p}):ℂ)*unramifiedPrimeDeletedSeries p s h*hg
end

end

section
open Filter MeasureTheory
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

structure SubexponentialBesselCoefficients where
  value : ActualEisensteinCubic.O→ℂ
  growth : ∀epsilon : ℝ,0<epsilon → ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
    ‖value h‖≤C*Real.exp (epsilon*‖cuspFrequency h‖)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def term (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else (coeff.value h/cubicBesselNormalizer h)*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

def amplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma term_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.term h (v,z)=coeff.value h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [term,ite_eq_right hh]
  pm_3548
  have hn := cubicBesselNormalizer_ne_zero h hh
  pm_3690
  calc
    _ = (coeff.value h/cubicBesselNormalizer h)*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [sourceFourierKernel_cubic_height h hh v hv]
      field_simp

lemma term_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    coeff.term h (v,z)=coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  pm_5558 term amplitude coeff.term_bessel

lemma term_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (coeff.term h) {p : ℝ × ℂ | 0<p.1} := by pm_3691 term

lemma slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.term h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  pm_3556
  have hCu := cubicBesselUpperAway_pos delta hdelta
  pm_3557
  refine ⟨C*b*cubicBesselUpperAway delta,by positivity,?_⟩
  pm_7523
  pm_3558
  pm_3674
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1 ha.le (norm_nonneg _)
    dsimp [delta]
    pm_3692
  pm_1241 coeff.term_bessel
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (by positivity))
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway delta)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2=
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le]

lemma summable (p : ℝ × ℂ) (hp : 0<p.1) : Summable (fun h : ActualEisensteinCubic.O => coeff.term h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p

lemma series_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn coeff.series {p : ℝ × ℂ | p.1∈Set.Icc a b} := by pm_3694 coeff.slab_bound coeff.term_continuousOn

lemma series_continuousOn : ContinuousOn coeff.series {p : ℝ × ℂ | 0<p.1} := by pm_3695 coeff.series_continuousOn_slab

lemma series_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.series (v,z)=∑'h : ActualEisensteinCubic.O,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  exact tsum_congr (fun h => coeff.term_eq_amplitude v hv h z)

lemma series_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.series (v,z+3*ConcreteTraceCRT.eisEmbedding n)=coeff.series (v,z) := by
  pm_975 term

def function (w : HyperbolicSpace) : ℂ := coeff.series (hyperbolicHeight w,hyperbolicHorizontal w)

lemma function_continuous : Continuous coeff.function := by pm_3696 coeff.series_continuousOn.continuousAt

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

section
variable (v : ℝ) (hv : 0<v)
include v hv
lemma series_fourier (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v k := by pm_3697 coeff.amplitude coeff.slab_bound coeff.term_eq_amplitude coeff.term

lemma series_height_continuous :
    Continuous (fun z : ℂ => coeff.series (v,z)) := by pm_3576 coeff.series_continuousOn.continuousAt
end

def fullFunction (constant : ℂ) (w : HyperbolicSpace) : ℂ :=
  constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w

section
variable (constant : ℂ)
include constant
lemma fullFunction_continuous : Continuous (coeff.fullFunction constant) := by pm_3575 coeff.function_continuous

lemma fullFunction_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.fullFunction constant (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then constant*(v:ℂ)^(2/3:ℂ) else coeff.amplitude v k) := by pf_112 constant coeff.series coeff.series_height_continuous fullFunction function coeff.series_fourier amplitude

lemma fullFunction_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.fullFunction constant (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      coeff.fullFunction constant (upperPoint z v hv) := by
  pm_1443 fullFunction function hyperbolicHeight_upperPoint hyperbolicHorizontal_upperPoint coeff.series_period

lemma fullFunction_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.fullFunction constant (upperPoint z v hv)) := by
  have hc := coeff.series_height_continuous v hv
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma fullFunction_height_memLp (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => coeff.fullFunction constant (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by pf_177 (coeff.fullFunction_height_continuous constant) (coeff.fullFunction constant)
end

end SubexponentialBesselCoefficients
end CubicEisenstein


namespace ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D ∣r-r0) (hu : D ∣u*r-1) (hu0 : D ∣u0*r0-1) : D ∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D ∣r-r0)
    (hu : D ∣u*r-1) (hu0 : D ∣u0*r0-1) (hd : D ∣d-d0) :
    D ∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert dvd_neg.mpr hh using 1 ; ring

end ShortDraftCRT

open Filter MeasureTheory
open scoped Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedHeightCompact (M:levelTwo) (a b:ℝ) : Set KernelQuotient :=
  kernelSourceAction M '' cuspHeightQuotientCompact a b

lemma translatedHeightCompact_isCompact (M:levelTwo) (a b:ℝ) (ha:0<a) :
    IsCompact (translatedHeightCompact M a b) :=
  (cuspHeightQuotientCompact_isCompact a b ha).image (kernelSourceAction_continuous M)

def translatedHeightFourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) : KernelQuotientL2→L[ℂ]ℂ :=
  (kernelCuspHeightFourier a b ha ρ h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedHeightFourier_integral (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M F=
      ∫w in cuspPeriodStrip a b,F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,kernelCuspHeightFourier_integral]
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp (kernelSourcePullback_ae_eq M F)
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w) hw

lemma translatedHeightFourier_restrict (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M
      (kernelMassRestrictionCLM (translatedHeightCompact M a b)
        (translatedHeightCompact_isCompact M a b ha).measurableSet F)=translatedHeightFourier a b ha ρ h M F := by
  rw [translatedHeightFourier_integral,translatedHeightFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha).measurableSet F)
  pm_7906 he hsource
  pm_3665
  pm_3559
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem hm _))

def translatedHeightFamily (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) : ℂ :=
  translatedHeightFourier a b ha ρ h M
    (kernelLocalCorrectedSeed (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

section
variable (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (M:levelTwo)
include a b ha ρ h M
lemma translatedHeightFamily_analyticAt (s:ℂ) (hs:s.re≠1) (hi:s.im≠0) :
    AnalyticAt ℂ (translatedHeightFamily a b ha ρ h M) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedHeightFourier a b ha ρ h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedHeightCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma translatedHeightFamily_residue_limit :
    Tendsto (fun s:ℂ=>(s-4/3)*translatedHeightFamily a b ha ρ h M s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (translatedHeightFourier a b ha ρ h M cubicEisensteinResidue)) := by
  have hh:=(translatedHeightFourier a b ha ρ h M).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (translatedHeightCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedHeightFourier_restrict,
    translatedHeightFamily] using hh

lemma translatedHeightFamily_initial (s:ℂ) (hs:4< s.re) (hi:0< s.im) :
    translatedHeightFamily a b ha ρ h M s =
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*
        cuspWeightedFourierPhase ρ h w∂ hyperbolicVolume := by
  have hcorrected:kernelCorrectedSeed 2 3 (by norm_num) (by norm_num) s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi] with q hq
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hq]
    ring
  have hlocal:=kernelLocalCorrectedSeed_ae_eq _ (translatedHeightCompact_isCompact M a b ha)
    2 3 (by norm_num) (by norm_num) s
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hlocal
  have hE:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  pm_7906 hp hsource
  pm_7906 hpE hE
  rw [translatedHeightFamily,translatedHeightFourier_integral]
  apply integral_congr_ae
  filter_upwards [hp,hpE,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwe hwm
  pm_3559
  dsimp only [Function.comp_def] at hw hwe
  rw [hw,Set.indicator_of_mem hm,hwe,kernelSourceAction_mk,kernelQuotientEisenstein_mk]
end

end CubicEisenstein

end

end OAI
