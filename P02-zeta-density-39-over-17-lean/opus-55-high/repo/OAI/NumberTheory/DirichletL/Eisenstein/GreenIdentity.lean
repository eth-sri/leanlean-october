module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped Classical Topology

end CubicEisenstein

namespace CanonicalQuadraticSieve

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  pm_72 hT0 T hX X
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  pm_34 hT0 T hT1
  have hX : 0 < X := by linarith
  pm_6528 hY X₀ T hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    pm_5252 hm m
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end CanonicalQuadraticSieve

open scoped Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)

def SecondSourceSupport {ι : Type*} [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι) : Prop :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

abbrev SecondLogIndex := ℕ × ℕ × ℕ

def secondLogE (j : SecondLogIndex) : ℝ := normLogScale j.1
def secondLogV (j : SecondLogIndex) : ℝ := normLogScale j.2.1
def secondLogK (j : SecondLogIndex) : ℝ := normLogScale j.2.2

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogIndex (D : Finset ι) (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor), normLogBin (primeProductNorm p x.overlap),
    normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2))

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  pm_5580 a ha

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSupportedSector (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (SecondSourceSupport p X M)

def secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) : Finset (SecondExpansionData ι) :=
  (secondSupportedSector p F K R X M).filter (fun x => secondLogIndex p D x = j)

end SecondPassArithmetic

end

end OAI
