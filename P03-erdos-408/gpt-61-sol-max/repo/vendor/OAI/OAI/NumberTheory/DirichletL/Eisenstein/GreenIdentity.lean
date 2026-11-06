module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 

namespace CubicEisenstein
 
 

end CubicEisenstein

namespace CanonicalQuadraticSieve

section
variable (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀) (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T)


include hX₀ hlo hhi hT in
theorem symmetric_truncation_scales    
          :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

include hX₀ hlo hhi hT in
theorem symmetric_truncation_scalar_bound      
          :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
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
    gcongr <;> first | assumption | positivity | linarith
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
    gcongr <;> first | assumption | positivity | linarith
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end

end CanonicalQuadraticSieve

 
namespace SecondPassArithmetic

section
 
open FirstPassCubeLabels (columnLog primeProductNorm)

def SecondSourceSupport {ι } [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι)  :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end
section

 
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ)  := ⌊Real.log u⌋₊
def normLogScale (j : ℕ)  := Real.exp (j : ℝ)

section
variable (j : ℕ)


lemma normLogScale_pos   : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one   : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

end

lemma normLogBin_scale_bounds  u  (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono  {u v}  (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

abbrev SecondLogIndex := ℕ × ℕ × ℕ

def secondLogE (j : SecondLogIndex)  := normLogScale j.1
def secondLogV (j : SecondLogIndex)  := normLogScale j.2.1
def secondLogK (j : SecondLogIndex)  := normLogScale j.2.2

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogIndex (D : Finset ι) (x : SecondExpansionData ι)  :=
  (normLogBin (primeProductNorm p x.divisor), normLogBin (primeProductNorm p x.overlap),
    normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2))

lemma element_norm_ge_one  a  (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

end


 
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSupportedSector (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ)  :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (SecondSourceSupport p X M)

def secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)  :=
  (secondSupportedSector p F K R X M).filter (fun x => secondLogIndex p D x = j)

end SecondPassArithmetic

end

end OAI
