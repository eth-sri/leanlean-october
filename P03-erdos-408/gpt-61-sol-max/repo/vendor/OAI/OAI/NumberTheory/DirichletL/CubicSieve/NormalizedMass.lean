module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.DivisorTargets

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
 
 
 
 
 

 
namespace SecondPassArithmetic




 
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

end SecondPassArithmetic

 
namespace CompletedGauss

section
open   LocalReflectionBrackets

section
variable (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
include P hg

theorem bracket_one_eq_quadratic    
       z  :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P z)=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 := by
  simp only [bracket,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,↓reduceIte]
  rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  by_cases hz : z∈P
  · have he : Ideal.Quotient.mk P z=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg z
    change actualSextic P hg (Ideal.Quotient.mk P (z^6))=_ at h6
    simp only [map_pow,ite_eq_right hz] at h6
    grind

theorem quadratic_value_cube    
       b  :
    (actualSextic P hg (Ideal.Quotient.mk P (b^3)))^3=
      (actualSextic P hg (Ideal.Quotient.mk P b))^3 := by
  simp only [map_pow]
  by_cases hb : b∈P
  · have he : Ideal.Quotient.mk P b=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg b
    change actualSextic P hg (Ideal.Quotient.mk P (b^6))=_ at h6
    simp only [map_pow,ite_eq_right hb] at h6
    grind

theorem residual_bracket_cube    
       z n b  :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (z*n*b^3))=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 *
      (actualSextic P hg (Ideal.Quotient.mk P (n*b)))^3 := by
  rw [bracket_one_eq_quadratic]
  simp only [map_mul,mul_pow]
  rw [quadratic_value_cube]
  ring

end

end



 

theorem prime_square_dvd_powerful (I P : Ideal O) (hI : PowerfulIdeal I)
    (hP : Prime P) (hd : P∣I) : P^2∣I := by
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mpr ⟨hP,hd⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hP.ne_zero) hI.1).mpr
  rw [normalizedFactors_pow,normalizedFactors_irreducible hP.irreducible,normalize_eq]
  apply Multiset.le_iff_count.mpr
  intro Q
  by_cases hQP : Q=P
  · subst Q
    simpa using hI.2 P hm
  · simp [hQP]

theorem nonresidual_prime_square_dvd  I Q P  (hI : I≠0) (hP : Prime P)
    (hd : P∣I) (hr : ¬P∣rowResidualPart I Q) :
    P^2∣rowPowerfulPart I*(rowMaskPart I Q)^2 := by
  have hh : P∣rowPowerfulPart I*rowMaskPart I Q := by
    rw [←row_powerful_mask_residual_product I Q hI] at hd
    exact (hP.dvd_mul.mp hd).resolve_right hr
  rcases hP.dvd_mul.mp hh with ha|ht
  · exact dvd_mul_of_dvd_left (prime_square_dvd_powerful _ _ (rowPowerfulPart_powerful I) hP ha) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _

def nonresidualGain (I P : Ideal O)  := if P∣I then P^2 else P

theorem nonresidual_gain_product_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) :
    (∏i,nonresidualGain I (P i)) ∣ rowPowerfulPart I*(rowMaskPart I Q)^2*Q := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    change IsCoprime (nonresidualGain I (P i)) (nonresidualGain I (P j))
    unfold nonresidualGain
    by_cases hi : P i∣I
    · rw [ite_eq_left hi]
      by_cases hj : P j∣I
      · rw [ite_eq_left hj]
        exact (hcop hij).pow
      · rw [ite_eq_right hj]
        exact (hcop hij).pow_left
    · rw [ite_eq_right hi]
      by_cases hj : P j∣I
      · rw [ite_eq_left hj]
        exact (hcop hij).pow_right
      · rw [ite_eq_right hj]
        exact hcop hij
  · intro i
    have hp : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
    by_cases hi : P i∣I
    · rw [nonresidualGain,ite_eq_left hi]
      exact dvd_mul_of_dvd_left (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)) Q
    · rw [nonresidualGain,ite_eq_right hi]
      exact dvd_mul_of_dvd_right ((hp.dvd_mul.mp (hpool i)).resolve_left hi) _

 

def completedLocalExponent (I F P : Ideal O)  :=
  ((normalizedFactors I).count P+4*(if P∣F then 1 else 0))%6

def reflectionExtractedPrime (P : Ideal O) (j : ℕ) (e v : Fin 3)  :=
  if (j=4 ∧ e=v) ∨ (j=0 ∧ v=0) then P else 1

def reflectionExtractedDivisor {ι } [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3)  :=
  ∏i,reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι } [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3)  :=
  (Ideal.absNorm (∏i,P i):ℝ)^2/
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)^4)

def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3)  :=
  if j=4 then (if e=2 then 1/q^2 else q)
  else if j=0 then q else q^2

theorem reflectionConductorCost_eq_prod {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0)  j   e  :
    reflectionConductorCost P j e=∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (j i) (e i) := by
  
  simp only [reflectionConductorCost,reflectionExtractedDivisor,map_prod,Nat.cast_prod,
    ←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize he : e i=v
    fin_cases v <;> simp [reflectionExtractedPrime,reflectionLocalCost] <;> field_simp
  · by_cases hj0 : j i=0
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj0]
      field_simp
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj4,hj0]

section
variable (q : ℝ)
include q

theorem reflectionLocalCost_nonneg   (hq : 0≤q)  j   e  :
    0≤reflectionLocalCost q j e := by
  unfold reflectionLocalCost
  split_ifs <;> positivity

section
variable (hq : 1≤q) (j : ℕ) (e : Fin 3)
include hq j e

theorem reflectionLocalCost_le_square         :
    reflectionLocalCost q j e≤q^2 := by
  
  have hq2 : 1≤q^2 := one_le_pow₀ hq
  unfold reflectionLocalCost
  split_ifs
  · exact (div_le_one (by positivity)).mpr hq2 |>.trans hq2
  · nlinarith
  · nlinarith
  · rfl

theorem reflectionLocalCost_le_single        
    (hj : j=0 ∨ j=4) : reflectionLocalCost q j e≤q := by
  
  rcases hj with rfl|rfl
  · simp [reflectionLocalCost]
  · simp only [reflectionLocalCost,ite_true]
    split_ifs
    · exact ((div_le_one (by positivity)).mpr (one_le_pow₀ hq)).trans hq
    · rfl

end

end

section
variable (I F P : Ideal O) (hI : I≠0)
include I F P hI

theorem completedLocalExponent_of_not_dvd     (_hP : Prime P)
    (hn : ¬P∣I) : completedLocalExponent I F P=0 ∨ completedLocalExponent I F P=4 := by
  have hm : P∉normalizedFactors I := by
    intro h
    exact hn ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp h).2
  simp only [completedLocalExponent,Multiset.count_eq_zero.mpr hm,zero_add]
  split_ifs <;> norm_num

theorem reflectionLocalCost_le_gain     (hP : Prime P)  e  :
    reflectionLocalCost (Ideal.absNorm P:ℝ) (completedLocalExponent I F P) e≤
      (Ideal.absNorm (nonresidualGain I P):ℝ) := by
  have hq : 1≤(Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  by_cases hd : P∣I
  · simp_all [nonresidualGain, reflectionLocalCost_le_square]
  · rw [nonresidualGain,ite_eq_right hd]
    exact reflectionLocalCost_le_single _ hq _ _ (completedLocalExponent_of_not_dvd I F P hI hP hd)

end

theorem reflectionConductorCost_bound {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q)  e  :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr

end CompletedGauss

end

end OAI
