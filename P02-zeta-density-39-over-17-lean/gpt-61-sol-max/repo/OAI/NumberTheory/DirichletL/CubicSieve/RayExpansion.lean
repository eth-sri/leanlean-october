module
import Mathlib
public import OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
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
                          
                          
           
                    
open ConcreteTraceCRT ActualEisensteinCubic
            
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
           
            
            
                                                       
                                     
                    
                       
open Ideal NumberField
                      
                      
                      
                      
                       
                                     
                    
open Filter Asymptotics Ideal NumberField
           
                                     
                    
                                     
                    
                                     
                    
                       
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
                                  
                                  
open scoped BigOperators Classical SchwartzMap ContDiff
                                                       
                                  
                                                       
                                  
                                                       
                                                       
                                                       
                                  
                                                       
open MeasureTheory
                        
                                  
                                  
                          

                                  
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport firstPassColumnMinus firstPassColumnPlus)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)

section
variable {ι : Type*}
include ι

def fixedRayExpansion  (p : ι → O) (F S : Finset ι) : ℂ :=
  ∑ χ : RayCharacter, ∑ η : RayCharacter,
    crossCoeff χ η * supportRay p χ S * supportRay p η F

section
variable [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
include p hp hcop hg

theorem fixedRayExpansion_eq_cross 
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F S : Finset ι) (hd : Disjoint S F) :
    fixedRayExpansion p F S = quadraticCrossPhase p hg S F :=
  (RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc S F hd).symm

section
variable (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι)
include B v ε₁ ε₂ C d S

def cubeMinusCoefficient  : ℂ :=
  star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
    firstPassColumnMinus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ true) S

def cubePlusCoefficient  : ℂ :=
  fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
    firstPassColumnPlus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ false) S
end


theorem threeGaussRowFactor_eq_ray_columns 
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
        star (supportMobius (fun i => Ideal.span {p i}) N *
          cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d N *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
        (supportMobius (fun i => Ideal.span {p i}) P *
          cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d P *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) := by
  rw [threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  unfold cubeTransformedPair cubeMinusCoefficient cubePlusCoefficient
  rw [fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) N
      (hNB.mono_right (Finset.filter_subset _ _)),
    fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) P
      (hPB.mono_right (Finset.filter_subset _ _))]
  simp only [star_mul, star_star]
  ring
end
end


end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FourierBridge (logPhase logPhase_norm logPhase_continuous_left)
open EisensteinSchwartzPoisson (paperRadialFourier)

section
variable {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι)
include ι C V y t S

def logTwistMinus  : ℂ :=
  C S * star (V (y S) * logPhase t (-(y S)))

def logTwistPlus  : ℂ :=
  C S * (V (y S) * logPhase t (-(y S)))
end


end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

section
variable {ι : Type*}
include ι

section
variable (p : ι → O)
include p

def primeProductNorm  (S : Finset ι) : ℝ :=
  ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2

theorem primeProductNorm_pos  (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2
end


theorem primeProductNorm_union  [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

def columnLog  (p : ι → O) (X : ℝ) (S : Finset ι) : ℝ :=
  Real.log (primeProductNorm p S / X)
end


end FirstPassCubeLabels

open scoped BigOperators Classical
namespace QuadraticDivisorSplit
abbrev O := ActualEisensteinCubic.O

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  grind

open IdealMobiusDivisorSum

section
variable (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C)
include B C hB hC hBC

theorem divisors_coprime_product  :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product  (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he
end







