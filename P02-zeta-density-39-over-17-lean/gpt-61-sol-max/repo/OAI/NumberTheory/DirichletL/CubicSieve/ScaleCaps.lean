module
import Mathlib
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
public import OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology

@[expose] public section

namespace OAI



open scoped BigOperators
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
open scoped BigOperators Classical
                                  
                                  
open scoped BigOperators Classical SchwartzMap ContDiff
                                                       
                                  
                                                       
                                  
                                                       
                                                       
                                                       
                                  
                                                       
open MeasureTheory Set
                        
                                  
                                  
open ActualEisensteinCubic UniqueFactorizationMonoid
                        

                                  


open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem maskedPairDualTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M N K : ℝ),
      G≠0 → I≠0 → J≠0 → 0<M → 1≤N → 0≤K →
      N/2≤(Ideal.absNorm I:ℝ) → (Ideal.absNorm I:ℝ)≤N →
      N/2≤(Ideal.absNorm J:ℝ) → (Ideal.absNorm J:ℝ)≤N →
      ‖maskedPairDualTail G I J W M K‖ ≤
        (2*M/N)*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := dualSquarefreeTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro G I J W M N K hG hI hJ hM hN hK hIl hIu hJl hJu
  have hNG : 0<(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNI : 0<(Ideal.absNorm I:ℝ) := by linarith
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by linarith
  have hN0 : 0<N := by linarith
  let t0 := M/((Ideal.absNorm G:ℝ)*N*N)
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 t0)^2*(1+t0*K)^A)
  have ht0 : 0<t0 := by dsimp only [t0]; positivity
  have hT : 0≤T := by dsimp only [T]; positivity
  have hterm (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖ ≤ T := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hqN : (Ideal.absNorm q:ℝ)≤(Ideal.absNorm G:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by exact_mod_cast hNG) (map_dvd Ideal.absNorm hqG)
    have ht : 0<M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by positivity
    have htlo : t0≤M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      gcongr
    have hc : ‖(UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ)‖≤1 := by
      rw [norm_div,norm_mul,Complex.norm_natCast]
      have hp : ‖unrestrictedPairCharacter I J q‖≤1 := by
        rw [unrestrictedPairCharacter,norm_mul]
        exact (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      calc
        _ ≤ (1*1)/(Ideal.absNorm q:ℝ) := by
          gcongr
          exact QuadraticInitialBound.norm_ideal_moebius_le_one q
        _ ≤ 1 := by simpa only [one_mul,div_one] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1)
    have hb : ‖dualSquarefreeTail I J W
        (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖≤T := by
      apply (hbound I J W _ K ht hK).trans
      dsimp only [T]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    rw [norm_mul]
    exact (mul_le_mul hc hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpref : ‖(M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ)‖≤2*M/N := by
    simp only [norm_div, norm_real, norm_eq_abs, abs_of_nonneg hM.le, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one,one_mul] using
      dual_truncation_prefactor_bound M 1 N (Ideal.absNorm I) (Ideal.absNorm J)
        hM (by norm_num) hN0 ⟨hIl,hIu⟩ ⟨hJl,hJu⟩
  rw [maskedPairDualTail,norm_mul]
  calc
    _ ≤ (2*M/N)*(∑ q ∈ idealDivisors G, T) := mul_le_mul hpref
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T,t0]; ring

theorem coprime_pair_error_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (E : ℝ) (hE : 0≤E)
    (error : n → n → ℂ) (herr : ∀ j k, ‖error j k‖≤E) :
    ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ ≤
      (Fintype.card n:ℝ)*E*∑ j, ‖a j‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖*‖a k‖*E) = (∑ j, ‖a j‖)^2*E := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    apply Finset.sum_congr rfl
    grind
  calc
    _ ≤ ∑ j, ∑ k, ‖if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, ‖a j‖*‖a k‖*E := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · simp only [norm_mul,norm_star]
        exact mul_le_mul_of_nonneg_left (herr j k) (by positivity)
      · simp only [norm_zero]
        positivity
    _ = (∑ j, ‖a j‖)^2*E := hs
    _ ≤ ((∑ j, ‖a j‖^2)*(Fintype.card n:ℝ))*E := mul_le_mul_of_nonneg_right hcs hE
    _ = _ := by ring

theorem maskedDualTailFamily_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ)
      (W : 𝓢(ℝ,ℂ)) (M N K : ℝ), G≠0 → Function.Injective cols →
      0<M → 1≤N → 0≤K →
      (∀ j, cols j≠0 ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
      ‖maskedDualTailFamily G cols a W M K‖ ≤
        256*M*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) * ∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := maskedPairDualTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro n _ G cols a W M N K hG hinj hM hN hK hcols
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)
  have hT : 0≤T := by dsimp only [T]; positivity
  have hn := finite_ideal_family_card_bound cols hinj N hN
    (fun j => (hcols j).1) (fun j => (hcols j).2.2)
  have herr (j k : n) : ‖maskedPairDualTail G (cols j) (cols k) W M K‖≤
      (2*M/N)*(idealDivisors G).card*T :=
    hbound G (cols j) (cols k) W M N K hG (hcols j).1 (hcols k).1 hM hN hK
      (hcols j).2.1 (hcols j).2.2 (hcols k).2.1 (hcols k).2.2
  calc
    _ ≤ (Fintype.card n:ℝ)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 :=
      coprime_pair_error_energy cols a _ (by positivity) _ herr
    _ ≤ (128*N)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 := by gcongr
    _ = _ := by dsimp only [T]; field_simp; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical





