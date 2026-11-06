module
import Mathlib
public import OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects

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

open Filter


           
                    
open ConcreteTraceCRT
            
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
           
            
            
                                                       
                                     
                    
                       
open Ideal NumberField
                      
                      
                      
                      
                       
                                     
                    
open Filter Asymptotics Ideal NumberField
           
                                     
                    
                                     
                    
                                     
                    
                       
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
                                  
                                  
open scoped BigOperators Classical SchwartzMap ContDiff
                                                       
                                  
                                                       
                                  
                                                       
                                                       
                                                       
                                  
                                                       
open MeasureTheory
                        
                                  
                                  

                        

                                  
namespace SecondPassArithmetic


section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj

theorem primeIdealProduct_emultiplicity (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))

theorem primeIdealProduct_exponents_eq
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : (∏ i ∈ B, P i ^ v i) = ∏ i ∈ C, P i ^ w i) : v = w := by
  funext i
  have he := congrArg (fun I => emultiplicity (P i) I) heq
  rw [primeIdealProduct_emultiplicity P hinj,primeIdealProduct_emultiplicity P hinj] at he
  have hB : (if i ∈ B then (v i : ℕ∞) else 0) = (v i : ℕ∞) := by
    by_cases h : i ∈ B <;> simp [h,hv i]
  have hC : (if i ∈ C then (w i : ℕ∞) else 0) = (w i : ℕ∞) := by
    by_cases h : i ∈ C <;> simp [h,hw i]
  simp_all

end

theorem primeProduct_span_exponents_eq {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : Ideal.span {FirstPassCubeLabels.primeProduct p B v} =
      Ideal.span {FirstPassCubeLabels.primeProduct p C w}) : v = w := by
  apply primeIdealProduct_exponents_eq (fun i => Ideal.span {p i}) hinj B C v w hv hw
  simpa only [FirstPassCubeLabels.primeProduct,FiniteGaussPhase.span_finset_prod,
    ←Ideal.span_singleton_pow] using heq

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ConcreteTraceCRT
open IdealMobiusDivisorSum

theorem divisor_dyadic_sum_le (S T : Finset (Ideal O)) (N : ℝ)
    (f : Ideal O → Ideal O → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j k : Fin (columnDyadicLength N + 1),
      (divisorDyadicBin S N j).Nonempty → (divisorDyadicBin T N k).Nonempty →
      (∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E) ≤ C) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) ≤ ((columnDyadicLength N + 1 : ℕ) : ℝ)^2 * C := by
  rw [sum_divisorDyadicRectangles S T N f]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases hS : (divisorDyadicBin S N j).Nonempty
      · by_cases hT : (divisorDyadicBin T N k).Nonempty
        · exact hb j k hS hT
        · simpa only [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty, Finset.sum_const_zero] using hC
      · simpa only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty] using hC
    _ = _ := by simp; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def largePrincipalWindow (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ)*(Ideal.absNorm E : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalWindow_le (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) :
    largePrincipalWindow S T rows left right a b M P ≤
      principalCorrectionAt S T rows left right a b M := by
  classical
  unfold principalCorrectionAt
  rw [sum_two_subtype_pools S T (fun D E => ∑ i,
    (Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)))*
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)]
  unfold largePrincipalWindow
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> first | exact le_rfl | positivity

section
variable {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
include α hexp deltaLoss hδ ε hε S T

theorem HasSieveExponent.large_principal_window 
    (D₁ D₂ B N M V : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hV : 0 ≤ V) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (V+Real.sqrt M*B^(α-1/2)) := by
  classical
  by_cases hc : Real.sqrt (M/B)*N ≤ V*(D₁*D₂)
  · exact (largePrincipalWindow_le S T rows left right a b M P).trans
      (HasSieveExponent.large_principal_correction ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
        rows left right hr hl hri hrows hleft hright a b hexp deltaLoss hδ hD₁N hD₂N V hc)
  · have hz : largePrincipalWindow S T rows left right a b M P = 0 := by
      unfold largePrincipalWindow
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        have hlo := hP D hD E hE i hp
        have hhi : (Ideal.absNorm (D*E):ℝ) ≤ 4*(D₁*D₂) := by
          rw [map_mul, Nat.cast_mul]
          calc
            _ ≤ (2*D₁)*(2*D₂) := mul_le_mul (hS D hD).2 (hT E hE).2 (by positivity) (by linarith)
            _ = _ := by ring
        nlinarith
      simp only [hn, ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.large_principal_pool 
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  classical
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.large_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M V
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hV
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P
      (fun D hD E hE i hp => hP D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 i hp)
end


end

open ConcreteTraceCRT
open IdealMobiusDivisorSum

theorem finite_principal_triangle
    {m n p D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d‖ ≤
      ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d) =
      ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalDivisorCorrection (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

def largePrincipalProductAt (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalProductAt_le_window (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    largePrincipalProductAt K rows left right a b M P ≤
      largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P
    (fun d i _ _ => ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ))
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  unfold largePrincipalWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hd : D*E ∈ K
  · by_cases hi : P (D*E) i
    · simp only [hd, hi, and_self, ite_true, map_mul, Nat.cast_mul]
      simp only [←Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/
          ((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)) by positivity)]
      ring
    · simp only [hd, hi, and_false, ite_true, ite_false]
  · simp only [hd, false_and, ite_false]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma principalDivisorCorrection_le_product (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hK : ∀ j k d, d ∣ left j*right k → d ∈ K) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      largePrincipalProductAt K rows left right a b M P := by
  classical
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d.val:ℝ):ℝ):ℂ) else 0 else 0
  have he : principalDivisorCorrection rows left right a b M P =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ)*A i j k d := by
    unfold principalDivisorCorrection
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  unfold largePrincipalProductAt
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then
    if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.principal_divisor_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm d:ℝ)) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hl0 := fun j => (hleft j).1.1
  have hr0 := fun k => (hright k).1.1
  have hp0 : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hl0 x.1) (hr0 x.2)
  have hk :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hp0 (j,k) d hd
  calc
    _ ≤ largePrincipalProductAt K rows left right a b M P :=
      principalDivisorCorrection_le_product K rows left right a b M P hl0 hr0 hk
    _ ≤ largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) :=
      largePrincipalProductAt_le_window K S T rows left right a b M P hl0 hr0
        (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
    _ ≤ _ := hexp.large_principal_pool deltaLoss hδ ε hε S T B N M V hB hN hM hV
      (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
      (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
      rows left right hr hl hri hrows hleft hright a b _
      (fun D _ E _ i hp => hP (D*E) i hp.2)

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section

open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

@[ext] structure CubeCoordinates (ι : Type*) where
  leftExponent : ι →₀ ℕ
  rightExponent : ι →₀ ℕ
  leftDivisor : Finset ι
  rightDivisor : Finset ι

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

section
variable (x : CubeCoordinates ι)
include x

def support  : Finset ι :=
  x.leftExponent.support ∪ x.rightExponent.support

def leftBit  (i : ι) : Bool := decide (i ∈ x.leftDivisor)
def rightBit  (i : ι) : Bool := decide (i ∈ x.rightDivisor)

def Admissible  : Prop :=
  x.leftDivisor ⊆ x.support ∧ x.rightDivisor ⊆ x.support

section
variable (i : ι)
include i

theorem support_pos  (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

section
variable (hi : i ∉ x.support)
include hi

theorem left_off  :
    x.leftExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv))

theorem right_off  :
    x.rightExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv))
end
end
end


section
variable (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible)
include p x hx

theorem aLabel_left  :
    aLabel p x.support x.leftBit = ∏ i ∈ x.leftDivisor,p i := by
  simp only [aLabel,primeProduct,leftBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.leftDivisor)=x.leftDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.1 hi)
  rw [he]

theorem aLabel_right  :
    aLabel p x.support x.rightBit = ∏ i ∈ x.rightDivisor,p i := by
  simp only [aLabel,primeProduct,rightBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.rightDivisor)=x.rightDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.2 hi)
  rw [he]
end


end CubeCoordinates

@[ext] structure GlobalSecondData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι
  source : SecondExpansionData ι

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end


open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj






