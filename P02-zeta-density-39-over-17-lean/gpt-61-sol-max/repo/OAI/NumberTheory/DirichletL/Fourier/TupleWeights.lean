module
import Mathlib
public import OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks
public import OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer

@[expose] public section

namespace OAI

noncomputable section

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
                        

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform


namespace SecondPassIntegration

section
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
open FourierBridge (logPhase)

def tupleOuterWeight (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (q : Frequency) (x : OldTuple) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassIntegration

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
namespace JointLogSeparation

lemma sqrt_exp_half (s : ℝ) : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos s).le (Real.exp_pos (s / 2)).le).mpr
  rw [← Real.exp_add]
  simp

end JointLogSeparation


end

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma lambdaIdeal_maximal : (Ideal.span {lambda} : Ideal O).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible PrimaryIdealUnitReindex.lambda_prime_actual.irreducible

lemma twoIdeal_maximal : (Ideal.span {(2 : O)} : Ideal O).IsMaximal := by
  simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal

lemma twoIdeal_characteristic : ringChar (O ⧸ Ideal.span {(2 : O)}) = 2 := by
  rw [← Ideal.span_singleton_neg (2 : O)]
  exact cubicTwoIdeal_residue_char

theorem supported_span_iff (z : O) :
    Supported (Ideal.span {z}) ↔ ¬lambda ∣ z ∧ ¬(2 : O) ∣ z := by
  constructor
  · intro h
    constructor
    · intro hz
      have hm : (Ideal.span {lambda} : Ideal O) ∈
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {z}) := by
        apply (Ideal.mem_normalizedFactors_iff h.1).mpr
        exact ⟨lambdaIdeal_maximal.isPrime,
          (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hz)⟩
      exact (h.2 _ hm).1 (Ideal.subset_span (by simp))
    · intro hz
      have hm : (Ideal.span {(2 : O)} : Ideal O) ∈
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {z}) := by
        apply (Ideal.mem_normalizedFactors_iff h.1).mpr
        exact ⟨twoIdeal_maximal.isPrime,
          (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hz)⟩
      exact (h.2 _ hm).2 twoIdeal_characteristic
  · rintro ⟨hLam, htwo⟩
    have hz : z ≠ 0 := fun heq => hLam (heq ▸ dvd_zero lambda)
    refine ⟨Ideal.span_singleton_eq_bot.not.mpr hz, ?_⟩
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzP : z ∈ P := ((Ideal.mem_normalizedFactors_iff
      (Ideal.span_singleton_eq_bot.not.mpr hz)).mp hP).2 (Ideal.subset_span (by simp))
    constructor
    · intro hlambdaP
      have heq := maximal_ideal_eq_span_of_mem P inferInstance lambda lambdaIdeal_maximal hlambdaP
      rw [heq] at hzP
      exact hLam (Ideal.mem_span_singleton.mp hzP)
    · intro hchar
      have htwoP : (2 : O) ∈ P := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hzero : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hchar])
        exact hzero
      have heq := maximal_ideal_eq_span_of_mem P inferInstance (2 : O) twoIdeal_maximal htwoP
      rw [heq] at hzP
      exact htwo (Ideal.mem_span_singleton.mp hzP)

def badPrime (i : Bool) : Ideal O := if i then Ideal.span {(2 : O)} else Ideal.span {lambda}

instance badPrime_maximal (i : Bool) : (badPrime i).IsMaximal := by
  cases i
  · exact lambdaIdeal_maximal
  · exact twoIdeal_maximal

theorem badPrime_mask (z : O) :
    rowCoprimeMask badPrime Finset.univ z = if Supported (Ideal.span {z}) then 1 else 0 := by
  rw [supported_span_iff]
  simp only [rowCoprimeMask, Finset.mem_univ, badPrime, true_and, Bool.exists_bool, Bool.false_eq_true, ite_false, mem_span_singleton, ite_true]
  by_cases hLam : lambda ∣ z <;> by_cases htwo : (2 : O) ∣ z <;> simp [hLam, htwo]

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

theorem highKernelNorm_mono {M N K M' N' K' : ℝ}
    (hM : M ≤ M') (hN : N ≤ N') (hK : K' ≤ K) :
    highKernelNorm M N K ≤ highKernelNorm M' N' K' := by
  let r : highKernelRange M K → highKernelRange M' K' := fun I => ⟨I.val, by
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp I.property
    exact mem_highKernelRange.mpr ⟨hs, hn.trans hM, hK.trans_lt hk⟩⟩
  have hr : Function.Injective r := fun I J h =>
    Subtype.ext (congrArg (fun I : highKernelRange M' K' => I.val) h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hr
    (rangeInclusion hN) (rangeInclusion_injective hN) (highKernelMatrix M' N' K')
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

section
variable {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
include m n

theorem highKernel_family_squared_norm_le 
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M N K := by
  let r : m → highKernelRange M K := fun i => ⟨rows i, hrows i⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (highKernelMatrix M N K)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2
section
variable (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
include D hD rows cols hr hc

theorem highKernel_quotient_family_squared_norm_le 
    (hdiv : ∀ j, D ∣ cols j) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  apply highKernel_family_squared_norm_le rows (fun j => idealQuotient D (cols j)) hr
  · intro j k heq
    exact hc (idealQuotient_injective_on D (hdiv j) (hdiv k) heq)
  · exact hrows
  · intro j
    exact ⟨admissible_idealQuotient (hcols j).1 (hdiv j),
      idealQuotient_norm_le hD (hdiv j) N (hcols j).2⟩

theorem highKernel_quotientMatrix_squared_norm_le  (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  let S := Finset.univ.filter (fun j => D ∣ cols j)
  let A : Matrix m S ℂ := fun i j =>
    quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i))
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
    apply highKernel_quotient_family_squared_norm_le D hD rows (fun j : S => cols j.val) hr
      (hc.comp Subtype.val_injective)
    · intro j
      exact (Finset.mem_filter.mp j.property).2
    · exact hrows
    · intro j
      exact hcols j.val
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (highKernelNorm_nonneg _ _ _)
  intro a
  have hinner (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, A i j * a j.val := by
    change (∑ j, (if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0) * a j) =
      ∑ j : S, quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i)) * a j.val
    rw [Finset.sum_coe_sort S (fun j : n =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) * a j)]
    simp only [S, Finset.sum_filter, ite_mul, zero_mul]
  simp_rw [hinner]
  have henergy := FiniteSieveOperator.energy_bound A (fun j : S => a j.val)
  apply henergy.trans
  calc
    _ ≤ highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (highKernelNorm_nonneg _ _ _)
      rw [Finset.sum_coe_sort S (fun j : n => ‖a j‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)
end
end


open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator

def totalQuotient (D I : Ideal O) : Ideal O := if D ∣ I then idealQuotient D I else 1

section
variable (D I : Ideal O) (hI : Admissible I)
include D I hI

theorem totalQuotient_ne_zero  : totalQuotient D I ≠ 0 := by
  by_cases h : D ∣ I
  · simpa only [totalQuotient, ite_eq_left h] using (admissible_idealQuotient hI h).1
  · simp [totalQuotient, h]

theorem totalQuotient_norm_le 
    (N : ℝ) (hN : 1 ≤ N) (hIN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (totalQuotient D I) : ℝ) ≤ N := by
  by_cases h : D ∣ I
  · rw [totalQuotient, ite_eq_left h]
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hn (map_dvd Ideal.absNorm (idealQuotient_dvd h)))).trans hIN
  · simpa only [totalQuotient, ite_eq_right h, map_one, Nat.cast_one] using hN
end


theorem gcd_eq_iff_quotient_coprime (D I J : Ideal O) (hD : D ≠ 0)
    (hDI : D ∣ I) (hDJ : D ∣ J) :
    gcd I J = D ↔ IsCoprime (idealQuotient D I) (idealQuotient D J) := by
  have he : gcd I J = D * gcd (idealQuotient D I) (idealQuotient D J) := by
    calc
      gcd I J = gcd (D * idealQuotient D I) (D * idealQuotient D J) := by
        rw [idealQuotient_mul hDI, idealQuotient_mul hDJ]
      _ = _ := by rw [_root_.gcd_mul_left, normalize_eq]
  rw [he, Ideal.isCoprime_iff_gcd]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (h.trans (mul_one D).symm)
  · intro h
    rw [h, mul_one]

def gcdTerm {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (i : m) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
      (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0

def gcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, gcdTerm D rows cols a i j k

theorem gcdTerm_eq_quotient {m n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (i : m) (j k : n) :
    gcdTerm D rows cols a i j k =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i))) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [gcdTerm, totalQuotient, quotientMatrix, ite_eq_left hj, ite_eq_left hk]
      rw [← gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, quadraticRow_divisor_factor _ D (hcols j) hj,
          quadraticRow_divisor_factor _ D (hcols k) hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [gcdTerm, ite_eq_right hg]
      simp [quotientMatrix, hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [gcdTerm, ite_eq_right hg]
    simp [quotientMatrix, hj]






