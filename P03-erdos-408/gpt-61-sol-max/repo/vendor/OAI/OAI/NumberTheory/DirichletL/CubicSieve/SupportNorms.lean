module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
public import OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes

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

section
 
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem sourceSupportMobius_norm (E : Finset ι) :
    ‖supportMobius (fun i => Ideal.span {p i}) E‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj E)
  simp only [norm_mul, norm_one] at h
  nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) E)]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm  E  :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

include hp hinj in
theorem secondSourceCommonCoefficient_norm_le_one
     Ψ  (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)  m c d   G E  :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ 1 := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hN := primeProductNorm_ge_one p hp E
  have hμ := sourceSupportMobius_norm p hinj E
  change ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ)‖ = 1 at hμ
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), primeSubsetGenerator_norm_eq_productNorm,
    Complex.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp E).le, hμ]
  exact (mul_le_of_le_one_left (div_nonneg zero_le_one (zero_le_one.trans hN))
    hA2).trans ((div_le_one (by linarith)).mpr hN)

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)  m c d   H   S  :
    ‖secondInputCoefficient p hg Ψ m c d H S‖ ≤ ‖H S‖ := by
  have he : secondInputCoefficient p hg Ψ m c d H S =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) S * H S := by
    simp only [secondInputCoefficient, mul_one]
  rw [he, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((secondInputCoefficient_norm_le p hg Ψ m c d S).trans (hΨ _))

end
section

theorem tail_radial_scalar_le (Y E n lengthScale H P : ℝ)  A 
    (hY : 0 < Y) (hE : 0 < E) (hn : 1 ≤ n) (hL : 1 ≤ lengthScale)
    (hden : E*n^2 ≤ lengthScale^3) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    (Y/n) * (P / ((min 1 (Y/(E*n^2)))^2 * (1+H)^A)) ≤
      Y*P*(1+lengthScale^3/Y)^2 / (1+H)^A := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 0 < E*n^2 := mul_pos hE (sq_pos_of_pos hn0)
  have hs : 0 < Y/(E*n^2) := div_pos hY he
  have hr : 0 ≤ lengthScale^3/Y := div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hY.le
  have hi : (min 1 (Y/(E*n^2)))⁻¹ ≤ 1+lengthScale^3/Y := by
    by_cases h : 1 ≤ Y/(E*n^2)
    · rw [min_eq_left h, inv_one]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_div]
      exact (div_le_div_of_nonneg_right hden hY.le).trans (by linarith)
  have hi0 : 0 ≤ (min 1 (Y/(E*n^2)))⁻¹ := inv_nonneg.mpr (le_min zero_le_one hs.le)
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  have hyn : Y/n ≤ Y := div_le_self hY.le hn
  calc
    _ = (Y/n)*P*((min 1 (Y/(E*n^2)))⁻¹)^2 / (1+H)^A := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ _ := by
      gcongr <;> first | assumption | positivity | linarith

theorem sum_pair_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]  U  :
    (∑ a ∈ s, ∑ b ∈ s, if P a ∧ P b then U else 0) =
      ((s.filter P).card : ℝ)^2 * U := by
  calc
    _ = ∑ a ∈ s.filter P, ∑ b ∈ s.filter P, U := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      aesop
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring



 
open FirstPassCubeLabels (columnLog primeProductNorm)

end

 
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

 
namespace CanonicalQuadraticSieve
open     EisensteinSchwartzPoisson

section
variable (M F B b N D₁ D₂ d e U : ℝ) (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : B / 2 ≤ b) (hN : 0 ≤ N) (hU : 0 ≤ U) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)


include hM hB hb in
theorem sqrt_scale_shell_upper      
      : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
  simpa only [one_mul, div_one] using principal_middle_prefactor_bound
    M B b 1 1 1 1 hM hB hb (by norm_num) le_rfl (by norm_num) le_rfl

include hM hB hb hU hD₁ hD₂ hd he in
theorem original_middle_rectangle_upper  
           
           
    (hcut : d * e ≤ U * Real.sqrt (M / b)) :
    D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B) := by
  calc
    _ ≤ d * e := mul_le_mul hd he hD₂ (hD₁.trans hd)
    _ ≤ U * Real.sqrt (M / b) := hcut
    _ ≤ U * (2 * Real.sqrt (M / B)) :=
      mul_le_mul_of_nonneg_left (sqrt_scale_shell_upper M B b hM hB hb) hU
    _ = _ := by ring

include hM hF hB hb hN hU hD₁ hD₂ hd he in
theorem dual_middle_rectangle_upper  
               
           
    (hcut : d * e ≤ U * (N * Real.sqrt (F / (M * b)))) :
    D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B))) := by
  have harg (z : ℝ) : F / (M * z) = (F / M) / z := by ring
  simp only [harg] at hcut ⊢
  have hh := original_middle_rectangle_upper (F / M) B b D₁ D₂ d e (U * N)
    (div_pos hF hM) hB hb (mul_nonneg hU hN) hD₁ hD₂ hd he
    (by simpa only [mul_assoc] using hcut)
  simpa only [mul_assoc] using hh

end

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

def dualMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
     a   b   M   P   h  :
    0 ≤ originalMiddleWindowAt W S T rows left right a b M P h ∧
    originalMiddleWindowAt W S T rows left right a b M P h ≤
      originalMiddleAt W S T rows left right a b M h := by
  classical
  constructor
  · unfold originalMiddleWindowAt
    positivity
  · unfold originalMiddleWindowAt originalMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
     a   b   M F   P   h  :
    0 ≤ dualMiddleWindowAt W S T rows left right a b M F P h ∧
    dualMiddleWindowAt W S T rows left right a b M F P h ≤
      dualMiddleAt W S T rows left right a b M F h := by
  classical
  constructor
  · unfold dualMiddleWindowAt
    positivity
  · unfold dualMiddleWindowAt dualMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)  h 
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    originalMiddleWindowAt W S T rows left right a b M P h = 0 := by
  classical
  simp only [originalMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)  h 
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    dualMiddleWindowAt W S T rows left right a b M F P h = 0 := by
  classical
  simp only [dualMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

end CanonicalQuadraticSieve

end

end OAI
