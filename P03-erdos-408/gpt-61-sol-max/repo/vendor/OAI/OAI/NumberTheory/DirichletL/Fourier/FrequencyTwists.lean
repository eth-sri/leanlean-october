module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson
public import OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation

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
 
 
 
 
 

namespace JointLogSeparation

 
 
open FourierBridge

lemma logPhase_temperate  t  : (logPhase t).HasTemperateGrowth := by
  have hl : Function.HasTemperateGrowth (fun x : ℝ => (2 * Real.pi * t) * x) := by
    simpa [Pi.smul_def, smul_eq_mul] using (((2 * Real.pi * t) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth)
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hl

def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ)  :=
  SchwartzMap.smulLeftCLM ℂ (logPhase t) g

@[simp] lemma frequencyTwist_apply  g   t x  :
    frequencyTwist g t x = logPhase t x * g x := SchwartzMap.smulLeftCLM_apply_apply (logPhase_temperate t) g x

lemma logPhase_add_frequency  t s x  :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring





def phaseDerivative (t : ℝ)  := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

lemma logPhase_hasDerivAt  t x  :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv  t   n  :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm  t  : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp_all [phaseDerivative]

lemma logPhase_iteratedFDeriv_norm  t x   n  :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ)  :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g

lemma derivativeSeminormSum_nonneg  g   k n  :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum  g   k n i  (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound  g   t   k n  :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            bound) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial  g   t   k n  :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ)  :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))

lemma twistSourceBound_nonneg  g   K  : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist  g   t   K  :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ K := Finset.mem_range_succ_iff.mp hi
  have hb := add_le_add (frequencyTwist_seminorm_polynomial g t 0 i)
    (frequencyTwist_seminorm_polynomial g t (volume : Measure ℝ).integrablePower i)
  have hn : 0 ≤ (2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))
  calc
    _ ≤ ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
        (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i)) *
          (1 + ‖t‖)^i := by convert hb using 1 ; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hin) hn

end JointLogSeparation

section

 
 
namespace JointLogSeparation
open FourierBridge

end JointLogSeparation

namespace SecondPassArithmetic
 
open FirstPassCubeLabels (columnLog)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι)  :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)

end SecondPassArithmetic
end

 
namespace SecondPassArithmetic



 
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

lemma secondRayMinus_norm_le  Ψ   z   a  :
    ‖secondRayMinus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayMinus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

lemma secondRayPlus_norm_le  Ψ   z   a  :
    ‖secondRayPlus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayPlus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
     Ψ   m c d e k   S  :
    ‖secondPreColumn p hp hcop hg Ψ m c d e k (fun _ => 1) S‖ ≤ ‖Ψ (∏ i ∈ S, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one,
    columnCoefficient_norm_one p hp hcop hg hc S]
  calc
    _ ≤ 1 * ‖Ψ (∏ i ∈ S, p i)‖ * 1 * 1 ^ 4 * 1 * 1 * 1 * 1 := by
      gcongr <;> exact finiteSquarefreeRow_norm_le_one _ hg S _
    _ = _ := by ring

theorem secondCommonWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
     Ψ₁ Ψ₂   m r c d e k₁ k₂   S  :
    ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ S‖ ≤
      ‖Ψ₁ (∏ i ∈ S, p i)‖ * ‖Ψ₂ (∏ i ∈ S, p i)‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) S‖ = 1 := by
    have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S)
    simp only [norm_mul, norm_one] at h
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) S)]
  simp only [secondCommonWeight, norm_mul, norm_star, hmu, one_mul]
  exact mul_le_mul (secondPreColumn_norm_le p hp hcop hg hc Ψ₁ _ _ _ _ _ S)
    (secondPreColumn_norm_le p hp hcop hg hc Ψ₂ _ _ _ _ _ S) (norm_nonneg _) (norm_nonneg _)

end

theorem secondRayCoefficient_mass :
    (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) ≤ 512 * 32 ^ 2 := by
  have hG := RayFourExpansion.gCoeff_sum_norm_le
  have hQ := RayFourExpansion.crossCoeff_sum_norm_le
  have heq : (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) =
      (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ a : RayCharacter, ‖gCoeff a‖) ^ 2 := by
    simp only [secondRayCoefficient, Fintype.sum_prod_type, norm_mul, norm_star, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    ring
  rw [heq]
  exact (by gcongr <;> first | assumption | positivity | linarith)

end SecondPassArithmetic

end

end OAI
