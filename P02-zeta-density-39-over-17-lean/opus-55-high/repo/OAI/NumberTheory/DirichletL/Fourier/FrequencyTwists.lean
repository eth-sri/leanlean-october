module
public import OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson
public import OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
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

namespace JointLogSeparation

open MeasureTheory
open scoped Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_temperate (t : ℝ) : (logPhase t).HasTemperateGrowth := by
  have hl : Function.HasTemperateGrowth (fun x : ℝ => (2 * Real.pi * t) * x) := by
    fun_prop
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hl

def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (logPhase t) g

@[simp] lemma frequencyTwist_apply (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    frequencyTwist g t x = logPhase t x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (logPhase_temperate t) g x

lemma logPhase_add_frequency (t s x : ℝ) :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  pm_5155 logPhase Complex.exp_add

def phaseDerivative (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

lemma logPhase_hasDerivAt (t x : ℝ) :
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

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
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

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  pm_93 phaseDerivative norm_mul Complex.norm_real Complex.norm_I mul_one
  simp_all

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  pm_93 norm_mul norm_pow phaseDerivative_norm logPhase_norm mul_one

def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g

section
variable (g : 𝓢(ℝ, ℂ))
include g
lemma derivativeSeminormSum_nonneg (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  simp_all
  grind

theorem frequencyTwist_seminorm_bound (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; simp_all
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      pm_223 Finset.mul_sum i hi logPhase_iteratedFDeriv_norm
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      pm_8270 n
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      pm_7230

theorem frequencyTwist_seminorm_polynomial (t : ℝ) (k n : ℕ) :
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
end

def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))

section
variable (g : 𝓢(ℝ, ℂ))
include g
lemma twistSourceBound_nonneg (K : ℕ) : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist (t : ℝ) (K : ℕ) :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  pm_8270 K
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
end

end JointLogSeparation

section

open scoped Classical SchwartzMap FourierTransform
open MeasureTheory
namespace JointLogSeparation
open FourierBridge

end JointLogSeparation

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)

end SecondPassArithmetic
end

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

section
variable (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O)
include Ψ z a
lemma secondRayMinus_norm_le :
    ‖secondRayMinus Ψ z a‖ ≤ ‖Ψ a‖ := by
  pm_93 secondRayMinus MonoidHom.mul_apply norm_mul conjugateRayMonoid_apply norm_star
  pm_933

lemma secondRayPlus_norm_le :
    ‖secondRayPlus Ψ z a‖ ≤ ‖Ψ a‖ := by
  pm_316 secondRayPlus MonoidHom.mul_apply norm_mul conjugateRayMonoid_apply rayMonoid_apply norm_star
  pm_933
end

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (m c d e k : O) (S : Finset ι) :
    ‖secondPreColumn p hp hcop hg Ψ m c d e k (fun _ => 1) S‖ ≤ ‖Ψ (∏ i ∈ S, p i)‖ := by
  pm_3444 S m
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one,
    columnCoefficient_norm_one p hp hcop hg hc S]
  calc
    _ ≤ 1 * ‖Ψ (∏ i ∈ S, p i)‖ * 1 * 1 ^ 4 * 1 * 1 * 1 * 1 := by
      pm_8573 S
    _ = _ := by ring

theorem secondCommonWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (S : Finset ι) :
    ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ S‖ ≤
      ‖Ψ₁ (∏ i ∈ S, p i)‖ * ‖Ψ₂ (∏ i ∈ S, p i)‖ := by
  pm_3509
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) S‖ = 1 := by
    pm_754 S
  pm_93 secondCommonWeight norm_mul norm_star hmu one_mul
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
    pm_3445
    pm_3397 χ hχ η hη
    ring
  rw [heq]
  exact mul_le_mul hQ (pow_le_pow_left₀ (by positivity) hG 2) (by positivity) (by norm_num)

end SecondPassArithmetic

end

end OAI
