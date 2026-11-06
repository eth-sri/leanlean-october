module
public import OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
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

namespace TraceLambdaPhase

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate

theorem eisLam_sq : eisLam ^ 2 = (-3 : ℂ) := by
  change (1 + 2 * omega3) ^ 2 = -3
  linear_combination 4 * omega3_sq

theorem exp_minus_four_pi_div_three :
    Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) = omega3 := by
  have hshift : Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) =
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I / 3) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [hshift]
  have harg : ((2 : ℂ) * Real.pi * Complex.I / 3) =
      (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold omega3
  push_cast
  ring

end TraceLambdaPhase

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT TraceLambdaPhase

end ActualEisensteinCubic

namespace PoissonFirstLocal
open scoped Classical

end PoissonFirstLocal

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT TraceLambdaPhase

end

noncomputable def finiteSquarefreeRow
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  pm_1327 hex a
  · obtain ⟨i, hi, hai⟩ := hex
    rw [ite_eq_left ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [ite_eq_right hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

section
variable {ι N : Type*} [DecidableEq N] (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hgood : ∀ i, lambda ∉ P i) (columns : Finset N) (support : N → Finset ι) (weight : N → ℂ) (a : O)
include ι N P hgood columns support weight a
theorem finiteSquarefreeRow_difference :
    (∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6)) =
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), weight n := by
  classical
  rw [← Finset.sum_sub_distrib]
  pm_223 Finset.sum_filter n hn finiteSquarefreeRow_sixth_power
  by_cases h : ∃ i ∈ support n, a ∈ P i <;> simp [h]

theorem finiteSquarefreeRow_difference_norm :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6))‖ ≤
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), ‖weight n‖ := by
  rw [finiteSquarefreeRow_difference]
  exact norm_sum_le _ _
end

end ActualEisensteinCubic

namespace AnalyticBridge

end AnalyticBridge

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

end ShortDraftCusp

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_quarter_trace (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) =
      Complex.I ^ b := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / 4) = star z / 4 := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / 4) =
      (b : ℂ) * (Real.pi / 2 * Complex.I) := by
    rw [← add_div, hL]
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

noncomputable def breveGaussianFourTerms (a b : ℤ) : ℂ :=
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  (ShortDraftTrace.breveE (0 : ℂ) +
      ShortDraftTrace.breveE (((-c) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * omega3 ^ 2) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * (1 + omega3) ^ 2) / eisLam) / 4)) / 2

theorem breveGaussianFourTerms_formula (a b : ℤ) :
    breveGaussianFourTerms a b =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  pm_256 c a b omega3
  have hfirst : ShortDraftTrace.breveE (((-c) / eisLam) / 4) =
      Complex.I ^ (-b) := by
    have hc : -c = ((-a : ℤ) : ℂ) + ((-b : ℤ) : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      ring
    rw [hc]
    exact breveE_quarter_trace (-a) (-b)
  have hsecond : ShortDraftTrace.breveE
      (((-c * omega3 ^ 2) / eisLam) / 4) = Complex.I ^ a := by
    have hc : -c * omega3 ^ 2 = ((a-b : ℤ) : ℂ) + (a : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      linear_combination -(a : ℂ) * omega3_sq -
        (b : ℂ) * (omega3 - 1) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace (a-b) a
  have hthird : ShortDraftTrace.breveE
      (((-c * (1 + omega3) ^ 2) / eisLam) / 4) =
      Complex.I ^ (b-a) := by
    have hω : (1 + omega3) ^ 2 = omega3 := by
      linear_combination omega3_sq
    have hc : -c * (1 + omega3) ^ 2 =
        (b : ℂ) + ((b-a : ℤ) : ℂ) * omega3 := by
      rw [hω]
      dsimp [c]
      push_cast
      linear_combination -(b : ℂ) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace b (b-a)
  dsimp [breveGaussianFourTerms]
  rw [hfirst, hsecond, hthird]
  simp only [map_zero_eq_one]

end ActualEisensteinCubic

end

end OAI
