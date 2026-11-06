module

public import RequestProject.PhysicalDrivenMoments
public import RequestProject.Transmutation
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Absolute convergence and inversion of the actual factorial gauge

The exponential row bound is the only growth hypothesis. The inverse is
an equality of convergent complex series at a fixed energy and point.
Regrouping is justified by absolute convergence before the finite
alternating factorial identity is applied.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Finset

def factorialGauge (z : ℂ) (d : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑' l : ℕ, (-z) ^ l / (l.factorial : ℂ) * d (l + j)

def factorialGaugeInverseTerm (z : ℂ) (d : ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  z ^ p.1 / (p.1.factorial : ℂ) *
    ((-z) ^ p.2 / (p.2.factorial : ℂ) * d (p.2 + p.1))

variable (z : ℂ) (d : ℕ → ℂ) {C a : ℝ} (n : ℕ)

theorem summable_norm_factorialGaugeInverseTerm
    (ha : 0 ≤ a)
    (hd : ∀ n, ‖d n‖ ≤ C * a ^ n) :
    Summable (fun p  => ‖factorialGaugeInverseTerm z d p‖) := by
  let r  := fun n => (‖z‖ * a) ^ n / n.factorial
  have hr₀ (n : ℕ) : 0 ≤ r n := by positivity
  have hr : Summable (fun n => ‖r n‖) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hr₀ _)]
    exact Real.summable_pow_div_factorial (‖z‖ * a)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((summable_mul_of_summable_norm  hr hr).mul_left C)
  intro p
  unfold factorialGaugeInverseTerm
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖z ^ p.1 / p.1.factorial‖ *
        (‖(-z) ^ p.2 / p.2.factorial‖ * (C * a ^ (p.2 + p.1))) := by
      gcongr
      simp_all
    _ = _ := by
      simp 
      ring

private theorem complex_alternating_factorial_sum :
    ∑ l ∈ range (n + 1), (-1 : ℂ) ^ l /
        ((l.factorial : ℂ) * ((n - l).factorial : ℂ)) =
      if n = 0 then 1 else 0 := by
  have h := congrArg (fun q : ℚ => (q : ℂ)) (alternating_factorial_sum n)
  simp_all [apply_ite]

private theorem factorialGaugeInverseTerm_antidiagonal
    :
    ∑ p ∈ antidiagonal n, factorialGaugeInverseTerm z d p =
      if n = 0 then d 0 else 0 := by
  have hswap := Nat.sum_antidiagonal_swap (n := n)
    (f := factorialGaugeInverseTerm z d)
  rw [← hswap]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have ht (l : ℕ) (hl : l ∈ range (n + 1)) :
      factorialGaugeInverseTerm z d ((l, n - l).swap) =
        (z ^ n * d n) * ((-1 : ℂ) ^ l /
          ((l.factorial : ℂ) * ((n - l).factorial : ℂ))) := by
    have hln : l ≤ n := by simp_all
    have hadd : n - l + l = n := Nat.sub_add_cancel hln
    have hpow : z ^ (n - l) * z ^ l = z ^ n := by grind
    unfold factorialGaugeInverseTerm
    simp only [Prod.swap]
    rw [show -z = (-1 : ℂ) * z by ring, mul_pow,
      show l + (n - l) = n by omega]
    grind
  rw [sum_congr rfl ht, ← mul_sum, complex_alternating_factorial_sum]
  simp_all

/-- A genuinely convergent factorial inverse, rather than a formal
coefficient identity. The original zeroth row is retained. -/
theorem factorialGauge_inverse
    (ha : 0 ≤ a)
    (hd : ∀ n, ‖d n‖ ≤ C * a ^ n) :
    (∑' j : ℕ, z ^ j / j.factorial * factorialGauge z d j) = d 0 := by
  let T  := factorialGaugeInverseTerm z d
  have hs  :=
    (summable_norm_factorialGaugeInverseTerm z d ha hd).of_norm
  have hg : (∑' j : ℕ, z ^ j / j.factorial * factorialGauge z d j) =
      ∑' p : ℕ × ℕ, T p := by
    rw [hs.tsum_prod]
    apply tsum_congr
    intro j
    exact tsum_mul_left.symm
  rw [hg, ← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq T]
  have hσ : Summable (fun p : Σ n : ℕ, antidiagonal n => T p.2) :=
    HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hs
  change (∑' p : Σ n : ℕ, antidiagonal n, T p.2) = d 0
  rw [hσ.tsum_sigma]
  simp_rw [tsum_fintype, sum_coe_sort, T, factorialGaugeInverseTerm_antidiagonal]
  simp

/-- The inverse applies directly to the actual Hilbert-space driven
rows, with their proved exponential bound and sqrt(2) zeroth scale. -/
theorem physicalDrivenGauge_inverse
    (γ : ℝ → ℂ) (E : ℝ) (y : ℝ → Ell2) (θ : ℝ) :
    (∑' j : ℕ, physicalDrivenCentered γ θ ^ j / j.factorial *
      physicalDrivenGauge γ E y j θ) = physicalDrivenRow y 0 θ := by
  simpa only [factorialGauge, physicalDrivenGauge, physicalDrivenGaugeTerm,
    physicalDrivenPower, physicalDrivenScaledRow, pow_zero, one_mul] using factorialGauge_inverse (physicalDrivenCentered γ θ)
    (fun n => physicalDrivenScaledRow E y n θ)
    (C := 2 * ‖y θ‖)  (norm_nonneg _)
    (fun n => (norm_physicalDrivenScaledRow_le E y n θ).trans_eq (by ring))

end PolyaNeumann

end
