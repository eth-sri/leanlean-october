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


noncomputable section

namespace PolyaNeumann

open Finset

def factorialGauge (z : ℂ) (d : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑' l : ℕ, (-z) ^ l / (l.factorial : ℂ) * d (l + j)

def factorialGaugeInverseTerm (z : ℂ) (d : ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  z ^ p.1 / (p.1.factorial : ℂ) *
    ((-z) ^ p.2 / (p.2.factorial : ℂ) * d (p.2 + p.1))

theorem factorialGauge_inverse
    z d {C a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ n, ‖d n‖ ≤ C * a ^ n) :
    (∑' j : ℕ, z ^ j / (j.factorial : ℂ) * factorialGauge z d j) = d 0 := by
  let T : ℕ × ℕ → ℂ := factorialGaugeInverseTerm z d
  have hs :=
    (show Summable (fun p : ℕ × ℕ => ‖factorialGaugeInverseTerm z d p‖) by
      let r : ℕ → ℝ := fun n => (‖z‖ * a) ^ n / n.factorial
      have hr₀ n : 0 ≤ r n := by dsimp only [r]; positivity
      have hr : Summable (fun n => ‖r n‖) := by
        simp [abs_of_nonneg (hr₀ _)]
        exact Real.summable_pow_div_factorial (‖z‖ * a)
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((summable_mul_of_summable_norm (R := ℝ) hr hr).mul_left C)
      intro p
      unfold factorialGaugeInverseTerm
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖z ^ p.1 / p.1.factorial‖ *
            (‖(-z) ^ p.2 / p.2.factorial‖ * (C * a ^ (p.2 + p.1))) := by
          gcongr
          exact hd _
        _ = _ := by
          simp [r, pow_add, mul_pow]
          ring).of_norm
  rw [show (∑' j : ℕ, z ^ j / j.factorial * factorialGauge z d j) = ∑' p : ℕ × ℕ, T p by
    rw [hs.tsum_prod]
    apply tsum_congr
    intro j
    exact tsum_mul_left.symm, ← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq T]
  have hσ : Summable (fun p : Σ n : ℕ, antidiagonal n => T p.2) :=
    HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hs
  change (∑' p : Σ n : ℕ, antidiagonal n, T p.2) = _
  rw [hσ.tsum_sigma]
  have h_inl z d n : ∑ p ∈ antidiagonal n, factorialGaugeInverseTerm z d p = if n = 0 then d 0 else 0 := by
    rw [← Nat.sum_antidiagonal_swap (n := n) (f := factorialGaugeInverseTerm z d), Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have ht l (hl : l ∈ range (n + 1)) :
        factorialGaugeInverseTerm z d ((l, n - l).swap) =
          z ^ n * d n * ((-1) ^ l /
            (l.factorial * ((n - l).factorial))) := by
      have hln : l ≤ n := by have := mem_range.mp hl; omega
      have hpow : z ^ (n - l) * z ^ l = z ^ n := by rw [← pow_add, Nat.sub_add_cancel hln]
      unfold factorialGaugeInverseTerm
      simp [Prod.swap]
      rw [show -z = (-1) * z by ring, mul_pow,
        show l + (n - l) = n by omega]
      calc
        _ = z ^ (n - l) * z ^ l * d n * ((-1) ^ l /
            (l.factorial * ((n - l).factorial))) := by ring
        _ = _ := by rw [hpow]
    have h_inl n : ∑ l ∈ range (n + 1), (-1 : ℂ) ^ l / ((l.factorial : ℂ) * ((n - l).factorial : ℂ)) = if n = 0 then 1 else 0 := by simpa [apply_ite] using congrArg (fun q : ℚ => (q : ℂ)) (alternating_factorial_sum n)
    rw [sum_congr rfl ht, ← mul_sum, h_inl]
    by_cases hn : n = 0 <;> simp [hn]
  simp_rw [tsum_fintype, sum_coe_sort, T, h_inl]
  simp

/-- The inverse applies directly to the actual Hilbert-space driven
rows, with their proved exponential bound and sqrt(2) zeroth scale. -/
theorem physicalDrivenGauge_inverse
    γ E y θ :
    (∑' j : ℕ, physicalDrivenCentered γ θ ^ j / (j.factorial : ℂ) *
      physicalDrivenGauge γ E y j θ) = physicalDrivenRow y 0 θ := by
  simpa [factorialGauge, physicalDrivenGauge, physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow] using factorialGauge_inverse (physicalDrivenCentered γ θ) (fun n => physicalDrivenScaledRow E y n θ) (C := 2 * ‖y θ‖) (a := ‖physicalDrivenQ E‖) (norm_nonneg _) (fun n => (norm_physicalDrivenScaledRow_le E y n θ).trans_eq (by ring))

end PolyaNeumann

end
