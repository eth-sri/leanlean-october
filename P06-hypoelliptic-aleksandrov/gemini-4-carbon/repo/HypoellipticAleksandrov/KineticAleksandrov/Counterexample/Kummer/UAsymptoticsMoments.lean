module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral
public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
open Set Filter MeasureTheory
open scoped Topology

/-- Literal Taylor polynomial of the translated power, truncated before order N. -/
def powerTaylor (q : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Ring.choose q n * t ^ n

/-- The analytic partial sum is precisely the scalar binomial polynomial. -/
theorem powerTaylor_eq_partialSum (q : ℝ) (N : ℕ) (t : ℝ) :
    powerTaylor q N t = (binomialSeries ℝ q).partialSum N t := by
  simp [powerTaylor, binomialSeries, FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm]



/-- Every finite truncation has a global, polynomially dominated remainder. -/
theorem exists_powerTaylor_remainder_bound (q : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∃ L : ℕ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖(1 + t) ^ q - powerTaylor q N t‖ ≤ C * t ^ N * (1 + t) ^ L   := by
  have powerTaylor_remainder_growth (L : ℕ) (hq : q ≤ (L : ℝ)) (hN : N ≤ L) (t : ℝ) (ht : 0 ≤ t) :
      ‖(1 + t) ^ q - powerTaylor q N t‖ ≤
      (1 + ∑ n ∈ Finset.range N, ‖Ring.choose q n‖) * (1 + t) ^ L := by
    have hbase : 1 ≤ 1 + t := by linarith only [ht]
    have hf : ‖(1 + t) ^ q‖ ≤ (1 + t) ^ L := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith only [ht]) _)]
      simpa using Real.rpow_le_rpow_of_exponent_le hbase hq
    have hp : ‖powerTaylor q N t‖ ≤
        (∑ n ∈ Finset.range N, ‖Ring.choose q n‖) * (1 + t) ^ L := by
      apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht n)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        t ^ n ≤ (1 + t) ^ n := pow_le_pow_left₀ ht (by linarith) n
        _ ≤ (1 + t) ^ L := pow_le_pow_right₀ hbase ((Finset.mem_range.mp hn).le.trans hN)
    calc
      ‖(1 + t) ^ q - powerTaylor q N t‖ ≤ ‖(1 + t) ^ q‖ + ‖powerTaylor q N t‖ :=
        norm_sub_le _ _
      _ ≤ (1 + t) ^ L + (∑ n ∈ Finset.range N, ‖Ring.choose q n‖) * (1 + t) ^ L :=
        add_le_add hf hp
      _ = _ := by ring
  have powerTaylor_remainder_local :
      Asymptotics.IsBigO (𝓝 0)
      (fun t => (1 + t) ^ q - powerTaylor q N t) (fun t => ‖t‖ ^ N) := by
    have h := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := q))
      |>.isBigO_sub_partialSum_pow N
    simpa [← powerTaylor_eq_partialSum] using h
  obtain ⟨n, hn⟩ := exists_nat_gt q
  let L := max n N
  have hq : q ≤ (L : ℝ) := hn.le.trans (by exact_mod_cast le_max_left n N)
  obtain ⟨C₀, hC₀, hlocal⟩ := Asymptotics.isBigO_iff'.mp (powerTaylor_remainder_local)
  obtain ⟨δ, hδ, hδlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let D : ℝ := 1 + ∑ n ∈ Finset.range N, ‖Ring.choose q n‖
  let C : ℝ := max C₀ (D / δ ^ N)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, L, hC, ?_⟩
  intro t ht
  have hbase : 1 ≤ (1 + t) ^ L := one_le_pow₀ (by linarith only [ht])
  by_cases htδ : t < δ
  · have hdist : dist t 0 < δ := by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht]
      exact htδ
    have h := hδlocal hdist
    simp [abs_of_nonneg ht, abs_of_nonneg (pow_nonneg ht N)] at h
    exact h.trans ((mul_le_mul_of_nonneg_right (le_max_left C₀ _) (pow_nonneg ht N)).trans
      (le_mul_of_one_le_right (by positivity) hbase))
  · have hδt : δ ≤ t := le_of_not_gt htδ
    have hDC : D ≤ C * t ^ N := by
      have hDδ : D ≤ C * δ ^ N := (div_le_iff₀ (pow_pos hδ N)).mp (le_max_right _ _)
      exact hDδ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδt N) hC.le)
    exact (powerTaylor_remainder_growth L hq (le_max_right n N) t ht).trans
      (mul_le_mul_of_nonneg_right hDC (pow_nonneg (by linarith only [ht]) L))


/-- Finite positive-axis U expansion in inverse powers of the argument. -/
def uExpansion (a b : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  z ^ (-a) * ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n /
      (n.factorial : ℝ) * z⁻¹ ^ n

/-- Binomial coefficients written with the signed rising factorial. -/
theorem choose_eq_signed_poch (q : ℝ) (n : ℕ) :
    Ring.choose q n = (-1 : ℝ) ^ n * poch (-q) n / (n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer, poch,
    ascPochhammer_eval_neg_eq_descPochhammer, smul_eq_mul]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hs]
  ring

/-- Gamma recurrence at every nonnegative integer shift of a positive shape. -/
theorem Gamma_add_nat_eq_poch (a : Pos) (n : ℕ) :
    Real.Gamma (a.1 + n) = Real.Gamma a.1 * poch a.1 n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc,
        Real.Gamma_add_one (ne_of_gt (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n))),
        ih, poch_succ]
      ring

/-- Evaluation of a scaled real Gamma kernel. -/
theorem integral_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a - 1)) =
      z ^ (-a) * Real.Gamma a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hz
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [mul_comm] using h


/-- Integrability of each Taylor moment before finite summation. -/
theorem integrableOn_gammaKernel_moment (a : Pos) (z : ℝ) (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n)
      (Ioi 0) volume := by
  apply IntegrableOn.congr_fun
    (integrableOn_gammaKernel (a.1 + n) z
      (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n)) hz) _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show a.1 + (n : ℝ) - 1 = (a.1 - 1) + (n : ℝ) by ring,
    Real.rpow_add ht, Real.rpow_natCast]
  ring

/-- Integrability of the complete finite Taylor polynomial against the Gamma kernel. -/
theorem integrableOn_gammaKernel_powerTaylor (a : Pos) (q z : ℝ) (hz : 0 < z) (N : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a.1 - 1) * powerTaylor q N t)
      (Ioi 0) volume := by
  apply IntegrableOn.congr_fun (integrable_finsetSum (Finset.range N) (fun n _ => (integrableOn_gammaKernel_moment a z hz n).const_mul (Ring.choose q n))) _ measurableSet_Ioi
  intro t _
  simp only [powerTaylor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The integral of the finite binomial polynomial equals the normalized expansion. -/
theorem integral_powerTaylor (a : Pos) (b z : ℝ) (hz : 0 < z) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) *
      powerTaylor (b - a.1 - 1) N t) = Real.Gamma a.1 * uExpansion a.1 b N z  := by
  have integral_gammaKernel_moment (n : ℕ) :
      (∫ t in Ioi 0, Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n) =
      Real.Gamma a.1 * poch a.1 n * z ^ (-a.1) * z⁻¹ ^ n := by
    have heq : (∫ t in Ioi 0, Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n) =
        ∫ t in Ioi 0, Real.exp (-(z * t)) * t ^ (a.1 + (n : ℝ) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [show a.1 + (n : ℝ) - 1 = (a.1 - 1) + (n : ℝ) by ring,
        Real.rpow_add ht, Real.rpow_natCast]
      ring
    rw [heq, integral_gammaKernel _ z
      (add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg n)) hz, Gamma_add_nat_eq_poch]
    rw [neg_add, Real.rpow_add hz]
    simp
    ring
  have hsum : (∫ t in Ioi 0, Real.exp (-(z * t)) * t ^ (a.1 - 1) *
      powerTaylor (b - a.1 - 1) N t) =
      ∑ n ∈ Finset.range N, Ring.choose (b - a.1 - 1) n *
        (∫ t in Ioi 0, Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n) := by
    simp only [powerTaylor, Finset.mul_sum]
    have heq : (fun t => ∑ n ∈ Finset.range N,
        Real.exp (-(z * t)) * t ^ (a.1 - 1) * (Ring.choose (b - a.1 - 1) n * t ^ n)) =
        (fun t => ∑ n ∈ Finset.range N, Ring.choose (b - a.1 - 1) n *
          (Real.exp (-(z * t)) * t ^ (a.1 - 1) * t ^ n)) := by
      funext t
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [heq, integral_finsetSum]
    · simp only [integral_const_mul]
    · intro n _
      exact (integrableOn_gammaKernel_moment a z hz n).const_mul _
  rw [hsum]
  simp only [uExpansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_gammaKernel_moment n, choose_eq_signed_poch,
    show -(b - a.1 - 1) = a.1 - b + 1 by ring]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

