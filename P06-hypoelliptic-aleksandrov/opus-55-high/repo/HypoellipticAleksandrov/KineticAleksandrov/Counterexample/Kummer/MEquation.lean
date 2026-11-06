module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Differential identities for the Kummer series

Coefficient recurrences and differentiation of the convergent series.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Raising the denominator parameter by one. -/
def next (b : Pos) : Pos := ⟨b.1 + 1, by grind⟩

variable (a : ℝ) (b : Pos) (n : ℕ) (z : ℝ)

/-- Left recurrence for the rising factorial. -/
theorem poch_succ_left  : poch a (n + 1) = a * poch (a + 1) n := by
  simp [poch, ascPochhammer_succ_left]

/-- Differentiation recurrence for the coefficients. -/
theorem coeff_deriv  :
    (n + 1 : ℝ) * coeff a b (n + 1) = (a / b.1) * coeff (a + 1) (next b) n := by
  simp only [coeff, poch_succ_left, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, next]
  field_simp

/-- The coefficient recurrence encoding Kummer's equation. -/
theorem coeff_recurrence  :
    (n + 1 : ℝ) * (b.1 + n) * coeff a b (n + 1) = (a + n) * coeff a b n := by
  have hb : b.1 + n ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg b.2 (Nat.cast_nonneg n))
  simp only [coeff, poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp

/-- The real formal power series has infinite convergence radius. -/
theorem radius_M  :
    (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs := (hasSum_M a b r).summable.norm
  simp_all

private theorem series_sum  :
    (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).sum = M a b := by
  funext z
  exact FormalMultilinearSeries.ofScalars_sum_eq _ z

private theorem derivative_sum  :
    (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.sum z 1 =
      ∑' n : ℕ, ((n + 1 : ℝ) * coeff a b (n + 1)) * z ^ n := by
  have hz : z ∈ Metric.eball (0)
      (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.radius := by
    have hr := (FormalMultilinearSeries.ofScalars ℝ (coeff a b))
      |>.radius_le_radius_derivSeries
    rw [radius_M] at hr
    simp_all
  have hs := ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.hasSum hz)
    |>.summable
  have hm := (ContinuousLinearMap.apply ℝ ℝ 1).map_tsum hs
  refine hm.trans ?_
  apply tsum_congr
  intro n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change z ^ n *
    ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.coeff n 1) = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars]
  ring

/-- Termwise differentiated series, with a genuine derivative. -/
theorem hasDerivAt_M  :
    HasDerivAt (M a b) ((a / b.1) * M (a + 1) (next b) z) z := by
  have hz : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).radius := by
    rw [radius_M]
    simp
  have hd := ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).hasFDerivAt_sum hz)
    |>.hasDerivAt
  rw [series_sum, derivative_sum] at hd
  simpa only [coeff_deriv, mul_assoc, tsum_mul_left, M] using hd

/-- The first derivative shifts both Kummer parameters. -/
theorem deriv_M  :
    deriv (M a b) z = (a / b.1) * M (a + 1) ⟨b.1 + 1, by grind⟩ z :=
  (hasDerivAt_M a b z).deriv

/-- The second derivative shifts both parameters twice. -/
theorem deriv2_M  :
    deriv (deriv (M a b)) z =
      (a / b.1) * ((a + 1) / (b.1 + 1)) * M (a + 2) (next (next b)) z := by
  have he : deriv _ = fun x => (a / b.1) * M _ _ x :=
    funext (fun x => (hasDerivAt_M a b x).deriv)
  rw [he, deriv_const_mul_field, deriv_M]
  change a / b.1 * ((a + 1) / (b.1 + 1) * M _ (next _) z) = _
  ring

/-- The first differentiated series. -/
theorem hasSum_deriv_M  :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * coeff a b (n + 1) * z ^ n)
      (deriv (M a b) z) := by
  rw [(hasDerivAt_M a b z).deriv]
  simpa only [coeff_deriv, mul_assoc] using (hasSum_M _ _ z)
    |>.mul_left (a / b.1)

/-- The twice differentiated series. -/
theorem hasSum_deriv2_M  :
    HasSum (fun n : ℕ =>
      (n + 1 : ℝ) * (n + 2 : ℝ) * coeff a b (n + 2) * z ^ n)
      (deriv (deriv (M a b)) z) := by
  have hc (n : ℕ) :
      (n + 1) * (n + 2) * coeff a b (n + 2) =
        (a / b.1 * ((a + 1) / (b.1 + 1))) * coeff (a + 2) (next (next b)) n := by
    have h1 := coeff_deriv a b (n + 1)
    have h2 := coeff_deriv (a + 1) (next b) n
    have he : a + 1 + 1 = a + 2 := by ring
    have hn : n + 1 + 1 = n + 2 := by omega
    simp only [Nat.cast_add, Nat.cast_one] at h1
    rw [he] at h2
    calc
      _ = (n + 1) * ((n + 1 + 1) * coeff a b _) := by ring
      _ = (n + 1) * ((a / b.1) * coeff _ _ _) := by rw [h1]
      _ = (a / b.1) * ((n + 1) * coeff _ _ _) := by ring
      _ = _ := by rw [h2, mul_assoc]; rfl

  rw [deriv2_M]
  simpa only [hc, mul_assoc] using (hasSum_M _ _ z)
    |>.mul_left (a / b.1 * ((a + 1) / (b.1 + 1)))

private theorem hasSum_z_deriv  :
    HasSum (fun n : ℕ => (n : ℝ) * coeff a b n * z ^ n)
      (z * deriv (M a b) z) := by
  have hs := (hasSum_deriv_M a b z).mul_left z
  have he (n : ℕ) : z * ((n + 1) * coeff a b (n + 1) * z ^ n) =
      ((n + 1 : ℕ)) * coeff a b (n + 1) * z ^ (n + 1) := by
    grind
  simp only [he] at hs
  simpa using
    hs.zero_add (f := fun n : ℕ => n * coeff a b n * z ^ n)

private theorem hasSum_z_deriv2  :
    HasSum (fun n : ℕ => (n : ℝ) * (n + 1 : ℝ) * coeff a b (n + 1) * z ^ n)
      (z * deriv (deriv (M a b)) z) := by
  have hs := (hasSum_deriv2_M a b z).mul_left z
  have he (n : ℕ) : z * ((n + 1) * (n + 2) * coeff a b (n + 2) * z ^ n) =
      ((n + 1 : ℕ)) * ((n + 1 : ℕ) + 1) *
        coeff a b ((n + 1) + 1) * z ^ (n + 1) := by
    grind
  simp only [he] at hs
  simpa using
    hs.zero_add (f := fun n : ℕ =>
      n * (n + 1) * coeff a b _ * z ^ n)

/-- The literal entire power series solves Kummer's differential equation. -/
theorem M_ode  :
    z * deriv (deriv (M a b)) z + (b.1 - z) * deriv (M a b) z - a * M a b z = 0 := by
  have hl := (hasSum_z_deriv2 a b z).add ((hasSum_deriv_M a b z).mul_left b.1)
  have hr := (hasSum_z_deriv a b z).add ((hasSum_M a b z).mul_left a)
  have he (n : ℕ) :
      n * (n + 1) * coeff a b (n + 1) * z ^ n +
        b.1 * ((n + 1) * coeff a b (n + 1) * z ^ n) =
      n * coeff a b n * z ^ n + a * (coeff a b n * z ^ n) := by
    calc
      _ = ((n + 1) * (b.1 + n) * coeff a b _) * z ^ n := by ring
      _ = _ := by rw [coeff_recurrence]; ring
  simp only [he] at hl
  have h := hl.unique hr
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
