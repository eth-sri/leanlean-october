module

public import NearlyMinimax.ExponentialSpatialKernels
public import NearlyMinimax.GammaTailBounds


@[expose] public section

/-! Genuine scalar pair Laplace kernels and fine-tail spatial integrability. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The true scalar pair kernel from the source integral. -/
def pairLaplaceKernel (N r : ℝ) : ℝ := ∫ T in (0 : ℝ)..N, T * Real.exp (-(T*r))

/-- The true fine alias Laplace kernel. -/
def fineAliasLaplaceKernel (T0 N r : ℝ) : ℝ := ∫ T in T0..N, T * Real.exp (-(T*r))

theorem exactEuclideanDistance_eq_euclideanNorm {d : ℕ} (x y : Covariate d) :
    exactEuclideanDistance x y = euclideanNorm (fun i => x i - y i) := by
  unfold exactEuclideanDistance spatialSquaredDistance euclideanNorm
  grind

section
variable {r : ℝ} (hr : 0 < r)
include hr

section
variable (A : ℝ)

/-- The actual complete positive-tail Laplace integral. -/
theorem laplace_linear_tail_integral :
    (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) =
      (1 + A*r) * Real.exp (-(A*r)) / r^2 := by
  simpa [mul_comm] using (gamma_linear_tail hr A).2

theorem laplace_linear_tail_integrable :
    IntegrableOn (fun T : ℝ => T * Real.exp (-(T*r))) (Ici A) := by
  simpa [mul_comm] using (gamma_linear_tail hr A).1

end

/-- Actual finite Laplace integration, derived by subtracting two genuine complete tails. -/
theorem pairLaplaceKernel_formula (N : ℝ) :
    pairLaplaceKernel N r = (1 - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
  unfold pairLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr 0) (laplace_linear_tail_integrable hr N),
    laplace_linear_tail_integral hr 0, laplace_linear_tail_integral hr N]
  simp only [zero_mul, add_zero, neg_zero, Real.exp_zero, mul_one]
  ring

end

/-- The exact count-two cancellation identity, including zero distance. -/
theorem pairLaplaceKernel_defect (N r : ℝ) (hr : 0 ≤ r) :
    1 - r^2 * pairLaplaceKernel N r = (1+N*r) * Real.exp (-(N*r)) := by
  by_cases hr0 : r = 0
  · simp_all
  · rw [pairLaplaceKernel_formula (lt_of_le_of_ne hr (Ne.symm hr0))]
    field_simp
    ring

/-- The actual finite fine tail equals a difference of its genuine endpoint tails. -/
theorem fineAliasLaplaceKernel_formula {r : ℝ} (hr : 0 < r) (T0 N : ℝ) :
    fineAliasLaplaceKernel T0 N r =
      ((1+T0*r)*Real.exp (-(T0*r)) - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
  unfold fineAliasLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr T0) (laplace_linear_tail_integrable hr N),
    laplace_linear_tail_integral hr T0, laplace_linear_tail_integral hr N]
  ring

/-- Fine Laplace integration is nonnegative and bounded by its complete tail. -/
theorem fineAliasLaplaceKernel_nonneg_le {r T0 N : ℝ} (hr : 0 < r) (hT0 : 0 ≤ T0) (hN : T0 ≤ N) :
    0 ≤ fineAliasLaplaceKernel T0 N r ∧
      fineAliasLaplaceKernel T0 N r ≤ (1+T0*r)*Real.exp (-(T0*r))/r^2 := by
  constructor
  · unfold fineAliasLaplaceKernel
    apply intervalIntegral.integral_nonneg hN
    intro T hT
    exact mul_nonneg (hT0.trans hT.1) (Real.exp_pos _).le
  · rw [fineAliasLaplaceKernel_formula hr]
    have hpos : 0 ≤ (1+N*r)*Real.exp (-(N*r)) := by
      have hn0 := hT0.trans hN
      positivity
    have hd : 0 ≤ r^2 := sq_nonneg _
    exact div_le_div_of_nonneg_right (sub_le_self _ hpos) hd

theorem fineAliasLaplaceKernel_measurable (T0 N : ℝ) (hN : T0 ≤ N) :
    Measurable (fineAliasLaplaceKernel T0 N) := by
  unfold fineAliasLaplaceKernel
  simp_rw [intervalIntegral.integral_of_le hN]
  have hm : Measurable (fun rt : ℝ × ℝ => rt.2 * Real.exp (-(rt.2*rt.1))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Complete-space normalization for the fine alias tail. -/
def spatialInverseFourConstant (d : ℕ) : ℝ := radialExponentialConstant d 4

section
variable {d : ℕ} (hd : 4 < d)
include hd

section
variable {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N)
include hT0 hN

/-- The actual finite fine alias kernel has the source complete-space squared L² bound. -/
theorem euclidean_fineAlias_squared_integrable_and_integral_le :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) volume ∧
      (∫ z : EuclideanSpace ℝ (Fin d), (fineAliasLaplaceKernel T0 N ‖z‖)^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have henv := euclidean_radial_exponential hd hT0
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) :=
    ((fineAliasLaplaceKernel_measurable T0 N hN).comp continuous_norm.measurable).pow_const 2
  have hb : ∀ᵐ z : EuclideanSpace ℝ (Fin d) ∂volume,
      (fineAliasLaplaceKernel T0 N ‖z‖)^2 ≤ 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) := by
    filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin d))] with z hz
    have hr := norm_pos_iff.mpr hz
    have hw := fineAliasLaplaceKernel_nonneg_le hr hT0.le hN
    have hp := pair_defect_exponential_absorption (T0*‖z‖) (mul_nonneg hT0.le hr.le)
    calc
      _ ≤ ((1+T0*‖z‖)*Real.exp (-(T0*‖z‖))/‖z‖^2)^2 := pow_le_pow_left₀ hw.1 hw.2 2
      _ = (1+T0*‖z‖)^2 * Real.exp (-(2*T0*‖z‖)) / ‖z‖^4 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul,
          show (‖z‖^2)^2 = ‖z‖^4 by ring,
          show ((2 : ℕ) : ℝ) * -(T0*‖z‖) = -(2*T0*‖z‖) by ring]
      _ ≤ 6 * Real.exp (-(T0*‖z‖)) / ‖z‖^4 :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hp) (by positivity)
      _ = _ := by ring
  have hi :=
    (henv.1.const_mul 6).mono' hm.aestronglyMeasurable (hb.mono fun z hz => by
      simp_all)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin d), 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) :=
      integral_mono_ae hi (henv.1.const_mul 6) hb
    _ = _ := by rw [integral_const_mul, henv.2, spatialInverseFourConstant]; ring

/-- The same genuine fine-alias squared bound in actual source coordinates and at every center. -/
theorem fineAlias_spatial_squared_integrable_and_integral_le (x : Covariate d) :
    Integrable (fun y => (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) volume ∧
      (∫ y, (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  have he := euclidean_fineAlias_squared_integrable_and_integral_le hd hT0 hN
  have h := radial_spatial_transport x (fun r => (fineAliasLaplaceKernel T0 N r)^2) he.1
  exact ⟨h.1, h.2.trans_le he.2⟩

end

end

end NearlyMinimax
