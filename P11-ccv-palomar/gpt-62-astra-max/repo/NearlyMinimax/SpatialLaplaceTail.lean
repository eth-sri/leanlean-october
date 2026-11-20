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

section
variable {r : ℝ} (hr : 0 < r) (T0 N A : ℝ)

/-- The true scalar pair kernel from the source integral. -/
def pairLaplaceKernel (r : ℝ) : ℝ := ∫ T in 0..N, T * Real.exp (-(T*r))

/-- The true fine alias Laplace kernel. -/
def fineAliasLaplaceKernel (r : ℝ) : ℝ := ∫ T in T0..N, T * Real.exp (-(T*r))

theorem exactEuclideanDistance_eq_euclideanNorm {d : ℕ} (x y : Covariate d) :
    exactEuclideanDistance x y = euclideanNorm (fun i => x i - y i) := by
  grind [exactEuclideanDistance, spatialSquaredDistance, euclideanNorm]

include hr in
/-- The actual complete positive-tail Laplace integral. -/
theorem laplace_linear_tail_integral :
    (∫ T in Ici A, T * Real.exp (-(T*r))) =
      (1 + A*r) * Real.exp (-(A*r)) / r^2 := by
  have he : (∫ T in Ici A, T * Real.exp (-(T*r))) =
      Real.exp (-(r*A)) * (1/r^2 + A/r) := by
    simpa [Finset.sum_range_succ, mul_comm] using gamma_polynomial_tail_integral hr A 1
  rw [he]
  field_simp

include hr in
theorem laplace_linear_tail_integrable :
    IntegrableOn (fun T => T * Real.exp (-(T*r))) (Ici A) := by
  simpa [mul_comm] using gamma_polynomial_tail_integrable hr A 1

include hr in
/-- Actual finite Laplace integration, derived by subtracting two genuine complete tails. -/
theorem pairLaplaceKernel_formula :
    pairLaplaceKernel N r = (1 - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
  unfold pairLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr 0) (laplace_linear_tail_integrable hr N),
    laplace_linear_tail_integral hr 0, laplace_linear_tail_integral hr N]
  simp
  ring

/-- The exact count-two cancellation identity, including zero distance. -/
theorem pairLaplaceKernel_defect (r : ℝ) (hr : 0 ≤ r) :
    1 - r^2 * pairLaplaceKernel N r = (1+N*r) * Real.exp (-(N*r)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · rw [pairLaplaceKernel_formula (by positivity)]
    field_simp
    ring

include hr in
/-- The actual finite fine tail equals a difference of its genuine endpoint tails. -/
theorem fineAliasLaplaceKernel_formula :
    fineAliasLaplaceKernel T0 N r =
      ((1+T0*r)*Real.exp (-(T0*r)) - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
  unfold fineAliasLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr T0) (laplace_linear_tail_integrable hr N),
    laplace_linear_tail_integral hr T0, laplace_linear_tail_integral hr N]
  ring

end

/-- Fine Laplace integration is nonnegative and bounded by its complete tail. -/
theorem fineAliasLaplaceKernel_nonneg_le {r T0 N : ℝ} (hr : 0 < r) (hT0 : 0 ≤ T0) (hN : T0 ≤ N) :
    0 ≤ fineAliasLaplaceKernel T0 N r ∧
      fineAliasLaplaceKernel T0 N r ≤ (1+T0*r)*Real.exp (-(T0*r))/r^2 := by
  constructor
  · apply intervalIntegral.integral_nonneg hN
    intro T hT
    exact mul_nonneg (hT0.trans hT.1) (Real.exp_pos _).le
  · rw [fineAliasLaplaceKernel_formula hr]
    have hpos : 0 ≤ (1+N*r)*Real.exp (-(N*r)) := by
      bound
    bound

variable {d : ℕ} (hd : 4 < d) {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) {T : ℝ} (hT : 0 < T)

include hN in
theorem fineAliasLaplaceKernel_measurable :
    Measurable (fineAliasLaplaceKernel T0 N) := by
  unfold fineAliasLaplaceKernel
  simp_rw [intervalIntegral.integral_of_le hN]
  have hm : Measurable (fun rt : ℝ × ℝ => rt.2 * Real.exp (-(rt.2*rt.1))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A true complete-space radial constant for the fine alias tail. -/
def spatialInverseFourConstant (d : ℕ) : ℝ :=
  d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * (d-5).factorial

include hd in
private theorem radial_inverse_four_monomial {r : ℝ} (hr : r ≠ 0) (T : ℝ) :
    let expScale := Real.exp (-(T*r))
    r^(d-1) * (expScale/r^4) = r^(d-5) * expScale := by
  intro expScale
  calc
    _ = (r^(d-1)/r^4) * expScale := by ring
    _ = _ := by
      rw [show d-1 = d-5+4 by omega, pow_add]
      field_simp

include hd hT in
/-- The singular envelope is actually integrable exactly in the source dimension regime. -/
theorem euclidean_inverse_four_exponential_integrable :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(T*‖z‖))/‖z‖^4) volume := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  apply (integrable_fun_norm_addHaar volume (f := fun r => Real.exp (-(T*r))/r^4)).2
  apply ((gamma_monomial_integrable hT (d-5)).mono_set Ioi_subset_Ici_self).congr_fun _ measurableSet_Ioi
  intro r hr
  simp
  exact (radial_inverse_four_monomial hd hr.ne' T).symm

include hd hT in
/-- Exact genuine fine-envelope scaling from the radial Gamma integral. -/
theorem euclidean_inverse_four_exponential_integral :
    (∫ z : EuclideanSpace ℝ (Fin d), Real.exp (-(T*‖z‖))/‖z‖^4) =
      spatialInverseFourConstant d / T^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  rw [integral_fun_norm_addHaar volume (fun r => Real.exp (-(T*r))/r^4)]
  simp
  rw [(setIntegral_congr_fun measurableSet_Ioi (fun r hr => radial_inverse_four_monomial hd hr.ne' T)), ← integral_Ici_eq_integral_Ioi, gamma_monomial_integral hT, show d-5+1 = d-4 by omega]
  unfold spatialInverseFourConstant
  ring

include hd hT0 hN in
/-- The actual finite fine alias kernel has the source complete-space squared L² bound. -/
theorem euclidean_fineAlias_squared_integrable_and_integral_le :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) volume ∧
      (∫ z : EuclideanSpace ℝ (Fin d), (fineAliasLaplaceKernel T0 N ‖z‖)^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have henv := euclidean_inverse_four_exponential_integrable hd hT0
  have hb : ∀ᵐ z : EuclideanSpace ℝ (Fin d) ∂volume,
      (fineAliasLaplaceKernel T0 N ‖z‖)^2 ≤ 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) := by
    filter_upwards [volume.ae_ne 0] with z hz
    have hr  := norm_pos_iff.mpr hz
    have hw := fineAliasLaplaceKernel_nonneg_le hr hT0.le hN
    have hp := pair_defect_exponential_absorption (mul_nonneg hT0.le hr.le)
    calc
      _ ≤ ((1+T0*‖z‖)*Real.exp (-(T0*‖z‖))/‖z‖^2)^2 := by bound
      _ = _ := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul,
          show (‖z‖^2)^2 = ‖z‖^4 by ring,
          show (2 : ℕ) * -(T0*‖z‖) = -(2*T0*‖z‖) by ring]
      _ ≤ _ :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hp) (by positivity)
      _ = _ := by ring
  have hi  :=
    (henv.const_mul 6).mono' (((fineAliasLaplaceKernel_measurable hN).comp continuous_norm.measurable).pow_const 2).aestronglyMeasurable (hb.mono fun z hz => by
      simpa)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ _ :=
      integral_mono_ae hi (henv.const_mul 6) hb
    _ = _ := by rw [integral_const_mul, euclidean_inverse_four_exponential_integral hd hT0]; ring

include hd hT0 hN in
/-- The same genuine fine-alias squared bound in actual source coordinates and at every center. -/
theorem fineAlias_spatial_squared_integrable_and_integral_le (x : Covariate d) :
    Integrable (fun y => (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) volume ∧
      (∫ y, (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  have he := euclidean_fineAlias_squared_integrable_and_integral_le hd hT0 hN
  have hi := he.1
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hi
  have hi0 : Integrable (fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2) volume := by
    assumption
  refine ⟨by simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x, ?_⟩
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self (fun z => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2)]
  exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun z => (fineAliasLaplaceKernel T0 N ‖z‖)^2)).trans_le he.2

end NearlyMinimax
