/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianTiltSigned
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import DOZZ.GMC.FiniteGaussianExponentialIntegrability

/-! Gaussian integration by parts for smooth tests with exponential-linear growth. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- A finite Gaussian integration-by-parts formula for a measurable test and its gradient with
exponential-linear growth. The envelope is integrable for every centered jointly Gaussian vector,
including singular ones. -/
theorem finite_gaussian_integration_by_parts_of_absExp_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (i : ι)
    (G : (ι → ℝ) → ℝ) (D : (ι → ℝ) → ι → ℝ)
    (hGmeas : Measurable G) (hDmeas : ∀ j, Measurable (fun z => D z j))
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (M : ℝ) (hM : 0 ≤ M)
    (hGbound : ∀ z, ‖G z‖ ≤ M * Real.exp (∑ j, c j * |z j|))
    (hDbound : ∀ z j, ‖D z j‖ ≤ M * Real.exp (∑ j, c j * |z j|))
    (hGdir : ∀ (x d : ι → ℝ) t,
      HasDerivAt (fun s => G (fun j => x j + s * d j))
        (∑ j, d j * D (fun j => x j + t * d j) j) t) :
    ∫ ω, Z ω i * G (Z ω) ∂P =
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        ∫ ω, D (Z ω) j ∂P := by
  classical
  let q := fun j => gaussianCovariance P (Z · j) (Z · i)
  have hq (j : ι) : gaussianCovariance P (Z · i) (Z · j) = q j := by
    simp only [q, gaussianCovariance, mul_comm]
  have hq0 : 0 ≤ q i := integral_nonneg fun _ => mul_self_nonneg _
  let U := fun (t : ℝ) ω j => Z ω j + t * q j
  let R := fun t ω => G (U t ω)
  let R' := fun t ω => ∑ j, q j * D (U t ω) j
  let L := fun (t : ℝ) ω => Real.exp (t * Z ω i - t ^ 2 / 2 * q i) * G (Z ω)
  let L' := fun (t : ℝ) ω => (Z ω i - t * q i) * L t ω
  let E := fun ω => Real.exp (∑ j, c j * |Z ω j|)
  let A := ∑ j, c j * |q j|
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (abs_nonneg _)
  have hE : Integrable E P := centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ c
  have hU (t : ℝ) : AEMeasurable (U t) P :=
    aemeasurable_pi_iff.mpr fun j => (hZ.2.1 j).add aemeasurable_const
  have hZm : AEMeasurable Z P := aemeasurable_pi_iff.mpr hZ.2.1
  have hGm := hGmeas.comp_aemeasurable hZm
  have hshift (ω : Ω) (t : ℝ) : Real.exp (∑ j, c j * |U t ω j|) ≤ Real.exp (|t| * A) * E ω := by
    change Real.exp (∑ j, c j * |U t ω j|) ≤ Real.exp (|t| * A) * Real.exp (∑ j, c j * |Z ω j|)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ j, c j * (|t| * |q j| + |Z ω j|) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hc j)
        simpa [U, abs_mul, add_comm] using abs_add_le (Z ω j) (t * q j)
      _ = _ := by simp only [mul_add, Finset.sum_add_distrib, A, Finset.mul_sum];
                  congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
  have hRI (t : ℝ) : Integrable (R t) P := by
    refine (hE.const_mul (M * Real.exp (|t| * A))).mono'
      (hGmeas.comp_aemeasurable (hU t)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simpa [mul_assoc] using (hGbound _).trans (mul_le_mul_of_nonneg_left (hshift ω t) hM)
  have hDI (j : ι) : Integrable (fun ω => D (Z ω) j) P :=
    (hE.const_mul M).mono' ((hDmeas j).comp_aemeasurable hZm).aestronglyMeasurable
      (ae_of_all _ fun ω => hDbound (Z ω) j)
  have hLmeas (t : ℝ) : AEStronglyMeasurable (L t) P := by
    have hz := hZ.2.1 i
    exact ((Real.measurable_exp.comp_aemeasurable ((hz.const_mul t).sub aemeasurable_const)).mul hGm).aestronglyMeasurable
  have hLm : AEStronglyMeasurable (L' 0) P := by
    fun_prop
  have hLI : Integrable (L 0) P := by simpa [L, R, U] using hRI 0
  let c' := fun j => c j + if j = i then 1 else 0
  let E' := fun ω => Real.exp (∑ j, c' j * |Z ω j|)
  have hE' (ω : Ω) : E' ω = Real.exp |Z ω i| * E ω := by
    simp only [E', c', add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Real.exp_add, E]
    exact mul_comm _ _
  let bL := fun ω => M * ((|Z ω i| + q i) * E' ω)
  have hbL : Integrable bL P := by
    have h := (centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable P Z hZ c' i).norm
    have h' : Integrable (fun ω => |Z ω i| * E' ω) P := by
      simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), E'] using h
    have he : Integrable E' P := centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ c'
    simpa only [bL, add_mul, Pi.add_apply] using (h'.add (he.const_mul (q i))).const_mul M
  have hunit {t : ℝ} (ht : t ∈ Metric.ball (0 : ℝ) 1) : |t| ≤ 1 := by
    exact (by simpa [Metric.mem_ball, Real.dist_eq] using ht : |t| < 1).le
  have hLb : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖L' t ω‖ ≤ bL ω := by
    filter_upwards [] with ω t ht
    have ht' := hunit ht
    have halpha : t * Z ω i - t ^ 2 / 2 * q i ≤ |Z ω i| := by
      refine (sub_le_self _ (by positivity)).trans ?_
      calc
        _ ≤ |t * Z ω i| := le_abs_self _
        _ = |t| * |Z ω i| := abs_mul _ _
        _ ≤ _ := mul_le_of_le_one_left (abs_nonneg _) ht' 
    have hlin : |Z ω i - t * q i| ≤ |Z ω i| + q i := by
      refine (abs_sub _ _).trans (add_le_add_right ?_ _)
      rw [abs_mul, abs_of_nonneg hq0]
      exact mul_le_of_le_one_left hq0 ht'
    simp only [L', L, norm_mul, Real.norm_eq_abs (Z ω i - t * q i), Real.norm_eq_abs (Real.exp _),
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (|Z ω i| + q i) * (Real.exp |Z ω i| * (M * E ω)) := by
        exact mul_le_mul hlin (mul_le_mul (Real.exp_le_exp.mpr halpha) (hGbound _) (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
      _ = bL ω := by dsimp only [bL]; rw [hE']; ring
  have hLd : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (L · ω) (L' t ω) t := by
    filter_upwards [] with ω t ht
    have h : HasDerivAt (fun s : ℝ => s * Z ω i - s ^ 2 / 2 * q i) (Z ω i - t * q i) t := by
      convert ((hasDerivAt_id t).mul_const (Z ω i)).sub
        (((hasDerivAt_id t).pow 2).mul_const (q i / 2)) using 1
      · funext s
        change s * Z ω i - s ^ 2 / 2 * q i = s * Z ω i - s ^ 2 * (q i / 2)
        ring
      · simp only [id_eq, one_mul]; ring
    convert h.exp.mul_const (G (Z ω)) using 1 <;> simp only [L, L'] <;> ring
  let bR := fun ω => ((∑ j, |q j|) * M * Real.exp A) * E ω
  have hRb : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖R' t ω‖ ≤ bR ω := by
    filter_upwards [] with ω t ht
    have hAt : Real.exp (|t| * A) ≤ Real.exp A := Real.exp_le_exp.mpr (mul_le_of_le_one_left hA (hunit ht))
    calc
      _ ≤ ∑ j, ‖q j * D (U t ω) j‖ := norm_sum_le _ _
      _ ≤ ∑ j, |q j| * (M * (Real.exp A * E ω)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Real.norm_eq_abs (q j)]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (hDbound (U t ω) j).trans (mul_le_mul_of_nonneg_left
          ((hshift ω t).trans (mul_le_mul_of_nonneg_right hAt (Real.exp_nonneg _))) hM)
      _ = bR ω := by rw [← Finset.sum_mul]; dsimp [bR]; ring
  have hRm : AEStronglyMeasurable (R' 0) P := by
    apply Finset.univ.aestronglyMeasurable_fun_sum
    intro j _
    exact ((hDmeas j).comp_aemeasurable (hU 0)).aestronglyMeasurable.const_mul _
  have hball := Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)
  have hL := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball
    (Filter.Eventually.of_forall hLmeas) hLI hLm hLb hbL hLd).2
  have hR := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball
    (Filter.Eventually.of_forall fun t => (hRI t).aestronglyMeasurable) (hRI 0) hRm hRb (hE.const_mul _)
    (ae_of_all _ fun ω t _ => hGdir (Z ω) q t)).2
  have htilt : (fun t => ∫ ω, L t ω ∂P) = fun t => ∫ ω, R t ω ∂P := by
    funext t
    let a := fun j => if j = i then t else 0
    have hsum (ω : Ω) : (∑ j, a j * Z ω j) = t * Z ω i := by simp [a]
    have hvar : (∑ k, ∑ j, a k * gaussianCovariance P (Z · k) (Z · j) * a j) = t ^ 2 * q i := by
      simp [a, q]; ring
    have hs (j : ι) : (∑ k, gaussianCovariance P (Z · j) (Z · k) * a k) = t * q j := by
      simp [a, q, mul_comm]
    have hint := finite_gaussian_tilt_signed P Z hZ a G hGmeas (by simpa only [hs, R, U] using hRI t)
    simpa only [hsum, hvar, hs, L, R, U, div_mul_eq_mul_div] using hint
  have h := HasDerivAt.unique (htilt ▸ hL) hR
  simp only [L', L, R', U, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Real.exp_zero, one_mul, add_zero, integral_finsetSum _ (fun j _ => (hDI j).const_mul _), integral_const_mul] at h
  simpa only [hq] using h

end DOZZ.Proofs
