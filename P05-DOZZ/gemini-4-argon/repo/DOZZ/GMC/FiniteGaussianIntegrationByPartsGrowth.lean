/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianIntegrationByParts
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
    (P : Measure Ω) Z
    (hZ : IsCenteredJointlyGaussian P Z) i
    G (D : (ι → ℝ) → ι → ℝ)
    (hGmeas : Measurable G) (hDmeas : ∀ j, Measurable (fun z => D z j))
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) M (hM : 0 ≤ M)
    (hGbound : ∀ z, ‖G z‖ ≤ M * Real.exp (∑ j, c j * |z j|))
    (hDbound : ∀ z j, ‖D z j‖ ≤ M * Real.exp (∑ j, c j * |z j|))
    (hGdir : ∀ (x d : ι → ℝ) t,
      HasDerivAt (fun s => G (fun j => x j + s * d j))
        (∑ j, d j * D (fun j => x j + t * d j) j) t) :
    ∫ ω, Z ω i * G (Z ω) ∂P =
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        ∫ ω, D (Z ω) j ∂P := by
  classical
  let var : ℝ := gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω i)
  let shift : ι → ℝ := fun j =>
    gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i)
  let baseExp : Ω → ℝ := fun ω => Real.exp (∑ j, c j * |Z ω j|)
  let c' : ι → ℝ := fun j => c j + if j = i then 1 else 0
  let enlargedExp : Ω → ℝ := fun ω => Real.exp (∑ j, c' j * |Z ω j|)
  have hbaseExp : Integrable baseExp P := by
    simpa [baseExp] using centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ c
  have : Integrable (fun ω => Z ω i * baseExp ω) P := by
    simpa [baseExp] using
      centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable P Z hZ c i
  have hcov_symm j :
      gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) = shift j := by
    simp [shift, gaussianCovariance, mul_comm]
  have hshiftBound : ∀ ω t,
      ∑ j, c j * |Z ω j + t * shift j| ≤
        ∑ j, c j * |Z ω j| + |t| * ∑ j, c j * |shift j| := by
    intro ω t
    calc
      _ ≤ ∑ j, c j * (|Z ω j| + |t| * |shift j|) := by
        apply Finset.sum_le_sum
        intro j hj
        have habs : |Z ω j + t * shift j| ≤ |Z ω j| + |t| * |shift j| := by
          calc
            _ ≤ |Z ω j| + |t * shift j| := abs_add_le _ _
            _ = |Z ω j| + |t| * |shift j| := by rw [abs_mul]
        exact mul_le_mul_of_nonneg_left habs (hc j)
      _ = (∑ j, c j * |Z ω j|) + |t| * ∑ j, c j * |shift j| := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        calc
          _ = ∑ j, |t| * (c j * |shift j|) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = |t| * ∑ j, c j * |shift j| := by rw [Finset.mul_sum]
  have hshiftExpBound ω t :
      Real.exp (∑ j, c j * |Z ω j + t * shift j|) ≤
        Real.exp (∑ j, c j * |Z ω j|) *
          Real.exp (|t| * ∑ j, c j * |shift j|) := by
    calc
      _ ≤ Real.exp ((∑ j, c j * |Z ω j|) + |t| * ∑ j, c j * |shift j|) :=
        Real.exp_le_exp.mpr (hshiftBound ω t)
      _ = _ := by rw [Real.exp_add]
  have : 0 ≤ (Real.exp (∑ j, c j * |shift j|)) := by positivity
  have hGint : Integrable (fun ω => G (Z ω)) P := by
    apply (hbaseExp.const_mul M).mono'
    · exact hGmeas.aestronglyMeasurable.comp_aemeasurable
        (by
          apply AEMeasurable.of_eval
          intro j
          exact hZ.2.1 j)
    · filter_upwards [] with ω
      simpa [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hM (Real.exp_nonneg _)), baseExp] using hGbound (Z ω)
  have hDint j : Integrable (fun ω => D (Z ω) j) P := by
    apply (hbaseExp.const_mul M).mono'
    · exact (hDmeas j).aestronglyMeasurable.comp_aemeasurable (by
        apply AEMeasurable.of_eval
        intro k
        exact hZ.2.1 k)
    · filter_upwards [] with ω
      simpa [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hM (Real.exp_nonneg _)), baseExp] using hDbound (Z ω) j
  have hShiftInt : ∀ t, Integrable
      (fun ω => G (fun j => Z ω j + t * shift j)) P := by
    intro t
    let sf := Real.exp (|t| * ∑ j, c j * |shift j|)
    have hmeas : AEStronglyMeasurable
        (fun ω => G (fun j => Z ω j + t * shift j)) P := hGmeas.aestronglyMeasurable.comp_aemeasurable (by
        apply AEMeasurable.of_eval
        intro j
        exact (hZ.2.1 j).add (aemeasurable_const.mul (aemeasurable_const)) )
    apply (hbaseExp.const_mul (M * sf)).mono' hmeas
    filter_upwards [] with ω
    calc
      _ ≤ M * Real.exp (∑ j, c j * |Z ω j + t * shift j|) := hGbound _
      _ ≤ M * (baseExp ω * sf) := by
        dsimp [sf]
        exact mul_le_mul_of_nonneg_left (hshiftExpBound ω t) hM
      _ = M * sf * baseExp ω := by ring
  have hLmeas : ∀ᶠ t in 𝓝 0, AEStronglyMeasurable
      (fun ω => Real.exp (t * Z ω i - t ^ 2 / 2 * var) * G (Z ω)) P := by
    filter_upwards [] with t
    exact (Real.continuous_exp.comp_aestronglyMeasurable ((hZ.2.1 i).aestronglyMeasurable.const_mul t |>.sub (aestronglyMeasurable_const.mul_const _))).mul
      hGint.aestronglyMeasurable
  let tiltConst : ℝ := Real.exp (|var| / 2)
  have : 0 ≤ tiltConst := by positivity
  let bL : Ω → ℝ := fun ω => M * tiltConst *
    (|Z ω i| + |var|) * enlargedExp ω
  have hLbound : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      ‖(Z ω i - t * var) * Real.exp (t * Z ω i - t ^ 2 / 2 * var) * G (Z ω)‖ ≤ bL ω := by
    filter_upwards [] with ω t ht
    have : |t| ≤ 1 := by
      simpa using (le_of_lt (by simpa [Real.dist_eq] using ht))
    have harg : t * Z ω i - t ^ 2 / 2 * var ≤
        |Z ω i| + |var| / 2 := by
      have : t ^ 2 ≤ 1 := by
        nlinarith [sq_abs t, sq_nonneg (|t|), abs_nonneg t]
      calc
        _ ≤ |t| * |Z ω i| + t ^ 2 / 2 * |var| := by
          have : t * Z ω i ≤ |t| * |Z ω i| := by
            calc
              _ ≤ |t * Z ω i| := le_abs_self _
              _ = |t| * |Z ω i| := abs_mul _ _
          have : -(t ^ 2 / 2 * var) ≤ t ^ 2 / 2 * |var| := by
            calc
              _ = (t ^ 2 / 2) * (-var) := by ring
              _ ≤ (t ^ 2 / 2) * |var| :=
                mul_le_mul_of_nonneg_left (by simpa using (le_abs_self (-var))) (by positivity)
          nlinarith
        _ ≤ |Z ω i| + |var| / 2 := by nlinarith [abs_nonneg (Z ω i), abs_nonneg var]
    have : Real.exp (t * Z ω i - t ^ 2 / 2 * var) ≤
        tiltConst * Real.exp (|Z ω i|) := by
      calc
        _ ≤ Real.exp (|Z ω i| + |var| / 2) := Real.exp_le_exp.mpr harg
        _ = _ := by rw [Real.exp_add]; simp [tiltConst, mul_comm]
    have hsum : ∑ j, c' j * |Z ω j| =
        (∑ j, c j * |Z ω j|) + |Z ω i| := by
      dsimp [c']
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have hdelta : ∑ j, (if j = i then 1 else 0) * |Z ω j| = |Z ω i| := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hne
          simp [hne]
        · simp
      rw [hdelta]
    have : |Z ω i - t * var| ≤ |Z ω i| + |var| := by
      calc
        _ ≤ |Z ω i| + |t * var| := abs_sub _ _
        _ = |Z ω i| + |t| * |var| := by rw [abs_mul]
        _ ≤ |Z ω i| + |var| := by nlinarith [abs_nonneg var]
    have : ‖G (Z ω)‖ ≤ M * baseExp ω := by
      simpa [baseExp] using hGbound (Z ω)
    calc
      _ = |Z ω i - t * var| *
          Real.exp (t * Z ω i - t ^ 2 / 2 * var) * ‖G (Z ω)‖ := by
            simp [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (Real.exp_nonneg _), mul_assoc]
      _ ≤ (|Z ω i| + |var|) *
          (tiltConst * Real.exp (|Z ω i|)) * (M * baseExp ω) := by
            gcongr
      _ = bL ω := by
            dsimp [bL]
            rw [(show enlargedExp ω = baseExp ω * Real.exp |Z ω i| by dsimp [enlargedExp, baseExp]; rw [hsum, Real.exp_add])]
            dsimp [tiltConst]
            ring
  have hLdiff : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      HasDerivAt
        (fun s => Real.exp (s * Z ω i - s ^ 2 / 2 * var) * G (Z ω))
        ((Z ω i - t * var) * Real.exp (t * Z ω i - t ^ 2 / 2 * var) * G (Z ω)) t := by
    filter_upwards [] with ω t ht
    have hlin : HasDerivAt (fun s => s * Z ω i - s ^ 2 / 2 * var)
        (Z ω i - t * var) t := by
      convert ((hasDerivAt_id t).const_mul (Z ω i)).sub
        (((hasDerivAt_id t).pow 2).const_mul (var / 2)) using 1
      · ext s
        simp [id_eq]
        ring_nf
      · simp [id_eq]
        ring_nf
    convert ((Real.hasDerivAt_exp (t * Z ω i - t ^ 2 / 2 * var)).comp t hlin).const_mul (G (Z ω)) using 1
    · ext s
      simp
      ring
    · ring_nf
  have hRderivMeas : AEStronglyMeasurable
      (fun ω => ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * D (Z ω) j) P := by
    apply Finset.univ.aestronglyMeasurable_fun_sum
    intro j hj
    exact aestronglyMeasurable_const.mul
      ((hDmeas j).aestronglyMeasurable.comp_aemeasurable (by
        apply AEMeasurable.of_eval
        intro k
        exact hZ.2.1 k))
  let shiftMass : ℝ := ∑ j, c j * |shift j|
  let bR : Ω → ℝ := fun ω =>
    (∑ j, |gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j)|) *
      M * Real.exp shiftMass * baseExp ω
  have hRbound : ∀ᵐ ω ∂P, ∀ t ∈ Metric.ball 0 (1 : ℝ),
      ‖∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
        D (fun j => Z ω j + t * gaussianCovariance P (fun ω' => Z ω' j)
          (fun ω' => Z ω' i)) j‖ ≤ bR ω := by
    filter_upwards [] with ω t ht
    calc
      ‖∑ j, gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
          D (fun j => Z ω j + t * shift j) j‖ ≤
          ∑ j, ‖gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j) *
            D (fun j => Z ω j + t * shift j) j‖ := norm_sum_le _ _
      _ ≤ ∑ j, |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
          (M * (baseExp ω * Real.exp shiftMass)) := by
        apply Finset.sum_le_sum
        intro j hj
        have : Real.exp (|t| * shiftMass) ≤ Real.exp shiftMass := by
          apply Real.exp_le_exp.mpr
          calc
            |t| * shiftMass ≤ 1 * shiftMass :=
              mul_le_mul_of_nonneg_right (by simpa using (le_of_lt (by simpa [Real.dist_eq] using ht))) (by dsimp [shiftMass]; exact Finset.sum_nonneg fun k hk => mul_nonneg (hc k) (abs_nonneg (shift k)))
            _ = shiftMass := by ring
        have hterm : ‖D (fun k => Z ω k + t * shift k) j‖ ≤
            M * (baseExp ω * Real.exp shiftMass) := by
          calc
            _ ≤ M * Real.exp (∑ k, c k * |Z ω k + t * shift k|) := (hDbound (fun k => Z ω k + t * shift k) j)
            _ ≤ M * (baseExp ω * Real.exp (|t| * shiftMass)) := by
              exact mul_le_mul_of_nonneg_left (hshiftExpBound ω t) hM
            _ ≤ M * (baseExp ω * Real.exp shiftMass) := by gcongr
        calc
          _ = |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
                ‖D (fun k => Z ω k + t * shift k) j‖ := by
              rw [norm_mul, Real.norm_eq_abs]
          _ ≤ |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
                (M * (baseExp ω * Real.exp shiftMass)) :=
              mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
          _ = |gaussianCovariance P (fun ω' => Z ω' i) (fun ω' => Z ω' j)| *
                (M * (baseExp ω * Real.exp shiftMass)) := by ring
      _ = (∑ j, |gaussianCovariance P (fun ω' => Z ω' i)
            (fun ω' => Z ω' j)|) * (M * (baseExp ω * Real.exp shiftMass)) := by
        rw [← Finset.sum_mul]
      _ = bR ω := by
        dsimp [bR]
        ring
  exact finite_gaussian_integration_by_parts P Z hZ i G hGmeas D
    (fun j => hDint j) hShiftInt 1 (by norm_num)
    hLmeas (by simpa using hGint.const_mul 1) (by exact ((hZ.2.1 i).aestronglyMeasurable.mul hGint.aestronglyMeasurable).congr (ae_of_all P fun ω => by simp)) bL (by convert (((show Integrable (fun ω => |Z ω i| * enlargedExp ω) P by simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), enlargedExp] using (show Integrable (fun ω => Z ω i * enlargedExp ω) P by simpa [enlargedExp, c'] using centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable P Z hZ c' i).norm).const_mul (M * tiltConst)).add ((show Integrable enlargedExp P by simpa [enlargedExp, c'] using centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ c').const_mul (M * tiltConst * |var|))) using 1; ext ω; simp [bL]; ring) hLbound hLdiff
    (by filter_upwards [] with t; exact hGmeas.aestronglyMeasurable.comp_aemeasurable (by apply AEMeasurable.of_eval; intro j; exact (hZ.2.1 j).add aemeasurable_const)) hRderivMeas bR (hbaseExp.const_mul _) hRbound (by filter_upwards [] with ω t ht; simpa [shift, hcov_symm] using (hGdir (fun j => Z ω j) shift t))


end DOZZ.Proofs
