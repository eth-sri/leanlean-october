module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ResidualNorm
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.SmoothDerivatives
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Quantitative residual and restricted norm bounds -/

 public section

namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Set MeasureTheory

variable {N : ℕ}

/-- The scalar residual is continuous wherever the coefficient and selected jet are continuous. -/
theorem continuousOn_residual  {V : HypoellipticAleksandrov.Parabolic.Region N}
    (a : TimeVelocity N → PDE.Mat N) (q : HypoellipticAleksandrov.Parabolic.ScalarField N)
    (ha : ContinuousOn a V) (hq : IsScalarC12On q V) :
    ContinuousOn (residual a q) V := by
  apply hq.continuousOn_scalarTimeDerivative.sub
  unfold matrixContraction
  apply continuousOn_finset_sum
  intro i _
  apply continuousOn_finset_sum
  intro j _
  exact (((continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn ha)).mul
    ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hq.continuousOn_scalarSpatialHessian)))

/-- Smooth functions and continuous coefficients have a continuous scalar residual. -/
theorem continuous_residual  (a : TimeVelocity N → PDE.Mat N)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField N) (ha : Continuous a) (hq : ContDiff ℝ 2 q) :
    Continuous (residual a q) := by
  apply continuousOn_univ.mp
  exact continuousOn_residual a q ha.continuousOn (isScalarC12On_of_contDiff_two hq univ)

/-- A bounded coefficient contraction amplifies uniform selected-jet errors by a finite factor. -/
theorem residual_difference_le  (a : PDE.Mat N)
    (q w : HypoellipticAleksandrov.Parabolic.ScalarField N) (z : TimeVelocity N) {δ M : ℝ}
    (hδ : 0 ≤ δ) (hM : (∑ i, ∑ j, |a i j|) ≤ M)
    (ht : |scalarTimeDerivative w z - scalarTimeDerivative q z| ≤ δ)
    (hh : ∀ i j, |scalarSpatialHessian w z i j - scalarSpatialHessian q z i j| ≤ δ) :
    |residual (fun _ => a) w z - residual (fun _ => a) q z| ≤ δ * (1 + M) := by

  have he : residual (fun _ => a) w z - residual (fun _ => a) q z =
      (scalarTimeDerivative w z - scalarTimeDerivative q z) -
      (matrixContraction a (scalarSpatialHessian w z) -
        matrixContraction a (scalarSpatialHessian q z)) := by unfold residual; ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add ht (by
      simp only [matrixContraction, ← Finset.sum_sub_distrib, ← mul_sub]
      calc
        |∑ i, ∑ j, a i j * (scalarSpatialHessian w z i j -
            scalarSpatialHessian q z i j)| ≤
            ∑ i, ∑ j, |a i j * (scalarSpatialHessian w z i j -
              scalarSpatialHessian q z i j)| := (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i, ∑ j, |a i j| * δ := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hh i j) (abs_nonneg _)
        _ ≤ δ * M := by
          simp only [← Finset.sum_mul]
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hM hδ)).trans_eq (by ring))

/-- A nonnegative source plus a constant bounds the positive residual in the restricted norm. -/
theorem positive_norm_le_add_constant
     {Q : HypoellipticAleksandrov.Parabolic.Region N} (hQ : MeasurableSet Q)
    (hfinite : volume Q < ⊤) (F G : HypoellipticAleksandrov.Parabolic.ScalarField N)
    (hF : AEStronglyMeasurable F (volume.restrict Q))
    (hG : MemLp G (parabolicExponent N) (volume.restrict Q))
    (hG0 : ∀ z ∈ Q, 0 ≤ G z) {e : ℝ} (he : 0 ≤ e)
    (hbound : ∀ z ∈ Q, F z ≤ G z + e) :
    parabolicLpNormOn N (fun z => max (F z) 0) Q ≤
      parabolicLpNormOn N G Q + e * parabolicLpNormOn N (fun _ => (1 )) Q := by
  letI : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩




  have hmono := ENNReal.toReal_mono (hG.add (memLp_const e)).eLpNorm_ne_top (eLpNorm_mono_ae ((continuous_id.max continuous_const).comp_aestronglyMeasurable hF) (show ∀ᵐ z ∂volume.restrict Q, ‖max (F z) 0‖ ≤ ‖G z + e‖ by
      filter_upwards [ae_restrict_mem hQ] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (hG0 z hz) he)]
      exact max_le (hbound z hz) (add_nonneg (hG0 z hz) he)))

  have hconst : lpNorm (fun _ : TimeVelocity N => e) (parabolicExponent N)
      (volume.restrict Q) = e * parabolicLpNormOn N (fun _ => (1 )) Q := by
    have h := lpNorm_const_smul e (fun _ : TimeVelocity N => (1 : ℝ))
      (volume.restrict Q) (p := parabolicExponent N)
    simpa only [Pi.smul_def, smul_eq_mul, mul_one, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg he]
      using! h
  exact hmono.trans ((lpNorm_add_le hG (by simp [parabolicExponent]) (g := fun _ => e)).trans_eq (by rw [hconst]; rfl))

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
