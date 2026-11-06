module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothCoefficients
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization

/-! # Coefficient errors vanish for each fixed smooth function -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ}

/-- A spatial almost everywhere statement lifts to native kinetic spacetime volume. -/
theorem ae_spatial_lift  {P : XV d → Prop} (hP : ∀ᵐ q ∂volume, P q) :
    ∀ᵐ z : KineticPoint d ∂volume, P (z.position, z.velocity) := by
  have hs : Measure.QuasiMeasurePreserving Prod.snd
      (volume : Measure (ℝ × XV d)) volume := by
    fun_prop
  exact (hs.comp (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving).ae hP

/-- Fixed-function coefficient mollification has vanishing full contraction error in Lp. -/
theorem smooth_coefficient_error_tendsto 
    (A : XV d → PDE.Mat d) (lam Lam : ℝ)
    (hA : ∀ i k, Measurable (fun q => A q i k))
    (hbound : ∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d))
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × XV d =>
      u ((KineticPoint.equivProd d).symm q)))
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun P => matrixContraction
      (mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) -
        A (P.position, P.velocity)) (kineticVelocityHessian u P))
      p (volume.restrict (backwardCylinder P₀ R))) atTop (𝓝 0) := by
  let C := 3 * (|lam| + |Lam|)
  obtain ⟨M, hM, hH⟩ := kineticVelocityHessian_bound_on_cylinder P₀ R hR u hu
  have hcv := continuous_kineticVelocityHessian_of_joint_smooth u hu
  have hsp : Continuous (fun P : KineticPoint d => (P.position, P.velocity)) :=
    continuous_position.prodMk continuous_velocity
  have hqmeas := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let : IsFiniteMeasure _ :=
    ⟨by rw [Measure.restrict_apply_univ]; exact backwardCylinder_volume_lt_top P₀ R hR⟩
  have hs n := smooth_coefficients_same_bounds (standardMollifierSequence n)
    A lam Lam hA hbound
  have hc n i k : Continuous
      (fun q => mollifiedMatrix _ A q i k) :=
    (continuous_apply k).comp ((continuous_apply i).comp (hs n).1.continuous)
  refine bounded_convergence_eLpNorm (volume.restrict _) p hp0 hp
    _
    ?_ (d * d * (2 * C * M)) ?_ ?_
  · intro n
    apply AEStronglyMeasurable.restrict
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro k hk
    exact (((hc n i k).measurable.comp hsp.measurable).sub
      ((hA i k).comp hsp.measurable)).mul
      (((continuous_apply k).comp ((continuous_apply i).comp hcv)).measurable)
  · intro n
    apply ae_restrict_of_forall_mem hqmeas
    intro P hP
    have hb i k : ‖(mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) i k -
        A (P.position, P.velocity) i k) * kineticVelocityHessian u P i k‖ ≤ 2 * C * M := by
      have h1 := coefficient_entry_abs_le_of_ellipticity
        ((hs n).2 _).1 ((hs n).2 (P.position, P.velocity)).2 i k
      have h2 := coefficient_entry_abs_le_of_ellipticity
        (hbound _).1 (hbound (P.position, P.velocity)).2 i k
      rw [norm_mul]
      apply mul_le_mul _ (hH P hP i k) (norm_nonneg _) (by positivity)
      exact (norm_sub_le _ _).trans (by
        simp only [Real.norm_eq_abs]
        linarith only [h1, h2])
    calc
      _ ≤ ∑ i : Fin d, ∑ k : Fin d, ‖(mollifiedMatrix _ A
          _ i k - A _ i k) *
          kineticVelocityHessian u P i k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ _i : Fin d, ∑ _k : Fin d, 2 * C * M :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hb i k))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  · filter_upwards [ae_restrict_of_ae (ae_spatial_lift
      (ae_tendsto_mollifiedMatrix A lam Lam hA hbound))] with P hP
    have he i k : Tendsto (fun n =>
        (mollifiedMatrix (standardMollifierSequence n) A (P.position, P.velocity) i k -
          A (P.position, P.velocity) i k) * kineticVelocityHessian u P i k)
        atTop (𝓝 0) := by
      have h := ((continuous_apply k).comp (continuous_apply i)).continuousAt.tendsto.comp hP
      change Tendsto (fun n => mollifiedMatrix _ A
        _ i k) atTop (𝓝 (A _ i k)) at h
      simpa using!
        (h.sub_const (A (P.position, P.velocity) i k)).mul_const
          _
    have hh := tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun k _ => he i k))
    aesop

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
