module

public import RequestProject.FactorialGaugeInverse
public import RequestProject.HardyVolterraBridge

/-!
# Actual boundary reconstruction from the driven factorial gauge

Finite-stage differentiation, integration and the true vanishing tail
give the primitive recurrence on every subinterval. The factorial inverse
then reconstructs the zeroth physical row as a convergent Vekua series.
These identities use the actual driven vector, without assuming an
interior reconstruction or an infinite derivative interchange.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

variable (γ : ℝ → ℂ)

theorem physicalDrivenQ_sq {E : ℝ} (hE : 0 ≤ E) :
    physicalDrivenQ E ^ 2 = -E / 4 := by
  have hs : (Real.sqrt E : ℂ) ^ 2 = E := by
    exact_mod_cast Real.sq_sqrt hE
  norm_num [physicalDrivenQ, div_pow, mul_pow, hs]

theorem physicalDrivenGauge_weightedIntegral_hasSum_to
    (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) (j : ℕ) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Icc 0 (2 * Real.pi))) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    HasSum (fun l  => ∫ s in 0..θ,
      w s * physicalDrivenGaugeTerm γ E y j l s)
      (∫ s in 0..θ, w s * physicalDrivenGauge γ E y j s) := by
  obtain ⟨u, hu, hbd⟩ := exists_physicalDrivenGaugeTerm_majorant γ hγ E y hy j
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hsub : uIoc 0 θ ⊆ Icc 0 (2 * Real.pi) := by
    grind
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
     (bound := fun l _ => C * u l) ?_ ?_ ?_ intervalIntegrable_const ?_
  · intro l
    exact ((hw.mul (physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j l)).mono hsub).aestronglyMeasurable
      measurableSet_uIoc
  · intro l
    exact Eventually.of_forall fun s hs => by
      rw [norm_mul]
      exact mul_le_mul (hC s (hsub hs)) (hbd l s (hsub hs)) (norm_nonneg _) ((norm_nonneg _).trans (hC 0 ⟨le_rfl, Real.two_pi_pos.le⟩))
  · exact Eventually.of_forall fun _ _ => hu.mul_left C
  · exact Eventually.of_forall fun s _ =>
      ((summable_norm_physicalDrivenGaugeTerm γ E y j s).of_norm.hasSum).mul_left (w s)

theorem physicalDrivenGaugePartial_weightedIntegral_tendsto_to
    (hγ : Continuous γ) (E : ℝ) (y : ℝ → Ell2)
    (hy : ContinuousOn y (Icc 0 (2 * Real.pi))) (j : ℕ) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Icc 0 (2 * Real.pi))) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    Tendsto (fun N  => ∫ s in 0..θ,
      w s * physicalDrivenGaugePartial γ E y j N s) atTop
      (𝓝 (∫ s in 0..θ, w s * physicalDrivenGauge γ E y j s)) := by
  have he (N : ℕ) : (∫ s in 0..θ,
      w s * physicalDrivenGaugePartial γ E y j N s) =
      ∑ l ∈ Finset.range (N + 1), ∫ s in 0..θ,
        w s * physicalDrivenGaugeTerm γ E y j l s := by
    unfold physicalDrivenGaugePartial
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun l _ =>
      ((hw.mul (physicalDrivenGaugeTerm_continuousOn γ hγ E y hy j l)).mono (by
    rw [uIcc_of_le hθ.1]
    grind)).intervalIntegrable)
  have h_simpa := (physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ E y hy j w hw hθ).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simp only [he] at h_simpa ⊢
  assumption

end PolyaNeumann

end
