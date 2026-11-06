module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturn

/-! # The literal scalar semigroup statement of velocity return -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/- The source's active velocity indicator, as actual bounded Borel scalar data. -/
def activeVelocityDatum (c : Clock) : BoundedBorel Z := by
  let B : Set Z := {w | w.2 ∈ c.active}
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage measurable_snd
  exact ⟨B.indicator (fun _ => 1), measurable_const.indicator hB,
    ⟨1, zero_le_one, fun w => by
      by_cases hw : w ∈ B
      · simp only [indicator_of_mem hw, abs_one, le_refl]
      · simp only [indicator_of_notMem hw, abs_zero, zero_le_one]⟩⟩

/- Scalar and native physical terminal kernels agree at every nonnegative elapsed time. -/
theorem return_Kphysical_eq_kernelXV
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (t : ℝ) (ht : 0 ≤ t) (z : Z) :
    Kphysical hH hLE hlam hLam A t z =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z := by
  unfold Kphysical kernelXV wholeQuery
  rw [dite_eq_left ht]
  simp only [Real.coe_toNNReal t ht]
  rfl

/- The source active indicator action is the real mass of the same active velocity set. -/
theorem activeVelocityDatum_action_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (t : ℝ) (ht : 0 ≤ t) (z : Z) :
    S hH hLE hlam hLam A t (activeVelocityDatum c) z =
      (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z
        {w | w.2 ∈ c.active}).toReal := by
  rw [S_eq_integral hH hLE hlam hLam A t ht]
  change (∫ w, ({w : Z | w.2 ∈ c.active}).indicator (fun _ => (1 : ℝ)) w
    ∂Kphysical hH hLE hlam hLam A t z) = _
  have hB : MeasurableSet {w : Z | w.2 ∈ c.active} :=
    isOpen_Ioo.measurableSet.preimage measurable_snd
  rw [integral_indicator hB]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    return_Kphysical_eq_kernelXV hH hLE hlam hLam A t ht]

/- Literal equation `e:velocity-return`, with the scalar source return-time premise. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
