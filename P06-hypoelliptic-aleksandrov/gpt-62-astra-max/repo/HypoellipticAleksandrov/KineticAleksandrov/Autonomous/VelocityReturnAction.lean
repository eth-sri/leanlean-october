module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturn

/-! # The literal scalar semigroup statement of velocity return -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (t : ℝ) (ht : 0 ≤ t) (z : Z)

include c in
/-- The source's active velocity indicator, as actual bounded Borel scalar data. -/
def activeVelocityDatum : BoundedBorel Z := by
  let B : Set Z := {w | w.2 ∈ c.active}
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage measurable_snd
  exact ⟨B.indicator (fun _ => 1), measurable_const.indicator hB,
    ⟨1, zero_le_one, fun w => by
      by_cases hw : w ∈ B
      · simp only [indicator_of_mem hw, abs_one, le_refl]
      · simp only [indicator_of_notMem hw, abs_zero, zero_le_one]⟩⟩

include ht in
/-- Scalar and native physical terminal kernels agree at every nonnegative elapsed time. -/
theorem return_Kphysical_eq_kernelXV :
    Kphysical hlam hLam A t z =
      kernelXV (fullSpaceEvolution hlam hLam A) (Real.toNNReal t) z := by
  unfold Kphysical kernelXV wholeQuery
  rw [dite_eq_left ht]
  simp only [Real.coe_toNNReal t ht]
  rfl

include ht in
/-- The source active indicator action is the real mass of the same active velocity set. -/
theorem activeVelocityDatum_action_eq :
    S hlam hLam A t (activeVelocityDatum c) z =
      (kernelXV (fullSpaceEvolution hlam hLam A) (Real.toNNReal t) z
        {w | w.2 ∈ c.active}).toReal := by
  rw [S_eq_integral hlam hLam A t ht]
  change (∫ w, ({w : Z | w.2 ∈ c.active}).indicator (fun _ => 1) w
    ∂Kphysical hlam hLam A t z) = _
  have hB : MeasurableSet {w : Z | w.2 ∈ c.active} :=
    isOpen_Ioo.measurableSet.preimage measurable_snd
  rw [integral_indicator hB]
  simp [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, return_Kphysical_eq_kernelXV hlam hLam A t ht]

/-- Literal equation `e:velocity-return`, with the scalar source return-time premise. -/
theorem velocity_return_action_of_return_time
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hlam hLam A t F (X, v) ≤ C * S hlam hLam A s F (X, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (z : Z) (t : ℝ),
      |c.vbar| = 2 * c.r → |z.2| ≤ 3 * c.r → 0 ≤ t →
      S hlam hLam A t (activeVelocityDatum c) z ≤
        C * (1 + t / c.r ^ 2) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := velocity_band_return_of_return_time hlam hLam hReturn
  refine ⟨C, hC, ?_⟩
  intro A c z t hc hz ht
  rw [activeVelocityDatum_action_eq hlam hLam A c t ht z]
  have hsub : {w : Z | w.2 ∈ c.active} ⊆ {w | |w.2| ≤ 3 * c.r} := by
    intro w hw
    have hh := (c.active_abs_bounds hw).2
    rw [hc] at hh
    change |w.2| ≤ 3 * c.r
    linarith only [hh]
  apply (ENNReal.toReal_mono (((measure_mono (subset_univ {w : Z | |w.2| ≤ 3 * c.r})).trans (kernelXV_mass_le_one (fullSpaceEvolution hlam hLam A) (Real.toNNReal t) z)).trans_lt ENNReal.one_lt_top).ne
    (measure_mono hsub)).trans
  simpa only [Real.coe_toNNReal t ht] using h A c.r z (Real.toNNReal t) c.positive hz

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
