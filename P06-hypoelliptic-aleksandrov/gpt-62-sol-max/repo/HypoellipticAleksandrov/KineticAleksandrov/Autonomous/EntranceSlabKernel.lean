module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabQuadratic

/-! # The actual terminal family as a finite kernel

This kernel is definitionally the existing terminal family, including the
zero-duration branch. It introduces no alternative terminal measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

/-- The guard for the zero-duration branch of the actual terminal family is measurable. -/
theorem entranceSlabTerminal_guard_measurable (c : Clock) (J : Interval) (b : ℝ) :
    MeasurableSet {p : Point | p.time = b ∧
      p.velocity 0 ∈ (visitActiveUnion c J).carrier} :=
  (isClosed_eq continuous_time continuous_const).measurableSet.inter
    ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
include lam Lam A c J b

/-- The existing terminal family, packaged as a measurable finite kernel. -/
def entranceSlabTerminalKernel :
    Kernel Point Point :=
  Kernel.piecewise (entranceSlabTerminal_guard_measurable c J b) Kernel.id
    ((enlargedVisitExitKernel A (visitActiveUnion c J) b).restrict
      (show MeasurableSet {p : Point | p.time = b} from
        (isClosed_eq continuous_time continuous_const).measurableSet))

/-- The finite kernel is exactly the canonical terminal family at every pole. -/
theorem entranceSlabTerminalKernel_apply (p : Point) :
    entranceSlabTerminalKernel A c J b p =
      enlargedActiveTerminalFamily A c J b p := rfl

end

/-- Each actual terminal family has a uniform finite mass bound. -/
instance entranceSlabTerminalKernel_isFiniteKernel
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (entranceSlabTerminalKernel A c J b) := by
  unfold entranceSlabTerminalKernel
  infer_instance

/-- The actual terminal family is measurable, including its initial-value branch. -/
theorem entranceSlabTerminalFamily_measurable
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Measurable (enlargedActiveTerminalFamily A c J b) :=
  (entranceSlabTerminalKernel A c J b).measurable

/-- A mixture of actual terminal families is finite for any finite starting measure. -/
instance entranceSlabTerminal_bind_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    IsFiniteMeasure (mu.bind (enlargedActiveTerminalFamily A c J b)) :=
  inferInstanceAs (IsFiniteMeasure
    (entranceSlabTerminalKernel A c J b ∘ₘ mu))

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
  (mu : Measure Point)

/-- Actual terminal mixtures remain in the closed active velocity interval. -/
theorem entranceSlabTerminal_ae_velocity :
    ∀ᵐ q ∂mu.bind (enlargedActiveTerminalFamily A c J b),
      q.velocity 0 ∈ closure c.active := by
  change ∀ᵐ q ∂(entranceSlabTerminalKernel A c J b ∘ₘ mu), _
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  rw [entranceSlabTerminalKernel_apply]
  unfold enlargedActiveTerminalFamily
  split
  · rename_i hp
    apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
    exact subset_closure (Eq.le (visitActiveUnion_carrier c J) hp.right).left
  · have hz := enlargedActiveExitMixture_ae_velocity A c J b
      (Measure.dirac p)
    rw [Measure.dirac_bind
      (enlargedVisitExitKernel A (visitActiveUnion c J) b).measurable p]
      at hz
    exact hz.filter_mono (ae_mono Measure.restrict_le_self)

/-- The source quadratic is integrable on every finite actual terminal mixture. -/
theorem entranceSlabTerminal_quadratic_integrable [IsFiniteMeasure mu] :
    Integrable (fun q => visitQuadratic c (q.velocity 0))
      (mu.bind (enlargedActiveTerminalFamily A c J b)) := 
  visitQuadratic_integrable_of_active_support c _ (entranceSlabTerminal_ae_velocity A c J b mu)

end

/-- Outside the open active interval the source quadratic is nonpositive. -/
theorem entranceSlabQuadratic_nonpos (c : Clock) (v : ℝ) (hv : v ∉ c.active) :
    visitQuadratic c v ≤ 0 := by
  have hr := c.positive
  change ¬(c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4) at hv
  rw [visitQuadratic]
  by_cases hl : c.vbar - 3 * c.r / 4 < v
  · have hu : c.vbar + 3 * c.r / 4 ≤ v := le_of_not_gt (fun h => hv ⟨hl, h⟩)
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl.le) (sub_nonpos.mpr hu)
  · have hl' : v ≤ c.vbar - 3 * c.r / 4 := le_of_not_gt hl
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl') (by linarith)

/-- The quadratic terminal contribution charges only the open active band. -/
theorem entranceSlabQuadratic_integral_le_active (c : Clock) (mu : Measure Point)
    [IsFiniteMeasure mu] (hi : Integrable (fun q => visitQuadratic c (q.velocity 0)) mu) :
    (∫ q, visitQuadratic c (q.velocity 0) ∂mu) ≤
      9 * c.r ^ 2 / 16 * (mu {q | q.velocity 0 ∈ c.active}).toReal := by
  let B : Set Point := {q | q.velocity 0 ∈ c.active}
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage
    ((continuous_apply 0).comp continuous_velocity).measurable
  have hm := integral_mono_ae hi ((integrable_const (9 * c.r ^ 2 / 16)).indicator hB)
    (Filter.Eventually.of_forall fun q => by
      by_cases hq : q ∈ B
      · rw [indicator_of_mem hq]
        exact visitQuadratic_le c _
      · rw [indicator_of_notMem hq]
        exact entranceSlabQuadratic_nonpos c _ hq)
  rw [integral_indicator hB] at hm
  simpa only [integral_const, smul_eq_mul, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm] using hm

/-- Removing starts can only decrease the actual terminal mixture. -/
theorem entranceSlabTerminal_restrict_bind_le
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) (D : Set Point) :
    (mu.restrict D).bind (enlargedActiveTerminalFamily A c J b) ≤
      mu.bind (enlargedActiveTerminalFamily A c J b) := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB
    (entranceSlabTerminalFamily_measurable A c J b).aemeasurable,
    Measure.bind_apply hB
      (entranceSlabTerminalFamily_measurable A c J b).aemeasurable]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
