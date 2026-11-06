module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolutionMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforward

/-! # One-index time-bin localization of the canonical active density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/- The observation bin includes every position and the entire active velocity interval. -/
def entranceOutputBin (c : Clock) (j : ℤ) : Set Point :=
  entranceTimeBin c.r j ∩ {p | p.velocity 0 ∈ c.active}

/- Full-position observation bins are Borel. -/
theorem measurableSet_entranceOutputBin (c : Clock) (j : ℤ) :
    MeasurableSet (entranceOutputBin c j) :=
  (measurableSet_entranceTimeBin c.r j).inter
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/- The canonical positive pole density retains its exact strict future support. -/
theorem timeActiveDensity_support (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionActiveDensity hH hLE hlam hLam A c e z ≠ 0 →
        e.time < z.time ∧ z.velocity 0 ∈ c.active := by
  have hm : Measurable (positionActiveDensity hH hLE hlam hLam A c e) :=
    (measurable_positionActiveDensity hH hLE hlam hLam A c).comp
    (measurable_const.prodMk measurable_id)
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionActiveDensity hpush hH hLE hlam hLam,
    enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
  obtain ⟨_, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
  obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
  have hS : MeasurableSet (densityClockStrip c e) :=
    (continuous_time.measurable measurableSet_Ioi).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  rw [hG]
  exact (ae_restrict_mem hS).filter_mono (withDensity_absolutelyContinuous _ _).ae_le

/- Source and output bins determine the nonnegative elapsed restart delay. -/
def entranceBinDelay (j k : ℤ) : ℝ := max ((j : ℝ) - (k : ℝ) - 1) 0

/- A valid pole obeys its exponential tail on a whole-position output bin. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
