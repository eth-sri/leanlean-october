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

variable (hpush : PushforwardStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (j k : ℤ)
    (he : e ∈ entranceTimeBin c.r k) (hv : e.velocity 0 ∈ c.active)

include c in
/-- The observation bin includes every position and the entire active velocity interval. -/
def entranceOutputBin (j : ℤ) : Set Point :=
  entranceTimeBin c.r j ∩ {p | p.velocity 0 ∈ c.active}

/-- Full-position observation bins are Borel. -/
theorem measurableSet_entranceOutputBin (j : ℤ) :
    MeasurableSet (entranceOutputBin c j) :=
  (measurableSet_entranceTimeBin c.r j).inter
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

include hpush in
/-- The canonical positive pole density retains its exact strict future support. -/
theorem timeActiveDensity_support (he : e.velocity 0 ∈ c.active) :
    ∀ᵐ z ∂(volume : Measure Point),
      positionActiveDensity hlam hLam A c e z ≠ 0 →
        e.time < z.time ∧ z.velocity 0 ∈ c.active := by
  have hm : Measurable (positionActiveDensity hlam hLam A c e) :=
    (measurable_positionActiveDensity hlam hLam A c).comp
    (measurable_const.prodMk measurable_id)
  apply (ae_withDensity_iff hm).mp
  rw [withDensity_positionActiveDensity hpush hlam hLam,
    enlargedActiveGreenKernel_apply hlam hLam A c e he]
  obtain ⟨_, _, hd⟩ := (hpush lam Lam hlam hLam).2 (5 / 4) (by norm_num)
  obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
  rw [hG]
  exact (ae_restrict_mem ((continuous_time.measurable measurableSet_Ioi).inter (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable))).filter_mono (withDensity_absolutelyContinuous _ _).ae_le

include j k in
/-- Source and output bins determine the nonnegative elapsed restart delay. -/
def entranceBinDelay : ℝ := max ((j : ℝ) - (k : ℝ) - 1) 0

include hpush he hv in
/-- A valid pole obeys its exponential tail on a whole-position output bin. -/
theorem timeActiveDensity_output_tail
    (q : ℝ) (hq : 0 < q) (K : ℝ≥0∞)
    (htail : positionPositiveNorm
      (volume.restrict {z | e.time + entranceBinDelay j k * c.r ^ 2 ≤ z.time ∧
        z.velocity 0 ∈ c.active}) q
      (positionActiveDensity hlam hLam A c e) ≤ K) :
    positionPositiveNorm (volume.restrict (entranceOutputBin c j)) q
      (positionActiveDensity hlam hLam A c e) ≤ K := by
  apply LE.le.trans _ htail
  apply positionPositiveNorm_restrict_le volume _ q hq _ _
    (measurableSet_entranceOutputBin c j)
    ((continuous_time.measurable measurableSet_Ici).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))
  filter_upwards [timeActiveDensity_support hpush hlam hLam A c e hv]
    with z hz hcell hnonzero
  have hs := hz hnonzero
  refine ⟨?_, hs.2⟩
  have hzlo := hcell.1.1
  unfold entranceBinDelay
  by_cases h : 0 ≤ j - (k : ℝ) - 1
  · rw [max_eq_left h]
    calc
      _ ≤ (k + 1) * c.r ^ 2 + (j - k - 1) * c.r ^ 2 :=
        add_le_add (he.2) le_rfl
      _ = j * c.r ^ 2 := by ring
      _ ≤ z.time := hzlo.le
  · rw [max_eq_right (le_of_not_ge h), zero_mul, add_zero]
    exact hs.1.le

include hpush he hv in
/-- Later starting bins cannot contribute to an earlier output bin. -/
theorem timeActiveDensity_output_zero (hjk : j < k) :
    ∀ᵐ z ∂volume.restrict (entranceOutputBin c j),
      positionActiveDensity hlam hLam A c e z = 0 := by
  filter_upwards [ae_restrict_of_ae
    (timeActiveDensity_support hpush hlam hLam A c e hv),
    ae_restrict_mem (measurableSet_entranceOutputBin c j)] with z hz hcell
  by_contra hn
  have hs := (hz hn).1
  have hcast : j + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
  have hh := mul_le_mul_of_nonneg_right hcast (sq_nonneg c.r)
  have helo := he.1
  linarith [hcell.1.2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
