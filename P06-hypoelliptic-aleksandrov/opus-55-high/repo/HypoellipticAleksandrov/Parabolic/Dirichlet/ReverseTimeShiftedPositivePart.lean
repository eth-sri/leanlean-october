module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing

/-!
# Shifted positive parts in reverse-time Bochner space

This module lifts the spatial shifted positive part to reverse-time `L²(V)` when
the truncation threshold depends affinely on reverse time.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The totalized affine reverse-time threshold.  Its values at negative raw
times have no mathematical semantics; on nonnegative times it represents
`M + τ N`. -/
def reverseTimeAffineThreshold (M N : ℝ≥0) (τ : ℝ) : ℝ≥0 :=
  M + τ.toNNReal * N

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T)

/-- On nonnegative times, the totalized threshold has the expected real value. -/
theorem coe_reverseTimeAffineThreshold_of_nonneg
     {τ : ℝ} (hτ : 0 ≤ τ) :
    (reverseTimeAffineThreshold M N τ : ℝ) = (M : ℝ) + τ * (N : ℝ) := by
  simp only [reverseTimeAffineThreshold, NNReal.coe_add, NNReal.coe_mul,
    Real.coe_toNNReal _ hτ]

private theorem continuous_reverseTimeAffineThreshold  :
    Continuous (reverseTimeAffineThreshold M N) := continuous_const.add (continuous_real_toNNReal.mul continuous_const)

private theorem aestronglyMeasurable_reverseTimeAffineThreshold
     :
    AEStronglyMeasurable (reverseTimeAffineThreshold M N)
      (reverseTimeVolume T) :=
  (continuous_reverseTimeAffineThreshold M N).aestronglyMeasurable

private theorem aestronglyMeasurable_reverseTimeInputThresholdPair
     : AEStronglyMeasurable
      (fun τ : ℝ => (u τ, reverseTimeAffineThreshold M N τ))
      (reverseTimeVolume T) :=
  (Lp.memLp u).aestronglyMeasurable.prodMk
    (aestronglyMeasurable_reverseTimeAffineThreshold T M N)

private theorem aestronglyMeasurable_h10ShiftedPositivePart_comp
    
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p : α → H10HilbertGraph hΩ × ℝ≥0)
    (hp : AEStronglyMeasurable p μ) :
    AEStronglyMeasurable
      (fun x => h10ShiftedPositivePart hΩ (p x).1 (p x).2) μ := (continuous_h10ShiftedPositivePart hΩ).comp_aestronglyMeasurable hp

private theorem aestronglyMeasurable_reverseTimeShiftedPositivePart
     : AEStronglyMeasurable
      (fun τ => h10ShiftedPositivePart hΩ (u τ)
        (reverseTimeAffineThreshold M N τ)) (reverseTimeVolume T) := aestronglyMeasurable_h10ShiftedPositivePart_comp hΩ
    (fun τ : ℝ => (u τ, reverseTimeAffineThreshold M N τ))
    (aestronglyMeasurable_reverseTimeInputThresholdPair hΩ T M N u)

/-- The affine-threshold truncation belongs to the reverse-time Bochner space. -/
theorem reverseTimeShiftedPositivePart_memLp
     :
    MemLp (fun τ => h10ShiftedPositivePart hΩ (u τ)
      (reverseTimeAffineThreshold M N τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume T) := by
  refine MemLp.of_le (Lp.memLp u)
    (aestronglyMeasurable_reverseTimeShiftedPositivePart hΩ T M N u) ?_
  filter_upwards with τ
  exact norm_h10ShiftedPositivePart_le hΩ _
    _

/-- The pointwise shifted positive part with affine threshold, lifted to
reverse-time Bochner `L²(V)`. -/
def reverseTimeShiftedPositivePart
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) : ReverseTimeL2V hΩ T :=
  (reverseTimeShiftedPositivePart_memLp hΩ T M N u).toLp
    (fun τ => h10ShiftedPositivePart hΩ (u τ)
      (reverseTimeAffineThreshold M N τ))

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T)

/-- The Bochner lift agrees almost everywhere with pointwise affine-threshold
truncation. -/
theorem coeFn_reverseTimeShiftedPositivePart
     :
    reverseTimeShiftedPositivePart hΩ T M N u =ᵐ[reverseTimeVolume T]
      fun τ => h10ShiftedPositivePart hΩ (u τ)
        (reverseTimeAffineThreshold M N τ) :=
  (reverseTimeShiftedPositivePart_memLp hΩ T M N u).coeFn_toLp

/-- Pairing a reverse-time dual curve with the affine-threshold shifted
positive part is integrable. -/
theorem integrable_reverseTimeDualPairing_shiftedPositivePart
     (g : ReverseTimeL2VStar hΩ T) :
    Integrable (fun τ => (g τ) (h10ShiftedPositivePart hΩ (u τ)
      (reverseTimeAffineThreshold M N τ))) (reverseTimeVolume T) := by
  refine (integrable_reverseTimeDualPairing hΩ T
    (reverseTimeShiftedPositivePart hΩ T M N u) g).congr ?_
  filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with τ hτ
  rw [hτ]

end HypoellipticAleksandrov.Parabolic.Dirichlet
