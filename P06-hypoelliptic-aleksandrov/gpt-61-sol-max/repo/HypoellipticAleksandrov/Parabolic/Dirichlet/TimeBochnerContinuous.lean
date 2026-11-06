module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandAffine

open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeVolume_real_univ from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandAffine


/-!
# Continuous curves in reverse-time Bochner spaces

This module places a curve continuous on the closed reverse-time interval in
the quotient-valued Bochner `L²` space over the literal open interval.  Its
representative comparison is only almost everywhere.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The real mass of the literal positive reverse-time interval. -/
alias reverseTimeVolume_real_univ := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeVolume_real_univ


/-- The squared Bochner `L²` norm is the integral of the pointwise squared norm. -/
theorem integral_norm_sq_eq_norm_sq_toLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} (w : α → E)
    (hw : MeasureTheory.MemLp w (2 ) μ) :
    (∫ t, ‖w t‖ ^ 2 ∂μ) = ‖hw.toLp w‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hw.coeFn_toLp,
    hw.eLpNorm_eq_integral_rpow_norm]
  · simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    exact (Real.rpow_inv_natCast_pow
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
  · norm_num
  · simp

variable {E : Type*}

/-- A curve continuous on the closed interval belongs to reverse-time Bochner `L²`.

For nonpositive `T`, the literal carrier `Ioo 0 T` is empty. -/
theorem memLp_two_reverseTime_of_continuousOn
     [NormedAddCommGroup E]
    (T : ℝ) (w : ℝ → E) (hw : ContinuousOn w (Set.Icc 0 T)) :
    MeasureTheory.MemLp w (2 ) (reverseTimeVolume T) := by
  by_cases hT : 0 < T
  · let K  := Icc 0 T
    have hKcompact : IsCompact K := isCompact_Icc
    have hKmeas : MeasurableSet K := measurableSet_Icc
    letI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact hKcompact.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hw
    have hKmem : MemLp w (2 ) (volume.restrict K) := by
      refine MemLp.of_bound (hw.aestronglyMeasurable_of_isCompact hKcompact hKmeas) C ?_
      filter_upwards [ae_restrict_mem hKmeas] with t ht
      exact hC t ht
    simpa only [K, reverseTimeVolume, reverseTimeOpenInterval] using
      hKmem.mono_measure (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  · simp_all [reverseTimeVolume, reverseTimeOpenInterval]

/-- The quotient-valued reverse-time Bochner `L²` class of a continuous curve. -/
def reverseTimeL2OfContinuousOn
     [NormedAddCommGroup E]
    (T : ℝ) (w : ℝ → E) (hw : ContinuousOn w (Set.Icc 0 T))  :=
  (memLp_two_reverseTime_of_continuousOn T w hw).toLp w

/-- The continuous curve represents its reverse-time Bochner class almost everywhere. -/
theorem coeFn_reverseTimeL2OfContinuousOn
     [NormedAddCommGroup E]
    (T : ℝ) (w : ℝ → E) (hw : ContinuousOn w (Set.Icc 0 T)) :
    reverseTimeL2OfContinuousOn T w hw =ᵐ[reverseTimeVolume T] w := (memLp_two_reverseTime_of_continuousOn T w hw).coeFn_toLp

end HypoellipticAleksandrov.Parabolic.Dirichlet
