module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Shifted positive-part inequality for the reverse-time spatial form

This file proves the fixed-slice spatial-form inequality for testing against
`(u - k)₊`.  The scalar integrability assumptions are exactly those needed by
the literal total integrals in the form.
-/

 public section

open MeasureTheory Set
open scoped ENNReal NNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private theorem h10ShiftedPositivePart_gradientCoord

    (u : H10HilbertGraph hΩ) (k : ℝ≥0) (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
    (PDE.hilbertVectorLpCoord Ω (2 ) i
      (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y =
      {z | (k : ℝ) < valueCLM hΩ u z}.indicator
        (fun z => (PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ u)) z) y := by
  let sharedTerm_88e2a0a076 := ({z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z})
  filter_upwards [gradientCLM_h10ShiftedPositivePart hΩ u k,
    PDE.coeFn_hilbertVectorLpCoord Ω _ i (gradientCLM hΩ u),
    PDE.coeFn_hilbertVectorLpCoord Ω _ i
      (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))] with y hg hu hw
  by_cases hy : (k : ℝ) < valueCLM hΩ u y
  · calc
      _ = (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) y).ofLp i := hw
      _ = (gradientCLM hΩ u y).ofLp i := congrArg (fun q => q.ofLp i)
        (hg.trans (Set.indicator_of_mem
          (s := sharedTerm_88e2a0a076) hy
          _))
      _ = _ := hu.symm
      _ = _ := (Set.indicator_of_mem
        (s := sharedTerm_88e2a0a076) hy _).symm
  · calc
      _ = (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) y).ofLp i := hw
      _ = (0 : PDE.HilbertVec d).ofLp i := congrArg (fun q => q.ofLp i)
        (hg.trans (Set.indicator_of_notMem
          (s := sharedTerm_88e2a0a076) hy
          _))
      _ = 0 := rfl
      _ = _ := (Set.indicator_of_notMem
        (s := sharedTerm_88e2a0a076) hy _).symm

variable (r₁ τ : ℝ)

variable (a : CoefficientField d)

private theorem reverseTimePrincipal_shiftedPositivePart_eq

      (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω (2 ) i
            (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω (2 ) j
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y *
            (PDE.hilbertVectorLpCoord Ω (2 ) i
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y := by
  let sharedTerm_347a70e238 := ({z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z})
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [h10ShiftedPositivePart_gradientCoord hΩ u k j,
    h10ShiftedPositivePart_gradientCoord hΩ u k i] with y hj hi
  by_cases hy : (k : ℝ) < valueCLM hΩ u y
  · have hj' := hj.trans (Set.indicator_of_mem
      (s := sharedTerm_347a70e238) hy _)
    have hi' := hi.trans (Set.indicator_of_mem
      (s := sharedTerm_347a70e238) hy _)
    rw [hj', hi']
  · have hj' := hj.trans (Set.indicator_of_notMem
      (s := sharedTerm_347a70e238) hy _)
    have hi' := hi.trans (Set.indicator_of_notMem
      (s := sharedTerm_347a70e238) hy _)
    rw [hj', hi']
    ring

private theorem reverseTimeDrift_shiftedPositivePart_eq


    (b : PDE.TimeVectorField d) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
      (∑ j : Fin d, ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y) =
        ∑ j : Fin d, ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω (2 ) j
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y *
            valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y := by
  let sharedTerm_a00f65ba41 := ({z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z})
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [h10ShiftedPositivePart_gradientCoord hΩ u k j,
    coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with y hj hw
  by_cases hy : (k : ℝ) < valueCLM hΩ u y
  · have hj' := hj.trans (Set.indicator_of_mem
      (s := sharedTerm_a00f65ba41) hy _)
    rw [hj']
  · have hj' := hj.trans (Set.indicator_of_notMem
      (s := sharedTerm_a00f65ba41) hy _)
    have hw0 : valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 := by
      rw [hw, max_eq_right]
      exact sub_nonpos.mpr (le_of_not_gt hy)
    rw [hj', hw0]
    ring

private theorem reverseTimeScalar_shiftedPositivePart_le
      (c : PDE.TimeScalarField d)
    (u : H10HilbertGraph hΩ) (k : ℝ≥0)
    (hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω,
      reverseTimeScalarCoefficient r₁ c τ y ≤ 0)
    (hScalarSquare : Integrable
      (fun y  => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω))
    (hScalarCross : Integrable
      (fun y  => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) :
    (∫ y, reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y *
      valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) ≤
      ∫ y, reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω := by
  let q := (reverseTimeScalarCoefficient r₁ c τ)
  let w := fun y  => valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y
  have hvalue := coeFn_valueCLM_h10ShiftedPositivePart hΩ u k
  have hremainder : Integrable (fun y => q y * (k : ℝ) * w y) (PDE.volumeOn Ω) := by
    apply (hScalarCross.sub hScalarSquare).congr
    filter_upwards [hvalue] with y hw
    dsimp only [q, w] at *
    by_cases hy : (k : ℝ) < valueCLM hΩ u y
    · have hwu : w y = valueCLM hΩ u y - (k : ℝ) := by
        simpa only [w, max_eq_left (sub_nonneg.mpr (le_of_lt hy))] using hw
      change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y =
        valueCLM hΩ u y - (k : ℝ) at hwu
      simp only [Pi.sub_apply]
      rw [hwu]
      ring
    · have hw0 : w y = 0 := by
        simpa only [w, max_eq_right (sub_nonpos.mpr (le_of_not_gt hy))] using hw
      change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 at hw0
      simp only [Pi.sub_apply, hw0, mul_zero]
      exact sub_self 0
  have hremainderNonpos : (∫ y, q y * (k : ℝ) * w y ∂PDE.volumeOn Ω) ≤ 0 := by
    rw [← integral_zero]
    apply integral_mono_ae hremainder (integrable_zero _ _ _)
    filter_upwards [hScalarNonpos, hvalue] with y hq hw

    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hq k.2) (by
        simpa only [w, hw] using le_max_right (valueCLM hΩ u y - (k : ℝ)) 0)
  have hscalar :
      (∫ y, q y * valueCLM hΩ u y * w y ∂PDE.volumeOn Ω) ≤
        ∫ y, q y * w y * w y ∂PDE.volumeOn Ω := by
    have hadd : (∫ y, q y * valueCLM hΩ u y * w y ∂PDE.volumeOn Ω) =
        (∫ y, q y * w y * w y ∂PDE.volumeOn Ω) +
          ∫ y, q y * (k : ℝ) * w y ∂PDE.volumeOn Ω := by
      rw [← integral_add hScalarSquare hremainder]
      apply integral_congr_ae
      filter_upwards [hvalue] with y hw
      dsimp only [q, w] at *
      by_cases hy : (k : ℝ) < valueCLM hΩ u y
      · have hwu : w y = valueCLM hΩ u y - (k : ℝ) := by
          simpa only [w, max_eq_left (sub_nonneg.mpr (le_of_lt hy))] using hw
        change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y =
          valueCLM hΩ u y - (k : ℝ) at hwu
        rw [hwu]
        ring
      · have hw0 : w y = 0 := by
          simpa only [w, max_eq_right (sub_nonpos.mpr (le_of_not_gt hy))] using hw
        change valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 at hw0
        rw [hw0]
        ring
    rw [hadd]
    linarith
  dsimp only [q, w] at hscalar
  exact hscalar

variable (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d) (u : H10HilbertGraph hΩ) (k : ℝ≥0)

private theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_scalar_le

    (hscalar :
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) ≤
        ∫ y, reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
  rw [reverseTimeSpatialForm_apply]
  rw [reverseTimePrincipal_shiftedPositivePart_eq hΩ r₁ τ a u k]
  rw [reverseTimeDrift_shiftedPositivePart_eq hΩ r₁ τ a b u k]
  rw [reverseTimeSpatialForm_apply]
  exact sub_le_sub_left hscalar _

/-- Testing the reverse-time spatial form against `(u - k)₊` dominates the
form with `(u - k)₊` in both slots when the reverse-time scalar coefficient is
nonpositive. -/
theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge

    (hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω,
      reverseTimeScalarCoefficient r₁ c τ y ≤ 0)
    (hScalarSquare : Integrable
      (fun y  => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω))
    (hScalarCross : Integrable
      (fun y  => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := (reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_scalar_le hΩ r₁ τ a b c u k
  (reverseTimeScalar_shiftedPositivePart_le hΩ r₁ τ c u k hScalarNonpos hScalarSquare hScalarCross))

end HypoellipticAleksandrov.Parabolic.Dirichlet
