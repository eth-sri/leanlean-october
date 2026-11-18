module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartEnergySupport
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeShiftedPositivePartConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Mass
public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.IntegralGronwall
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalNegation

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder






/-- Testing the reverse-time spatial form against `(u - k)₊` dominates the
form with `(u - k)₊` in both slots when the reverse-time scalar coefficient is
nonpositive. -/
theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (u : H10HilbertGraph hΩ) (k : ℝ≥0)
    (hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω,
      reverseTimeScalarCoefficient r₁ c τ y ≤ 0)
    (hScalarSquare : Integrable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω))
    (hScalarCross : Integrable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k)    := by
  have h10ShiftedPositivePart_gradientCoord {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (k : ℝ≥0) (i : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω,
    (PDE.hilbertVectorLpCoord Ω 2 i
      (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y =
      {z | (k : ℝ) < valueCLM hΩ u z}.indicator
        (fun z => (PDE.hilbertVectorLpCoord Ω 2 i
          (gradientCLM hΩ u)) z) y := by
    filter_upwards [gradientCLM_h10ShiftedPositivePart hΩ u k,
      PDE.coeFn_hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u),
      PDE.coeFn_hilbertVectorLpCoord Ω 2 i
        (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))] with y hg hu hw
    by_cases hy : (k : ℝ) < valueCLM hΩ u y
    · calc
        _ = (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) y).ofLp i := hw
        _ = (gradientCLM hΩ u y).ofLp i := congrArg (fun q => q.ofLp i)
          (hg.trans (Set.indicator_of_mem
            (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy
            (gradientCLM hΩ u)))
        _ = _ := hu.symm
        _ = _ := (Set.indicator_of_mem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _).symm
    · calc
        _ = (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k) y).ofLp i := hw
        _ = (0 : PDE.HilbertVec d).ofLp i := congrArg (fun q => q.ofLp i)
          (hg.trans (Set.indicator_of_notMem
            (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy
            (gradientCLM hΩ u)))
        _ = 0 := rfl
        _ = _ := (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _).symm
  have reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_scalar_le {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (u : H10HilbertGraph hΩ) (k : ℝ≥0) (hscalar : (∫ y, reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) ≤
        ∫ y, reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) :
      reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
    have reverseTimeDrift_shiftedPositivePart_eq {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
        (∑ j : Fin d, ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y *
            valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y) =
          ∑ j : Fin d, ∫ y in Ω,
            reverseTimeDivergenceDrift r₁ a b τ y j *
              (PDE.hilbertVectorLpCoord Ω 2 j
                (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y *
              valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y := by
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [h10ShiftedPositivePart_gradientCoord hΩ u k j,
        coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with y hj hw
      by_cases hy : (k : ℝ) < valueCLM hΩ u y
      · have hj' := hj.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
        rw [hj']
      · have hj' := hj.trans (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
        have hw0 : valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y = 0 := by
          rw [hw, max_eq_right]
          exact sub_nonpos.mpr (le_of_not_gt hy)
        rw [hj', hw0]
        ring
    have reverseTimePrincipal_shiftedPositivePart_eq {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ u)) y *
            (PDE.hilbertVectorLpCoord Ω 2 i
              (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y) =
          ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
            a (r₁ - τ) y i j *
              (PDE.hilbertVectorLpCoord Ω 2 j
                (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y *
              (PDE.hilbertVectorLpCoord Ω 2 i
                (gradientCLM hΩ (h10ShiftedPositivePart hΩ u k))) y := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [h10ShiftedPositivePart_gradientCoord hΩ u k j,
        h10ShiftedPositivePart_gradientCoord hΩ u k i] with y hj hi
      by_cases hy : (k : ℝ) < valueCLM hΩ u y
      · have hj' := hj.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
        have hi' := hi.trans (Set.indicator_of_mem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
        rw [hj', hi']
      · have hj' := hj.trans (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
        have hi' := hi.trans (Set.indicator_of_notMem
          (s := {z : PDE.Vec d | (k : ℝ) < valueCLM hΩ u z}) hy _)
        rw [hj', hi']
        ring
    rw [reverseTimeSpatialForm_apply]
    rw [reverseTimePrincipal_shiftedPositivePart_eq hΩ r₁ τ a u k]
    rw [reverseTimeDrift_shiftedPositivePart_eq hΩ r₁ τ a b u k]
    rw [reverseTimeSpatialForm_apply]
    exact sub_le_sub_left hscalar _
  have reverseTimeScalar_shiftedPositivePart_le {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (c : ℝ → PDE.Vec d → ℝ) (u : H10HilbertGraph hΩ) (k : ℝ≥0) (hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω,
      reverseTimeScalarCoefficient r₁ c τ y ≤ 0) (hScalarSquare : Integrable
      (fun y => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
          valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) (hScalarCross : Integrable
      (fun y => reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y)
      (PDE.volumeOn Ω)) :
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y *
      valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω) ≤
      ∫ y, reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y *
        valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y ∂PDE.volumeOn Ω := by
    let q := fun y => reverseTimeScalarCoefficient r₁ c τ y
    let w := fun y => valueCLM hΩ (h10ShiftedPositivePart hΩ u k) y
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
      have hwNonneg : 0 ≤ w y := by
        simpa only [w, hw] using le_max_right (valueCLM hΩ u y - (k : ℝ)) 0
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hq k.2) hwNonneg
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
  exact reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_scalar_le
    hΩ r₁ τ a b c u k (reverseTimeScalar_shiftedPositivePart_le hΩ r₁ τ c u k hScalarNonpos hScalarSquare hScalarCross)


/-- Smoothness of the scalar coefficient on a bounded closed cylinder supplies
the fixed-slice shifted positive-part spatial-form inequality. -/
theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
  let q := fun y => reverseTimeScalarCoefficient r₁ c τ y
  let U := valueCLM hΩ u
  let W := valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
  obtain ⟨C, hC, hCbound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded c hcSmooth
  have hqMeas : AEStronglyMeasurable q (PDE.volumeOn Ω) := by
    exact (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
      r₀ r₁ τ c hcSmooth hτ).aestronglyMeasurable hΩ.measurableSet
  have hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa [q] using hCbound τ hτ y hy
  have hScalarSquare : Integrable (fun y => q y * W y * W y) (PDE.volumeOn Ω) := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (scalarL2Multiplier q hqMeas C hC hqBound W) W).congr ?_
    filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound W] with y hy
    rw [hy]
    simp
    ring
  have hScalarCross : Integrable (fun y => q y * U y * W y) (PDE.volumeOn Ω) := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (scalarL2Multiplier q hqMeas C hC hqBound U) W).congr ?_
    filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound U] with y hy
    rw [hy]
    simp
    ring
  have hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω, q y ≤ 0 := by
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [h₀₁, hτ.1, hτ.2]
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa only [q, reverseTimeScalarCoefficient_apply] using
      hcNonpos (r₁ - τ, y) ⟨htime, subset_closure hy⟩
  exact reverseTimeSpatialForm_apply_shiftedPositivePart_ge hΩ r₁ τ a b c u k
    hScalarNonpos (by simpa only [q, W] using hScalarSquare)
    (by simpa only [q, U, W] using hScalarCross)

section
open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace
section
open MeasureTheory
open scoped ENNReal NNReal Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}


/-- On a bounded domain, the spatial `L²` shifted positive part is jointly
continuous in the function and its nonnegative constant threshold. -/
theorem continuous_shiftedPositivePartValue_of_isBounded
    (hΩbounded : Bornology.IsBounded Ω) :
    Continuous (fun p : PDE.ScalarLp Ω (2 : ℝ≥0∞) × ℝ≥0 =>
      shiftedPositivePartValue p.2 p.1)  := by
  have shiftedPositivePartValue_eq_posPart_sub_const [IsFiniteMeasure (PDE.volumeOn Ω)] (k : ℝ≥0) (f : PDE.ScalarLp Ω 2) :
      shiftedPositivePartValue k f =
      Lp.posPart (f - Lp.const 2 (PDE.volumeOn Ω) (k : ℝ)) := by
    apply Lp.ext
    filter_upwards [coeFn_shiftedPositivePartValue k f,
      Lp.coeFn_posPart (f - Lp.const 2 (PDE.volumeOn Ω) (k : ℝ)),
      Lp.coeFn_sub f (Lp.const 2 (PDE.volumeOn Ω) (k : ℝ)),
      Lp.coeFn_const (p := 2) (μ := PDE.volumeOn Ω) (k : ℝ)] with x hshift hpos hsub hconst
    rw [hshift, hpos, hsub]
    simp only [Pi.sub_apply, hconst, Function.const_apply]
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  rw [show (fun p : PDE.ScalarLp Ω 2 × ℝ≥0 =>
      shiftedPositivePartValue p.2 p.1) =
      fun p => Lp.posPart
        (p.1 - Lp.constL 2 (PDE.volumeOn Ω) ℝ (p.2 : ℝ)) by
    funext p
    exact shiftedPositivePartValue_eq_posPart_sub_const p.2 p.1]
  exact Lp.continuous_posPart.comp
    (continuous_fst.sub
      ((Lp.constL 2 (PDE.volumeOn Ω) ℝ).continuous.comp
        (NNReal.continuous_coe.comp continuous_snd)))

end

private theorem forward_shifted_rate_continuous
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0) {h : ℝ} (hh : 0 < h)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Continuous (shiftedPositivePartEnergyRate hΩ hΩb M N
      (fun s ↦ reverseTimeForwardSteklov T h u s)
      (fun s ↦ reverseTimeForwardSteklov T h g s)) := by
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  exact ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub (continuous_const.mul
    ((spatialMassCLM hΩb).continuous.comp ((valueCLM hΩ).continuous.comp hp)))

private theorem forward_shifted_halfEnergy_continuous
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    {h : ℝ} (hh : 0 < h) (u : ReverseTimeL2V hΩ T) :
    Continuous (fun t ↦ shiftedPositivePartHalfEnergy hΩ
      (reverseTimeForwardSteklov T h u t) (reverseTimeAffineThreshold M N t)) := by
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  convert (continuous_const : Continuous (fun _ : ℝ ↦ (1 / 2 : ℝ))).mul ((continuous_norm.comp ((valueCLM hΩ).continuous.comp hp)).pow 2) using 1
  funext t
  simp only [Function.comp_def, Pi.mul_def, Pi.pow_def, shiftedPositivePartHalfEnergy,
    valueCLM_h10ShiftedPositivePart]

private theorem hasDerivAt_forward_shifted_halfEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b t : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hb : b + h ≤ T) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ shiftedPositivePartHalfEnergy hΩ
      (reverseTimeForwardSteklov T h u s) (reverseTimeAffineThreshold M N s))
      (shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeForwardSteklov T h u s)
        (fun s ↦ reverseTimeForwardSteklov T h g s) t) t := by
  exact hasDerivAt_shiftedPositivePartHalfEnergy hΩ hΩb M N _
    (continuous_reverseTimeForwardSteklov T h hh u) _ t (by linarith [ha, ht.1])
    (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hd hh
      (by linarith [ha, ht.1]) (by linarith [hb, ht.2]))

/-- Half-energy identity underlying the forward fixed-window formula. -/
theorem reverseTimeForwardSteklov_shiftedPositivePart_halfEnergy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b + h ≤ T) :
    shiftedPositivePartHalfEnergy hΩ (reverseTimeForwardSteklov T h u b)
        (reverseTimeAffineThreshold M N b) -
      shiftedPositivePartHalfEnergy hΩ (reverseTimeForwardSteklov T h u a)
        (reverseTimeAffineThreshold M N a) =
      ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeForwardSteklov T h u s)
        (fun s ↦ reverseTimeForwardSteklov T h g s) t := by
  rw [← (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (forward_shifted_halfEnergy_continuous hΩ T M N hh u).continuousOn (fun t ht ↦ hasDerivAt_forward_shifted_halfEnergy hΩ hΩb T hT M N u g hd hh ha hb ht) ((forward_shifted_rate_continuous hΩ hΩb T M N hh u g).intervalIntegrable a b)), intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]


/-- Fixed-window forward Steklov shifted-positive-part energy identity. -/
theorem reverseTimeForwardSteklov_shiftedPositivePart_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b + h ≤ T) :
    shiftedPositivePartEnergy hΩ M N (fun t ↦ reverseTimeForwardSteklov T h u t) b -
      shiftedPositivePartEnergy hΩ M N (fun t ↦ reverseTimeForwardSteklov T h u t) a =
      2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩb M N
        (fun s ↦ reverseTimeForwardSteklov T h u s)
        (fun s ↦ reverseTimeForwardSteklov T h g s) t := by
  rw [← reverseTimeForwardSteklov_shiftedPositivePart_halfEnergy_identity hΩ
    hΩb T hT M N u g hd hh ha hab hb]
  simp only [shiftedPositivePartEnergy, shiftedPositivePartHalfEnergy,
    valueCLM_h10ShiftedPositivePart]
  ring



private noncomputable def rawShiftedPositivePartEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) : ℝ → ℝ :=
  shiftedPositivePartEnergy hΩ M N u

private noncomputable def rawShiftedPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ) : ℝ → ℝ :=
  fun t => 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t

private noncomputable def reverseTimeShiftedPositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => ∫ r in Ioc 0 t,
    rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T

private theorem integrable_rawShiftedPositivePartEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    Integrable (rawShiftedPositivePartEnergy hΩ M N u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  have hu :=
    memLp_congr_ae (by
      filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with t ht
      exact congrArg (valueCLM hΩ) ht) |>.mp
      ((Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).continuousLinearMap_comp
        (valueCLM hΩ))
  unfold rawShiftedPositivePartEnergy shiftedPositivePartEnergy
  exact hu.integrable_norm_pow (by norm_num : 2 ≠ 0)

private theorem integrable_rawShiftedPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g)
      (reverseTimeVolume T) := by
  unfold rawShiftedPositivePartEnergyRate
  apply Integrable.const_mul
  unfold shiftedPositivePartEnergyRate
  apply ((integrable_reverseTimeDualPairing_shiftedPositivePart hΩ T M N u g).sub ((integrable_reverseTimeShiftedPositivePart_spatialMass hΩ hΩbounded T M N u).const_mul (N : ℝ))).congr
  filter_upwards with t
  simp only [Pi.sub_apply]
  rw [spatialMassCLM_apply]

private theorem continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    ContinuousOn (reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g) (Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo 0 T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).integrableOn

private theorem reverseTimeShiftedPositivePartEnergyPrimitive_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g t -
        reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g s =
      ∫ r in Ioc s t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r
        ∂reverseTimeVolume T := by
  change (∫ r in Ioc 0 t, _ ∂reverseTimeVolume T) -
      (∫ r in Ioc 0 s, _ ∂reverseTimeVolume T) = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).intervalIntegrable
      (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]


private theorem integral_reverseTime_eq_integral_Icc_of_tsupport_subset
    {T a b : ℝ} {F phi : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) (hphi : tsupport phi ⊆ Ioo a b) :
    (∫ t, F t * phi t ∂reverseTimeVolume T) = ∫ t in Icc a b, F t * phi t := by
  change (∫ t in Ioo 0 T, F t * phi t) = ∫ t in Icc a b, F t * phi t
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hK
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun hts => ht.2
    ⟨le_of_lt (hphi hts).1, le_of_lt (hphi hts).2⟩)]
  ring

private theorem integral_energy_mul_deriv_eq_neg_integral_rate_of_increment
    {a b : ℝ} {E Q : ℝ → ℝ} (hab : a ≤ b)
    (hQ : Continuous Q)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      E t - E s = ∫ r in Icc s t, Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, E t * deriv eta t) = -(∫ t in Icc a b, Q t * eta t) := by
  have hQIcc : IntegrableOn Q (Icc a b) volume := hQ.integrableOn_Icc
  have hEformula : ∀ t ∈ Icc a b, E t = PDE.intervalPrimitive a Q t + E a := by
    intro t ht
    have h := hinc a ⟨le_rfl, hab⟩ t ht ht.1
    calc
      E t = (∫ r in Icc a t, Q r) + E a := by linarith
      _ = PDE.intervalPrimitive a Q t + E a := by
        rw [PDE.intervalPrimitive_eq_setIntegral_Icc ht.1]
  rw [show (∫ t in Icc a b, E t * deriv eta t) =
      ∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hEformula t ht]]
  calc
    (∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t) =
        (∫ t in Icc a b, PDE.intervalPrimitive a Q t * deriv eta t) +
          ∫ t in Icc a b, E a * deriv eta t := by
      rw [← integral_add]
      · apply setIntegral_congr_fun measurableSet_Icc
        intro t _
        ring
      · exact ((PDE.continuousOn_intervalPrimitive hab hQIcc).mul
          (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
      · exact (heta.continuous_deriv (by simp)).integrableOn_Icc.const_mul (E a)
    _ = -(∫ t in Icc a b, Q t * eta t) := by
      rw [PDE.intervalPrimitive_scalar_weak_identity_Icc hQIcc heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc heta.contDiffOn hab]
        rw [(image_eq_zero_of_notMem_tsupport (fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1)), (image_eq_zero_of_notMem_tsupport (fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2))]
        ring
      rw [integral_const_mul, htail]
      ring

private theorem eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N
          (fun r => reverseTimeForwardSteklov T h u r) t * eta.deriv t) =
      -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun r => reverseTimeForwardSteklov T h u r)
          (fun r => reverseTimeForwardSteklov T h g r) t * eta t) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  let x := fun r => reverseTimeForwardSteklov T h u r
  let y := fun r => reverseTimeForwardSteklov T h g r
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  have hQ : Continuous (fun r => 2 * shiftedPositivePartEnergyRate
      hΩ hΩbounded M N x y r) := by
    exact continuous_const.mul
      (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
        (continuous_const.mul
          (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp)))
  have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      shiftedPositivePartEnergy hΩ M N x t - shiftedPositivePartEnergy hΩ M N x s =
        ∫ r in Icc s t, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N x y r := by
    intro s hs t ht hst
    rw [reverseTimeForwardSteklov_shiftedPositivePart_energy_identity hΩ hΩbounded T hT
      M N u g hderiv hh (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall]),
      integral_const_mul]
  exact integral_energy_mul_deriv_eq_neg_integral_rate_of_increment hab.le hQ hinc
    (eta.contDiff.of_le (by simp)) heta

private theorem rawShiftedPositivePartEnergy_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T)  := by
  have exists_strict_test_collar :
      ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧
      tsupport (eta : ℝ → ℝ) ⊆ Ioo a b ∧ tsupport eta.deriv ⊆ Ioo a b := by
    by_cases hsupport : (tsupport (eta : ℝ → ℝ)).Nonempty
    · obtain ⟨lo, hlo, hloMin⟩ :=
        eta.hasCompactSupport.exists_isMinOn hsupport continuousOn_id
      obtain ⟨hi, hhi, hhiMax⟩ :=
        eta.hasCompactSupport.exists_isMaxOn hsupport continuousOn_id
      obtain ⟨a, ha0, halo⟩ := exists_between (eta.tsupport_subset hlo).1
      obtain ⟨b, hhib, hbT⟩ := exists_between (eta.tsupport_subset hhi).2
      refine ⟨a, b, ha0, lt_of_lt_of_le halo ((hloMin hhi).trans_lt hhib).le, hbT, ?_, ?_⟩
      · intro t ht
        exact ⟨lt_of_lt_of_le halo (hloMin ht), lt_of_le_of_lt (hhiMax ht) hhib⟩
      · have hd : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) := by
          rw [ReverseTimeScalarTest.deriv, tsupport]
          exact closure_minimal support_deriv_subset (isClosed_tsupport _)
        exact hd.trans (by
          intro t ht
          exact ⟨lt_of_lt_of_le halo (hloMin ht), lt_of_le_of_lt (hhiMax ht) hhib⟩)
    · have heta : (eta : ℝ → ℝ) = 0 := by
        funext t
        apply image_eq_zero_of_notMem_tsupport
        exact fun ht => hsupport ⟨t, ht⟩
      have hderiv : eta.deriv = 0 := by
        funext t
        rw [eta.deriv_apply, heta]
        simp
      refine ⟨T / 3, 2 * T / 3, by linarith, by linarith, by linarith, ?_, ?_⟩
      · rw [heta]
        simp
      · rw [hderiv]
        simp
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_test_collar
  have hK : Icc a b ⊆ Ioo 0 T := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hzero : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
      (𝓝 ((∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N u t * eta.deriv t) +
        2 * ∫ t in Icc a b,
          shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t)) := by
    apply ((tendsto_forwardSteklov_shiftedPositivePartEnergy_test hΩ M N T u eta ha hab hb).add (tendsto_const_nhds.mul (tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test hΩ hΩbounded M N T u g eta ha hab hb))).congr'
    filter_upwards [(eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity hΩ hΩbounded T hT M N u g hderiv eta ha hab hb heta)] with h hh
    have hfactor : (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun r => reverseTimeForwardSteklov T h u r)
        (fun r => reverseTimeForwardSteklov T h g r) t * eta t) =
        2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun r => reverseTimeForwardSteklov T h u r)
          (fun r => reverseTimeForwardSteklov T h g r) t * eta t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [hfactor] at hh
    exact (eq_neg_iff_add_eq_zero).mp hh
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  change _ = -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate
    hΩ hΩbounded M N u g t * eta t)
  rw [show (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate
      hΩ hΩbounded M N u g t * eta t) =
      2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate
        hΩ hΩbounded M N u g t * eta t by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    ring]
  exact (eq_neg_iff_add_eq_zero).mpr (tendsto_nhds_unique hzero tendsto_const_nhds)

private theorem integrable_reverseTimeShiftedPositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g) (reverseTimeVolume T) := by
  change IntegrableOn _ (Ioo 0 T) volume
  exact (continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
    hΩ hΩbounded T M N u g).integrableOn_Icc.mono_set Ioo_subset_Icc_self


private theorem reverseTimeShiftedPositivePartEnergyPrimitive_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g t *
      eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T) := by
  have hrIcc : IntegrableOn (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g)
      (Icc 0 T) volume := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, IntegrableOn] using (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g)
  have hae : (fun t => reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g t * eta.deriv t) =ᵐ[reverseTimeVolume T]
      fun t => PDE.intervalPrimitive 0
        (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g) t * deriv eta t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change (∫ r in Ioc 0 t, _ ∂reverseTimeVolume T) * eta.deriv t = _
    rw [show (∫ r in Ioc 0 t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r
        ∂reverseTimeVolume T) = ∫ r in Ioc 0 t,
          rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂volume by
      simp only [reverseTimeVolume, reverseTimeOpenInterval,
        Measure.restrict_restrict measurableSet_Ioc]
      rw [inter_eq_left.mpr]
      intro r hr'
      exact ⟨hr'.1, lt_of_le_of_lt hr'.2 ht.2⟩,
      (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
      PDE.intervalPrimitive]
  calc
    _ = ∫ t, PDE.intervalPrimitive 0
        (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g) t * deriv eta t
        ∂reverseTimeVolume T := integral_congr_ae hae
    _ = _ := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo hrIcc
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

private theorem exists_continuous_shiftedPositivePartEnergyRepresentative
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ e : ℝ → ℝ, ContinuousOn e (Icc 0 T) ∧
      e =ᵐ[reverseTimeVolume T] rawShiftedPositivePartEnergy hΩ M N u ∧
      ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t,
          rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T  := by
  have integrable_mul_reverseTimeScalarTest_deriv {T : ℝ} {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T)) (eta : ReverseTimeScalarTest T) :
      Integrable (fun t => f t * eta.deriv t) (reverseTimeVolume T) := by
    obtain ⟨C, hC⟩ := eta.exists_norm_deriv_le
    apply hf.mul_bdd eta.contDiff_deriv.continuous.aestronglyMeasurable
    filter_upwards with t
    exact hC t
  let P := reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g
  let defect := fun t => rawShiftedPositivePartEnergy hΩ M N u t - P t
  have hdefInt : Integrable defect (reverseTimeVolume T) :=
    (integrable_rawShiftedPositivePartEnergy hΩ T M N u).sub
      (integrable_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g)
  have hdefZero : ∀ eta : ReverseTimeScalarTest T,
      (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) = 0 := by
    intro eta
    rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
        (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
          ∂reverseTimeVolume T) -
        ∫ t, P t * eta.deriv t ∂reverseTimeVolume T by
      rw [← integral_sub (integrable_mul_reverseTimeScalarTest_deriv (integrable_rawShiftedPositivePartEnergy hΩ T M N u) eta) (integrable_mul_reverseTimeScalarTest_deriv (integrable_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g) eta)]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [defect]
      ring,
      rawShiftedPositivePartEnergy_test_deriv hΩ hΩbounded T hT M N u g hderiv eta,
      reverseTimeShiftedPositivePartEnergyPrimitive_test_deriv hΩ hΩbounded T M N u g eta]
    ring
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt hdefZero
  let e := fun t => P t + c
  have heCont : ContinuousOn e (Icc 0 T) :=
    (continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g).add continuousOn_const
  have heAE : e =ᵐ[reverseTimeVolume T] rawShiftedPositivePartEnergy hΩ M N u := by
    filter_upwards [hc] with t ht
    dsimp only [defect, e] at ht ⊢
    linarith
  refine ⟨e, heCont, heAE, ?_⟩
  intro s t hs ht hst
  calc
    e t - e s = P t - P s := by dsimp only [e]; ring
    _ = _ := reverseTimeShiftedPositivePartEnergyPrimitive_sub
      hΩ hΩbounded T M N u g hs ht hst

/-- Moving-threshold shifted-positive-part energy increment for the canonical
closed-time Hilbert representative. -/
theorem reverseTimeHilbertRepresentative_shiftedPositivePart_norm_sq_increment
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩)‖ ^ 2 -
      ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N s)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩)‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t,
        ((g r) (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r)) -
          (N : ℝ) * spatialMassCLM hΩbounded
            (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
              (reverseTimeAffineThreshold M N r))))
        ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, heAE, heInc⟩ :=
    exists_continuous_shiftedPositivePartEnergyRepresentative
      hΩ hΩbounded T hT M N u g hderiv
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let E : ℝ → ℝ := fun r => if hr : r ∈ Icc 0 T then
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, hr⟩)‖ ^ 2
    else 0
  have hECont : ContinuousOn E (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict E = fun r : (Icc 0 T) =>
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N (r : ℝ))
          (Ubar r)‖ ^ 2 := by
      funext r
      simp only [Set.domRestrict_apply, E, dif_pos r.2]
    rw [hEq]
    exact (continuous_norm.comp
      ((continuous_shiftedPositivePartValue_of_isBounded hΩbounded).comp
        (Ubar.continuous.prodMk
          ((continuous_const.add (continuous_real_toNNReal.mul continuous_const)).comp
            continuous_subtype_val)))).pow 2
  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hAE : E =ᵐ[volume.restrict (Icc 0 T)] e := by
    have hrep' : ∀ᵐ r ∂volume.restrict (Icc 0 T),
        ∀ hr : r ∈ Ioo 0 T, Ubar ⟨r, ⟨hr.1.le, hr.2.le⟩⟩ = valueCLM hΩ (u r) := by
      simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
        reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc, IntegrableOn] using hrep
    have he' : e =ᵐ[volume.restrict (Icc 0 T)]
        rawShiftedPositivePartEnergy hΩ M N u := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heAE
    have hi : ∀ᵐ r ∂volume.restrict (Icc 0 T), r ∈ Ioo 0 T := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hrep', he', hi] with r hU he hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
    change (if h : r ∈ Icc 0 T then
      ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, h⟩)‖ ^ 2
      else 0) = e r
    rw [dif_pos hr', hU hr, ← valueCLM_h10ShiftedPositivePart]
    exact he.symm
  have hEqOn :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hAE hECont heCont
  calc
    _ = E t - E s := by
      change ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t) (Ubar ⟨t, ht⟩)‖ ^ 2 -
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N s) (Ubar ⟨s, hs⟩)‖ ^ 2 = _
      dsimp only [E]
      rw [dif_pos ht, dif_pos hs]
    _ = e t - e s := congrArg₂ (· - ·) (hEqOn ht) (hEqOn hs)
    _ = _ := by
      rw [heInc s t hs ht hst]
      simp only [rawShiftedPositivePartEnergyRate, shiftedPositivePartEnergyRate,
        integral_const_mul]

end

private def affineUpperClamp (T r : ℝ) := min T (max 0 r)

private theorem affineUpperClamp_mem {T : ℝ} (hT : 0 < T) (r : ℝ) :
    affineUpperClamp T r ∈ Icc 0 T :=
  ⟨le_min hT.le (le_max_left _ _), min_le_left _ _⟩

private theorem affineUpperClamp_eq {T r : ℝ} (hr : r ∈ Icc 0 T) :
    affineUpperClamp T r = r := by
  simp only [affineUpperClamp, max_eq_right hr.1, min_eq_right hr.2]



private theorem affineUpper_value_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (_hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T)
    (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ r in Ioc 0 t,
        ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M N r))‖ ^ 2 ∂reverseTimeVolume T) =
      ∫ r in Ioc 0 t,
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r)
          (reverseTimeHilbertRepresentative hΩ T hT u g hd
            ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩)‖ ^ 2  := by
  have affineUpper_setIntegral_eq (f : ℝ → ℝ) :
      (∫ r in Ioc 0 t, f r ∂reverseTimeVolume T) = ∫ r in Ioc 0 t, f r := by
    rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    exact inter_eq_left.mpr (Ioc_subset_Icc_self.trans fun r hr => ⟨hr.1, hr.2.trans ht.2⟩)
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hd
  have hUbar := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hd).1
  calc
    _ = ∫ r in Ioc 0 t,
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r)
          (Ubar ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩)‖ ^ 2
          ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hUbar,
        ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioo)] with r hUr hr
      have hrcc : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
      have hUr' : Ubar ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩ =
          valueCLM hΩ (u r) := by
        simpa only [affineUpperClamp_eq hrcc] using hUr hr
      rw [hUr', valueCLM_h10ShiftedPositivePart]
    _ = _ := affineUpper_setIntegral_eq _

private theorem affineUpper_initial_energy_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ} (hT : 0 < T)
    (M N : ℝ≥0) (Ubar : C(Icc 0 T, PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hzero : shiftedPositivePartValue M (Ubar ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0) :
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N 0)
      (Ubar ⟨affineUpperClamp T 0, affineUpperClamp_mem hT 0⟩)‖ ^ 2 = 0 := by
  have hc : (⟨affineUpperClamp T 0, affineUpperClamp_mem hT 0⟩ : Icc 0 T) =
      ⟨0, ⟨le_rfl, hT.le⟩⟩ := Subtype.ext (affineUpperClamp_eq ⟨le_rfl, hT.le⟩)
  rw [hc]
  simp only [reverseTimeAffineThreshold, Real.toNNReal_zero, zero_mul, add_zero,
    hzero, norm_zero]
  norm_num

private theorem affineUpper_shiftedPositivePart_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T)
    (M N : ℝ≥0) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT u g) (K : ℝ) (hK : 0 ≤ K)
    (hrate : ∀ᵐ r ∂reverseTimeVolume T,
      2 * ((g r) (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M N r)) -
        (N : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r)))) +
        0 * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M N r))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M N r))‖ ^ 2)
    (hzero : shiftedPositivePartValue M
      (reverseTimeHilbertRepresentative hΩ T hT u g hd
        ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0) :
    ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
        (reverseTimeHilbertRepresentative hΩ T hT u g hd ⟨t, ht⟩) = 0  := by
  have affineUpperClamp_continuous : Continuous (affineUpperClamp T) :=
    continuous_const.min (continuous_const.max continuous_id)
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hd
  let E : ℝ → ℝ := fun r =>
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r)
      (Ubar ⟨affineUpperClamp T r, affineUpperClamp_mem hT r⟩)‖ ^ 2
  have hEc : ContinuousOn E (Icc 0 T) :=
    ((continuous_shiftedPositivePartValue_of_isBounded hΩbounded).comp
      (Ubar.continuous.comp
        ((affineUpperClamp_continuous).subtype_mk _) |>.prodMk
          (continuous_const.add
            (continuous_real_toNNReal.mul continuous_const)))).norm.pow 2 |>.continuousOn
  have hEn : ∀ r ∈ Icc 0 T, 0 ≤ E r := fun _ _ => sq_nonneg _
  have hE0 : E 0 = 0 := affineUpper_initial_energy_zero hT M N Ubar hzero
  have hpair : Integrable (fun r => (g r) (h10ShiftedPositivePart hΩ (u r)
      (reverseTimeAffineThreshold M N r))) (reverseTimeVolume T) :=
    (integrable_reverseTimeDualPairing hΩ T (reverseTimeShiftedPositivePart hΩ T M N u) g).congr
      (by filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with r hr; rw [hr])
  have hmass : Integrable (fun r => spatialMassCLM hΩbounded
      (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M N r)))) (reverseTimeVolume T) :=
    (integrable_reverseTimeShiftedPositivePart_spatialMass
      hΩ hΩbounded T M N u).congr (by
        filter_upwards with r
        exact (spatialMassCLM_apply hΩbounded _).symm)
  have hvalue : Integrable (fun r => ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
      (reverseTimeAffineThreshold M N r))‖ ^ 2) (reverseTimeVolume T) := by
    have hm := (Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).continuousLinearMap_comp
      (valueCLM hΩ)
    exact ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm).congr (by
      filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with r hr
      rw [hr])
  have hEle : ∀ t ∈ Icc 0 T, E t ≤ (2 * K) * ∫ r in Ioc 0 t, E r := by
    intro t ht
    have hinc := reverseTimeHilbertRepresentative_shiftedPositivePart_norm_sq_increment
      hΩ hΩbounded T hT M N u g hd 0 t ⟨le_rfl, hT.le⟩ ht ht.1
    have hint := setIntegral_mono_ae_restrict (s := Ioc 0 t)
      ((hpair.sub (hmass.const_mul (N : ℝ))).const_mul 2).integrableOn
      (hvalue.const_mul (2 * K)).integrableOn
      (ae_restrict_of_ae (by
        filter_upwards [hrate] with r hr
        simpa [Pi.sub_def] using hr))
    rw [integral_const_mul, integral_const_mul] at hint
    have hval := affineUpper_value_integral hΩ hΩbounded T hT M N u g hd t ht
    have hc : (⟨affineUpperClamp T t, affineUpperClamp_mem hT t⟩ : Icc 0 T) =
        ⟨t, ht⟩ := Subtype.ext (affineUpperClamp_eq ht)
    dsimp only [E]
    have hzero' : shiftedPositivePartValue (reverseTimeAffineThreshold M N 0)
        (reverseTimeHilbertRepresentative hΩ T hT u g hd
          ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0 := by
      simpa only [reverseTimeAffineThreshold, Real.toNNReal_zero, zero_mul, add_zero]
        using hzero
    rw [hzero', norm_zero, zero_pow (by norm_num), sub_zero] at hinc
    calc
      _ = ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
          (Ubar ⟨t, ht⟩)‖ ^ 2 := congrArg (fun q =>
            ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t) (Ubar q)‖ ^ 2) hc
      _ = 2 * (∫ r in Ioc 0 t,
          (g r) (h10ShiftedPositivePart hΩ (u r) (reverseTimeAffineThreshold M N r)) -
            (N : ℝ) * spatialMassCLM hΩbounded
              (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
                (reverseTimeAffineThreshold M N r))) ∂reverseTimeVolume T) := hinc
      _ ≤ 2 * K * (∫ r in Ioc 0 t,
          ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r))‖ ^ 2 ∂reverseTimeVolume T) := hint
      _ = _ := congrArg (fun q => 2 * K * q) hval
  have hz := eq_zero_on_Icc_of_nonneg_le_mul_integral hT
    (mul_nonneg (by norm_num) hK) E hEc hEn hE0 hEle
  intro t ht
  have hc : (⟨affineUpperClamp T t, affineUpperClamp_mem hT t⟩ : Icc 0 T) =
      ⟨t, ht⟩ := Subtype.ext (affineUpperClamp_eq ht)
  have hs : ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
      (Ubar ⟨t, ht⟩)‖ ^ 2 = 0 := by
    simpa only [E, hc] using hz t ht
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)

private theorem affineUpper_ae_rate
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0)
    (M N : ℝ≥0)
    (hFbound : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      |F z.1 z.2| ≤ (N : ℝ))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g τ) (h10ShiftedPositivePart hΩ (u τ)
          (reverseTimeAffineThreshold M N τ)) -
        (N : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ)
            (reverseTimeAffineThreshold M N τ)))) +
        lam * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u τ)
          (reverseTimeAffineThreshold M N τ))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u τ)
        (reverseTimeAffineThreshold M N τ))‖ ^ 2  := by
  have reverseTimeSourceFunctional_apply_shiftedPositivePart_le_mass_of_ae_abs_le {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (f : PDE.ScalarLp Ω 2) (MF : ℝ≥0) (hf : ∀ᵐ y ∂PDE.volumeOn Ω, |f y| ≤ (MF : ℝ)) (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
      reverseTimeSourceFunctional hΩ f
        (h10ShiftedPositivePart hΩ u k) ≤
      (MF : ℝ) * spatialMassCLM hΩbounded
        (valueCLM hΩ (h10ShiftedPositivePart hΩ u k)) := by
    let w : PDE.ScalarLp Ω 2 :=
      valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
    letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
      isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
    have hwNonneg : ∀ᵐ y ∂PDE.volumeOn Ω, 0 ≤ w y := by
      filter_upwards [coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with y hy
      rw [show w y = max (valueCLM hΩ u y - (k : ℝ)) 0 by exact hy]
      exact le_max_right _ _
    have hwIntegrable : Integrable (fun y => w y) (PDE.volumeOn Ω) :=
      (Lp.memLp w).integrable (by norm_num)
    rw [reverseTimeSourceFunctional_apply, L2.inner_def,
      spatialMassCLM_apply, ← integral_neg, ← integral_const_mul]
    apply integral_mono_ae
      (L2.integrable_inner (𝕜 := ℝ) w f).neg
      (hwIntegrable.const_mul (MF : ℝ))
    filter_upwards [hf, hwNonneg] with y hyf hyw
    simp only [RCLike.inner_apply, conj_trivial]
    calc
      -(f y * w y) ≤ w y * |f y| := by
        simpa only [mul_comm, neg_mul] using
          (mul_le_mul_of_nonneg_left (neg_le_abs (f y)) hyw)
      _ ≤ w y * (MF : ℝ) := mul_le_mul_of_nonneg_left hyf hyw
      _ = (MF : ℝ) * w y := mul_comm _ _
  obtain ⟨K, hK, hGard⟩ := reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  refine ⟨K, hK, ?_⟩
  rcases hu with ⟨_, heq⟩
  filter_upwards [heq, ae_restrict_mem measurableSet_Ioo] with τ heqτ hτ
  have hτcc : τ ∈ Icc 0 (r₁ - r₀) := ⟨hτ.1.le, hτ.2.le⟩
  let w := h10ShiftedPositivePart hΩ (u τ) (reverseTimeAffineThreshold M N τ)
  let f := reverseTimeSourceSlice r₁ τ F
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded F hFSmooth τ hτcc)
  have hf : ∀ᵐ y ∂PDE.volumeOn Ω, |f y| ≤ (N : ℝ) := by
    filter_upwards [coeFn_reverseTimeSourceSlice r₁ τ F _,
      ae_restrict_mem hΩ.measurableSet] with y hyF hy
    rw [hyF]
    exact hFbound (r₁ - τ, y)
      ⟨⟨by linarith [h₀₁, hτ.2], by linarith [hτ.1]⟩, subset_closure hy⟩
  have hsource :=
    reverseTimeSourceFunctional_apply_shiftedPositivePart_le_mass_of_ae_abs_le
      hΩ hΩbounded f N hf (u τ) (reverseTimeAffineThreshold M N τ)
  have hshift :=
    reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_smoothOnNeighborhood
      r₀ r₁ h₀₁ hΩ hΩbounded a b c hcSmooth hcNonpos τ hτcc (u τ)
        (reverseTimeAffineThreshold M N τ)
  have hgard := hGard τ hτcc w
  have he := heqτ hτ w
  dsimp only [w] at he hsource hshift hgard ⊢
  linarith

/-- A reverse-time variational energy solution is bounded above by the sharp
affine envelope determined by its initial and source bounds. -/
theorem IsReverseTimeVariationalEnergySolution.reverseTimeHilbertRepresentative_le_affine
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0)
    (Minit MF : ℝ) (hMinit : 0 ≤ Minit) (hMF : 0 ≤ MF)
    (hFbound : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      |F z.1 z.2| ≤ MF)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, initial y ≤ Minit)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u g hdu ⟨τ, hτ⟩ y ≤ Minit + τ * MF := by
  let hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  let M0 : ℝ≥0 := Minit.toNNReal
  let NF : ℝ≥0 := MF.toNNReal
  have hM0 : (M0 : ℝ) = Minit := Real.coe_toNNReal _ hMinit
  have hNF : (NF : ℝ) = MF := Real.coe_toNNReal _ hMF
  obtain ⟨K, hK, hrate⟩ := affineUpper_ae_rate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos M0 NF
    (by simpa only [hNF] using hFbound) initial u g hdu hu
  let Ubar := reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT u g hdu
  have hzero : shiftedPositivePartValue M0 (Ubar ⟨0, ⟨le_rfl, hT.le⟩⟩) = 0 := by
    rw [show Ubar ⟨0, ⟨le_rfl, hT.le⟩⟩ = initial by exact hu.1]
    apply Lp.ext
    filter_upwards [coeFn_shiftedPositivePartValue M0 initial,
      Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω), hinitial] with y hs hz hi
    rw [hs, hz, hM0]
    exact max_eq_right (sub_nonpos.mpr hi)
  have hrate0 : ∀ᵐ r ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g r) (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M0 NF r)) -
        (NF : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M0 NF r)))) +
        0 * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 := by
    filter_upwards [hrate] with r hr
    have hg : 0 ≤ lam * ‖gradientCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    simpa only [zero_mul, add_zero] using (show
      2 * ((g r) (h10ShiftedPositivePart hΩ (u r)
          (reverseTimeAffineThreshold M0 NF r)) -
        (NF : ℝ) * spatialMassCLM hΩbounded
          (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M0 NF r)))) ≤
      2 * K * ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
        (reverseTimeAffineThreshold M0 NF r))‖ ^ 2 by linarith)
  intro τ hτ
  have hz := affineUpper_shiftedPositivePart_zero hΩ hΩbounded (r₁ - r₀) hT
    M0 NF u g hdu K hK hrate0 hzero τ hτ
  filter_upwards [Lp.ext_iff.mp hz,
    coeFn_shiftedPositivePartValue (reverseTimeAffineThreshold M0 NF τ) (Ubar ⟨τ, hτ⟩),
    Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω)] with y hy hs h0
  rw [hs, h0] at hy
  have hle := max_eq_right_iff.mp hy
  rw [coe_reverseTimeAffineThreshold_of_nonneg M0 NF hτ.1, hM0, hNF] at hle
  exact sub_nonpos.mp hle


local instance instReverseTimeL2VStarModuleEnvelope
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

/-- A reverse-time variational energy solution is bounded in absolute value by
the sharp affine envelope determined by its initial and source bounds. -/
theorem IsReverseTimeVariationalEnergySolution.abs_reverseTimeHilbertRepresentative_le_affine
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (Minit MF : ℝ) (hMinit : 0 ≤ Minit) (hMF : 0 ≤ MF)
    (hFbound : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → |F z.1 z.2| ≤ MF)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, |initial y| ≤ Minit)
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        |reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u g hdu ⟨τ, hτ⟩ y| ≤ Minit + τ * MF := by
  have hinitialUpper : ∀ᵐ y ∂PDE.volumeOn Ω, initial y ≤ Minit := by
    filter_upwards [hinitial] with y hy
    exact (le_abs_self (initial y)).trans hy
  have hupper := hu.reverseTimeHilbertRepresentative_le_affine
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
      hLower hcNonpos Minit MF hMinit hMF hFbound initial hinitialUpper u g hdu
  let Fneg : ℝ → PDE.Vec d → ℝ := fun r y => -F r y
  let initialNeg : PDE.ScalarLp Ω 2 := -initial
  let uneg : ReverseTimeL2V hΩ (r₁ - r₀) := (-1 : ℝ) • u
  let gneg : ReverseTimeL2VStar hΩ (r₁ - r₀) := (-1 : ℝ) • g
  let hduneg : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) uneg gneg := hdu.smul (-1)
  have hFnegSmooth : IsSmoothOnNeighborhood
      (fun z => Fneg z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
    IsSmoothOnNeighborhood.neg hFSmooth
  have hFnegBound : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → |Fneg z.1 z.2| ≤ MF := by
    intro z hz
    simpa only [Fneg, abs_neg] using hFbound z hz
  have hinitialNeg : ∀ᵐ y ∂PDE.volumeOn Ω, initialNeg y ≤ Minit := by
    filter_upwards [hinitial, Lp.coeFn_neg initial] with y hy hneg
    rw [hneg]
    exact (neg_le_abs (initial y)).trans hy
  have huneg : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c Fneg hFnegSmooth initialNeg uneg gneg hduneg := by
    exact hu.neg r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu
  have hnegUpper := huneg.reverseTimeHilbertRepresentative_le_affine
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c Fneg haSmooth hbSmooth hcSmooth
      hFnegSmooth hLower hcNonpos Minit MF hMinit hMF hFnegBound initialNeg hinitialNeg
        uneg gneg hduneg
  intro τ hτ
  have hrep := reverseTimeHilbertRepresentative_neg_eq hΩ (r₁ - r₀)
    (sub_pos.mpr h₀₁) u g hdu
  have hrepτ := congrArg
    (fun Q : C(Set.Icc 0 (r₁ - r₀), PDE.ScalarLp Ω 2) => Q ⟨τ, hτ⟩) hrep
  have hrepτ' :
      reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          uneg gneg hduneg ⟨τ, hτ⟩ =
        -reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          u g hdu ⟨τ, hτ⟩ := by
    simpa only [uneg, gneg, hduneg, ContinuousMap.neg_apply] using hrepτ
  filter_upwards [hupper τ hτ, hnegUpper τ hτ, Lp.ext_iff.mp hrepτ',
    Lp.coeFn_neg
      (reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
        u g hdu ⟨τ, hτ⟩)] with y hyUpper hyNeg hrepY hcoeNeg
  have hyLower : -(Minit + τ * MF) ≤
      reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
        u g hdu ⟨τ, hτ⟩ y := by
    have hrepScalar :
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            uneg gneg hduneg ⟨τ, hτ⟩ y =
          -reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u g hdu ⟨τ, hτ⟩ y := by
      calc
        _ = (-reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
              u g hdu ⟨τ, hτ⟩) y := hrepY
        _ = _ := by simp only [hcoeNeg, Pi.neg_apply]
    rw [hrepScalar] at hyNeg
    exact neg_le.mp hyNeg
  exact abs_le.mpr ⟨hyLower, hyUpper⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet

