module

public import NearlyMinimax.IncrementKernelMeasurability
public import NearlyMinimax.DyadicPilotRows


@[expose] public section

/-! Joint Borel measurability of the actual centered polynomial pilot,
obtained from its exact finite factorial-kernel expansion. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem centeredKernelExpansion_field_measurable {Ω W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] {n p R : ℕ}
    {H : W → (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ => Fin p → ℝ) ℝ}
    (hH : ∀ r, Measurable (fun w => H w r))
    {X : Fin n → Ω → Fin p → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (fun t : Ω × W => LiftL2.centeredKernelExpansion 0 (H t.2) X t.1) := by
  classical
  unfold LiftL2.centeredKernelExpansion LiftL2.kernelStatistic LiftL2.kernelSum
  simp
  apply Finset.measurable_sum
  intro r _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  have hmH : Measurable (fun t : Ω × W => H t.2 r) := (hH r).comp measurable_snd
  exact continuous_eval.measurable.comp (hmH.prodMk (by fun_prop))

theorem dyadicPolynomialPilot_centered_field_measurable {d : ℕ} {C : ModelConstants d}
    [Nonempty (AnchoredIndex d C.order)] {θ : RegressionParameter d} (hθ : Admissible C θ)
    (n j : ℕ) (y : ℝ) {m : ℕ}
    {row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ}
    (hrow : Measurable row) (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicPolynomialPilot n j t.2.1 y m (row t.2) t.1 -
      incrementFinScalar C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m (row t.2)
          (dyadicIncrementRawMean θ j t.2.1)) := by
  let R := m + anchoredDimension d C.order + 1
  let H w (r : Fin R) :=
    dyadicIncrementKernel θ j w.1 y m (row w) (r.val + 1)
  have hH (r : Fin R)  :=
    dyadicIncrementKernel_field_measurable hθ j y m (r.val + 1) hrow
  have hX i : Measurable (fun z : Fin n → Observation d =>
      incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j) :=
    ((incrementGlobalVector_measurable j).comp (measurable_pi_apply i)).sub measurable_const
  have h := centeredKernelExpansion_field_measurable hH hX
  have heq : (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      LiftL2.centeredKernelExpansion 0 (H t.2)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) t.1) =
      (fun t => dyadicPolynomialPilot n j t.2.1 y m (row t.2) t.1 -
        incrementFinScalar C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m (row t.2)
            (dyadicIncrementRawMean θ j t.2.1)) := by
    funext t
    solve_by_elim [dyadicPolynomialPilot_centered_global]
  rwa [heq] at h

end NearlyMinimax
