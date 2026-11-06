module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Positive-part locality of the reverse-time spatial form

This file records the fixed-time locality identity obtained by testing the
literal reverse-time spatial form against the positive part of its first
argument.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal


namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (u : H10HilbertGraph hΩ)

private theorem h10PositivePart_gradientCoord
     (k : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
    (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) k
      (gradientCLM hΩ (h10PositivePart hΩ u))) y =
      {z | 0 < valueCLM hΩ u z}.indicator
        (fun z => (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) k
          (gradientCLM hΩ u)) z) y := by
  filter_upwards [gradientCLM_h10PositivePart hΩ u,
    PDE.coeFn_hilbertVectorLpCoord Ω _ k (gradientCLM hΩ u),
    PDE.coeFn_hilbertVectorLpCoord Ω _ k
      (gradientCLM hΩ (h10PositivePart hΩ u))] with y hg hu hp
  calc
    _ = (gradientCLM hΩ _ y).ofLp k := hp
    _ = ({z | 0 < valueCLM hΩ u z}.indicator
        (gradientCLM hΩ u) y).ofLp k := congrArg (fun q => q.ofLp k) hg
    _ = _ := by
      by_cases hy : 0 < valueCLM hΩ u y
      · have hleft :
            {z | 0 < valueCLM hΩ u z}.indicator
                (fun z => gradientCLM hΩ u z) y = gradientCLM hΩ u y :=
          Set.indicator_of_mem (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _
        simp_all
      simp_all

private theorem reverseTimePrincipal_positivePart_eq
     :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (h10PositivePart hΩ u))) y) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
              (gradientCLM hΩ (h10PositivePart hΩ u))) y := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  have hj := h10PositivePart_gradientCoord hΩ u j
  have hi := h10PositivePart_gradientCoord hΩ u i
  filter_upwards [hj, hi] with y hpj hpi
  by_cases hy : 0 < valueCLM hΩ u y
  · have hpj' := hpj.trans (Set.indicator_of_mem
        (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
    simp_all
  simp_all

private theorem reverseTimeDrift_positivePart_eq
     :
      (∑ j : Fin d, ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)) y *
          valueCLM hΩ (h10PositivePart hΩ u) y) =
        ∑ j : Fin d, ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            valueCLM hΩ (h10PositivePart hΩ u) y := by
  have hvalue : ∀ᵐ y ∂PDE.volumeOn Ω,
      valueCLM hΩ (h10PositivePart hΩ u) y = max (valueCLM hΩ u y) 0 := by
    rw [valueCLM_h10PositivePart]
    exact Lp.coeFn_posPart _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  have hj := h10PositivePart_gradientCoord hΩ u j
  filter_upwards [hvalue, hj] with y hv hpj
  by_cases hy : 0 < valueCLM hΩ u y
  · simp_all
  simp_all

private theorem reverseTimeScalar_positivePart_eq
     (c : ℝ → PDE.Vec d → ℝ) (u : H10HilbertGraph hΩ) :
      (∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10PositivePart hΩ u) y) =
        ∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ (h10PositivePart hΩ u) y *
          valueCLM hΩ (h10PositivePart hΩ u) y := by
  have hvalue : ∀ᵐ y ∂PDE.volumeOn Ω,
      valueCLM hΩ (h10PositivePart hΩ u) y = max (valueCLM hΩ u y) 0 := by
    rw [valueCLM_h10PositivePart]
    exact Lp.coeFn_posPart _
  apply integral_congr_ae
  filter_upwards [hvalue] with y hv
  by_cases hy : 0 < valueCLM hΩ u y
  · have hv' : valueCLM hΩ (h10PositivePart hΩ u) y = valueCLM hΩ u y :=
      hv.trans (max_eq_left (le_of_lt hy))
    simp_all
  simp_all

/-- Testing the reverse-time spatial form against `u₊` only sees `u₊` in
the first argument as well. -/
theorem reverseTimeSpatialForm_apply_positivePart_eq
     (c : ℝ → PDE.Vec d → ℝ)
    (u : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10PositivePart hΩ u) =
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10PositivePart hΩ u) (h10PositivePart hΩ u) := by
  rw [reverseTimeSpatialForm_apply, reverseTimePrincipal_positivePart_eq]
  apply congrArg₂ _
  · exact congrArg _
      (reverseTimeDrift_positivePart_eq hΩ r₁ τ a b u)
  · exact reverseTimeScalar_positivePart_eq hΩ r₁ τ c u
end HypoellipticAleksandrov.Parabolic.Dirichlet
