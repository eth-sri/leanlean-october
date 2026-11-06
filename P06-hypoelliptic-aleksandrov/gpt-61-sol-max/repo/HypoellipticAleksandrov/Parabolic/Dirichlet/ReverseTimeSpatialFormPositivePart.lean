module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Positive-part locality of the reverse-time spatial form

This file records the fixed-time locality identity obtained by testing the
literal reverse-time spatial form against the positive part of its first
argument.
-/

 public section

open MeasureTheory Set
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private theorem h10PositivePart_gradientCoord

    (u : H10HilbertGraph hΩ) (k : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
    (PDE.hilbertVectorLpCoord Ω (2 ) k
      (gradientCLM hΩ (h10PositivePart hΩ u))) y =
      {z | 0 < valueCLM hΩ u z}.indicator
        (fun z => (PDE.hilbertVectorLpCoord Ω (2 ) k
          (gradientCLM hΩ u)) z) y := by
  let sharedTerm_652ec727e1 := ({z : PDE.Vec d | 0 < valueCLM hΩ u z})
  filter_upwards [gradientCLM_h10PositivePart hΩ u,
    PDE.coeFn_hilbertVectorLpCoord Ω _ k (gradientCLM hΩ u),
    PDE.coeFn_hilbertVectorLpCoord Ω _ k
      (gradientCLM hΩ (h10PositivePart hΩ u))] with y hg hu hp
  calc
    _ = (gradientCLM hΩ (h10PositivePart hΩ u) y).ofLp k := hp
    _ = (sharedTerm_652ec727e1.indicator
        (gradientCLM hΩ u) y).ofLp k := congrArg (fun q => q.ofLp k) hg
    _ = _ := by
      let sharedTerm_dd2780e39e := ((PDE.hilbertVectorLpCoord Ω (2 ) k (gradientCLM hΩ u)))
      by_cases hy : 0 < valueCLM hΩ u y
      · have hleft :
            sharedTerm_652ec727e1.indicator
                (fun z => gradientCLM hΩ u z) y = gradientCLM hΩ u y :=
          Set.indicator_of_mem (s := sharedTerm_652ec727e1) hy _
        have hright :
            sharedTerm_652ec727e1.indicator
                (fun z => sharedTerm_dd2780e39e z) y =
              sharedTerm_dd2780e39e y :=
          Set.indicator_of_mem (s := sharedTerm_652ec727e1) hy _
        rw [hleft, hright]
        exact hu.symm
      · have hleft :
            sharedTerm_652ec727e1.indicator
                (fun z => gradientCLM hΩ u z) y = 0 :=
          Set.indicator_of_notMem
            (s := sharedTerm_652ec727e1) hy _
        have hright :
            sharedTerm_652ec727e1.indicator
                (fun z => sharedTerm_dd2780e39e z) y = 0 :=
          Set.indicator_of_notMem
            (s := sharedTerm_652ec727e1) hy _
        rw [hleft, hright]
        rfl

variable (r₁ τ : ℝ)

variable (a : CoefficientField d)

private theorem reverseTimePrincipal_positivePart_eq

      (u : H10HilbertGraph hΩ) :
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω (2 ) i
            (gradientCLM hΩ (h10PositivePart hΩ u))) y) =
        ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          a (r₁ - τ) y i j *
            (PDE.hilbertVectorLpCoord Ω (2 ) j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            (PDE.hilbertVectorLpCoord Ω (2 ) i
              (gradientCLM hΩ (h10PositivePart hΩ u))) y := by
  let sharedTerm_f7d7dfe5f3 := ({z : PDE.Vec d | 0 < valueCLM hΩ u z})
  let sharedTerm_a2ca0a6c0b := ((gradientCLM hΩ (h10PositivePart hΩ u)))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae


  filter_upwards [(h10PositivePart_gradientCoord hΩ u j), (h10PositivePart_gradientCoord hΩ u i)] with y hpj hpi
  by_cases hy : 0 < valueCLM hΩ u y
  · have hpj' := hpj.trans (Set.indicator_of_mem
        (s := sharedTerm_f7d7dfe5f3) hy _)
    have hpi' := hpi.trans (Set.indicator_of_mem
        (s := sharedTerm_f7d7dfe5f3) hy _)
    calc
      _ = a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y *
          (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ u)) y :=
        congrArg (fun q  => a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y * q) hpi'
      _ = a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j
            sharedTerm_a2ca0a6c0b) y *
          (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ u)) y :=
        congrArg (fun q  => a (r₁ - τ) y i j * q *
          (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ u)) y) hpj'.symm
      _ = _ := congrArg (fun q  => a (r₁ - τ) y i j *
        (PDE.hilbertVectorLpCoord Ω (2 ) j
          sharedTerm_a2ca0a6c0b) y * q) hpi'.symm
  ·
    have hpi' := hpi.trans (Set.indicator_of_notMem
        (s := sharedTerm_f7d7dfe5f3) hy _)
    calc
      _ = a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y * 0 :=
        congrArg (fun q  => a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y * q) hpi'
      _ = 0 := mul_zero _
      _ = a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j
            sharedTerm_a2ca0a6c0b) y * 0 := (mul_zero _).symm
      _ = _ := congrArg (fun q  => a (r₁ - τ) y i j *
        (PDE.hilbertVectorLpCoord Ω (2 ) j
          sharedTerm_a2ca0a6c0b) y * q) hpi'.symm

private theorem reverseTimeDrift_positivePart_eq


    (b : PDE.TimeVectorField d) (u : H10HilbertGraph hΩ) :
      (∑ j : Fin d, ∫ y in Ω,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y *
          valueCLM hΩ (h10PositivePart hΩ u) y) =
        ∑ j : Fin d, ∫ y in Ω,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            (PDE.hilbertVectorLpCoord Ω (2 ) j
              (gradientCLM hΩ (h10PositivePart hΩ u))) y *
            valueCLM hΩ (h10PositivePart hΩ u) y := by

  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  have hj := h10PositivePart_gradientCoord hΩ u j
  filter_upwards [(show ∀ᵐ y ∂PDE.volumeOn Ω,
      valueCLM hΩ (h10PositivePart hΩ u) y = max (valueCLM hΩ u y) 0 by
      rw [valueCLM_h10PositivePart]
      exact Lp.coeFn_posPart (valueCLM hΩ u)), hj] with y hv hpj
  by_cases hy : 0 < valueCLM hΩ u y
  · have hpj' := hpj.trans (Set.indicator_of_mem
        (s := {z : PDE.Vec d | 0 < valueCLM hΩ u z}) hy _)
    exact congrArg (fun q  => reverseTimeDivergenceDrift r₁ a b τ y j * q *
      valueCLM hΩ (h10PositivePart hΩ u) y) hpj'.symm
  · have hvzero  :=
      hv.trans (max_eq_right (le_of_not_gt hy))
    calc
      _ = reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y * 0 :=
        congrArg (fun q  => reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)) y * q) hvzero
      _ = 0 := mul_zero _
      _ = reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ (h10PositivePart hΩ u))) y * 0 := (mul_zero _).symm
      _ = _ := congrArg (fun q  => reverseTimeDivergenceDrift r₁ a b τ y j *
        (PDE.hilbertVectorLpCoord Ω (2 ) j
          (gradientCLM hΩ (h10PositivePart hΩ u))) y * q) hvzero.symm

private theorem reverseTimeScalar_positivePart_eq

     (c : PDE.TimeScalarField d) (u : H10HilbertGraph hΩ) :
      (∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
        valueCLM hΩ u y * valueCLM hΩ (h10PositivePart hΩ u) y) =
        ∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ (h10PositivePart hΩ u) y *
          valueCLM hΩ (h10PositivePart hΩ u) y := by

  apply integral_congr_ae
  filter_upwards [(show ∀ᵐ y ∂PDE.volumeOn Ω,
      valueCLM hΩ (h10PositivePart hΩ u) y = max (valueCLM hΩ u y) 0 by
      rw [valueCLM_h10PositivePart]
      exact Lp.coeFn_posPart (valueCLM hΩ u))] with y hv
  by_cases hy : 0 < valueCLM hΩ u y
  · have hv'  :=
      hv.trans (max_eq_left (le_of_lt hy))
    exact congrArg (fun q  => reverseTimeScalarCoefficient r₁ c τ y * q *
      valueCLM hΩ (h10PositivePart hΩ u) y) hv'.symm
  · have hvzero  :=
      hv.trans (max_eq_right (le_of_not_gt hy))
    calc
      _ = reverseTimeScalarCoefficient r₁ c τ y * valueCLM hΩ u y * 0 :=
        congrArg (fun q  => reverseTimeScalarCoefficient r₁ c τ y *
          valueCLM hΩ u y * q) hvzero
      _ = 0 := mul_zero _
      _ = reverseTimeScalarCoefficient r₁ c τ y * 0 * 0 := by ring
      _ = _ := congrArg (fun q  => reverseTimeScalarCoefficient r₁ c τ y * q * q)
        hvzero.symm

/-- Testing the reverse-time spatial form against `u₊` only sees `u₊` in
the first argument as well. -/
theorem reverseTimeSpatialForm_apply_positivePart_eq
      (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (u : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10PositivePart hΩ u) =
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10PositivePart hΩ u) (h10PositivePart hΩ u) := by
  rw [reverseTimeSpatialForm_apply, reverseTimeSpatialForm_apply]
  rw [reverseTimePrincipal_positivePart_eq hΩ r₁ τ a u]
  apply congrArg₂ (fun x y : ℝ => x - y)
  · solve_by_elim (maxDepth := 4) [reverseTimeDrift_positivePart_eq]
  · exact reverseTimeScalar_positivePart_eq hΩ r₁ τ c u
end HypoellipticAleksandrov.Parabolic.Dirichlet
