module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeBochnerEnergy

/-!
# Canonical reverse-time Galerkin Bochner classes

This module packages the selected raw reverse-time Galerkin curves into their
canonical `L²(V)` quotient classes.  It derives an explicit uniform squared
bound and its square-root radius, without making compactness, trace, or weak
solution assertions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

local notation "primalRaw" => reverseTimeGalerkinPrimalRaw P

local notation "primalM" => reverseTimeGalerkinPrimalM P

local notation "primalK" => reverseTimeGalerkinPrimalK P

/-- The canonical quotient-valued representative of the selected raw
reverse-time Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimal
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ReverseTimeL2V P.hΩ (r₁ - r₀) :=
  reverseTimeL2OfContinuousOn (r₁ - r₀)
    (primalRaw N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw P N initial)

local notation "primalCurve" => reverseTimeGalerkinPrimal P

/-- The uniform value-energy bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalValueBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  gronwallBound (‖initial‖ ^ 2)
    (2 * primalK + 1)
    (primalM ^ 2)
    (r₁ - r₀)

local notation "primalValueBound" => reverseTimeGalerkinPrimalValueBound P

/-- The uniform gradient-energy bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalGradientBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  ‖initial‖ ^ 2 +
    (2 * primalK + 1) * (r₁ - r₀) *
      primalValueBound initial +
    (primalM ^ 2) * (r₁ - r₀)

local notation "primalGradientBound" => reverseTimeGalerkinPrimalGradientBound P

/-- The uniform squared `L²(V)` bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalNormSqBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  (r₁ - r₀) *
      primalValueBound initial +
    primalGradientBound initial / lam

local notation "primalNormBound" => reverseTimeGalerkinPrimalNormSqBound P

/-- The explicit uniform radius associated with the squared Bochner bound. -/
noncomputable def reverseTimeGalerkinPrimalRadius
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  Real.sqrt
    (primalNormBound initial)

section
variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))

/-- The canonical quotient representative agrees almost everywhere with its
selected raw Galerkin curve. -/
theorem ae_reverseTimeGalerkinPrimal_eq_raw :
    primalCurve N initial =ᵐ[
        reverseTimeVolume (r₁ - r₀)]
      primalRaw N initial := by
  exact coeFn_reverseTimeL2OfContinuousOn (r₁ - r₀)
    (primalRaw N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw P N initial)

private theorem reverseTimeGalerkinPrimal_value_energy_le_bound
    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    ‖valueCLM P.hΩ
      (primalRaw N initial t)‖ ^ 2 ≤
      primalValueBound initial := by
  have hK : 0 ≤ 2 * primalK + 1 := by
    nlinarith [reverseTimeGalerkinPrimalK_nonneg P]
  calc
    ‖valueCLM P.hΩ
        (primalRaw N initial t)‖ ^ 2 ≤
        gronwallBound (‖initial‖ ^ 2)
          (2 * primalK + 1)
          (primalM ^ 2) t :=
      reverseTimeGalerkinPrimal_value_energy P N initial t ht
    _ ≤ gronwallBound (‖initial‖ ^ 2)
          (2 * primalK + 1)
          (primalM ^ 2) (r₁ - r₀) :=
      gronwallBound_mono (sq_nonneg ‖initial‖) (sq_nonneg _ ) hK ht.2
    _ = primalValueBound initial := rfl

private theorem reverseTimeGalerkinPrimal_gradient_energy_le_bound :
    lam * ∫ τ in Set.Ioc 0 (r₁ - r₀),
      ‖gradientCLM P.hΩ
        (primalRaw N initial τ)‖ ^ 2 ≤
      primalGradientBound initial := by
  simpa only [reverseTimeGalerkinPrimalGradientBound,
    reverseTimeGalerkinPrimalValueBound] using
    (reverseTimeGalerkinPrimal_gradient_energy P N initial (r₁ - r₀)
      ⟨sub_nonneg.mpr P.h₀₁.le, le_rfl⟩)

end

section
variable (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))

/-- The canonical reverse-time Galerkin class satisfies the explicit uniform
squared Bochner bound. -/
theorem norm_sq_reverseTimeGalerkinPrimal_le (N : ℕ) :
    ‖primalCurve N initial‖ ^ 2 ≤
      primalNormBound initial := by
  have hT : 0 < r₁ - r₀ := sub_pos.mpr P.h₀₁
  obtain ⟨W, hWraw, hWbound⟩ := exists_reverseTimeL2V_of_continuousOn_energy P.hΩ hT P.hlam
    (primalRaw N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw P N initial)
    (reverseTimeGalerkinPrimal_value_energy_le_bound P N initial)
    (reverseTimeGalerkinPrimal_gradient_energy_le_bound P N initial)
  have hW : W = primalCurve N initial := by
    apply MeasureTheory.Lp.ext
    exact hWraw.trans
      (ae_reverseTimeGalerkinPrimal_eq_raw P N initial).symm
  calc
    ‖primalCurve N initial‖ ^ 2 = ‖W‖ ^ 2 := by
      rw [hW]
    _ ≤ (r₁ - r₀) *
          primalValueBound initial +
        primalGradientBound initial / lam := hWbound
    _ = primalNormBound initial := rfl

private theorem reverseTimeGalerkinPrimalNormSqBound_nonneg :
    0 ≤ primalNormBound initial := by
  exact (sq_nonneg ‖primalCurve 0 initial‖).trans
    (norm_sq_reverseTimeGalerkinPrimal_le P initial 0)

/-- The canonical reverse-time Galerkin class lies in its explicit uniform
Bochner radius. -/
theorem norm_reverseTimeGalerkinPrimal_le_radius (N : ℕ) :
    ‖primalCurve N initial‖ ≤
      reverseTimeGalerkinPrimalRadius P initial := by
  apply (Real.le_sqrt (norm_nonneg _)
    (reverseTimeGalerkinPrimalNormSqBound_nonneg P initial)).mpr
  simpa only [reverseTimeGalerkinPrimalRadius] using
    (norm_sq_reverseTimeGalerkinPrimal_le P initial N)

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
