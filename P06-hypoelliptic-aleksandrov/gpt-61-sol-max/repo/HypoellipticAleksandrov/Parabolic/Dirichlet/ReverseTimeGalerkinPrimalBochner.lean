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

open Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder

variable {d : ℕ} {Ω : PDE.VelocityRegion d}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The canonical quotient-valued representative of the selected raw
reverse-time Galerkin curve. -/
def reverseTimeGalerkinPrimal
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 )) :
    ReverseTimeL2V hΩ (r₁ - r₀) :=
  reverseTimeL2OfContinuousOn (r₁ - r₀)
    _
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)

variable (initial : PDE.ScalarLp Ω (2 ))

/-- The uniform value-energy bound for every selected Galerkin curve. -/
def reverseTimeGalerkinPrimalValueBound
     : ℝ :=
  gronwallBound (‖initial‖ ^ 2)
    (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
    (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2)
    (r₁ - r₀)

/-- The uniform gradient-energy bound for every selected Galerkin curve. -/
def reverseTimeGalerkinPrimalGradientBound
     : ℝ :=
  ‖initial‖ ^ 2 +
    (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1) * (r₁ - r₀) *
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
    (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) * (r₁ - r₀)

/-- The uniform squared `L²(V)` bound for every selected Galerkin curve. -/
def reverseTimeGalerkinPrimalNormSqBound
     : ℝ :=
  (r₁ - r₀) *
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
    reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial / lam

/-- The explicit uniform radius associated with the squared Bochner bound. -/
def reverseTimeGalerkinPrimalRadius
     : ℝ :=
  Real.sqrt
    (reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)

variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 ))

/-- The canonical quotient representative agrees almost everywhere with its
selected raw Galerkin curve. -/
theorem ae_reverseTimeGalerkinPrimal_eq_raw
     :
    reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial =ᵐ[
        reverseTimeVolume (r₁ - r₀)]
      reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := coeFn_reverseTimeL2OfContinuousOn (r₁ - r₀)
    _
    _

private theorem reverseTimeGalerkinPrimal_value_energy_le_bound

    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    ‖valueCLM hΩ
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  let sharedTerm_2b3726d9f2 := ((2 *
      reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower
        hcNonpos +
    1))
  let sharedTerm_b296d887ac := (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos)

  calc
    ‖valueCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
        gronwallBound (‖initial‖ ^ 2)
          sharedTerm_2b3726d9f2
          (sharedTerm_b296d887ac ^ 2) t :=
      reverseTimeGalerkinPrimal_value_energy r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t ht
    _ ≤ gronwallBound (‖initial‖ ^ 2)
          sharedTerm_2b3726d9f2
          (sharedTerm_b296d887ac ^ 2) (r₁ - r₀) :=
      gronwallBound_mono (sq_nonneg ‖initial‖) (sq_nonneg _ ) (by
          nlinarith [reverseTimeGalerkinPrimalK_nonneg r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
            a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos]) ht.2
    _ = reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := rfl

private theorem reverseTimeGalerkinPrimal_gradient_energy_le_bound
     :
    lam * ∫ τ in Set.Ioc 0 (r₁ - r₀),
      ‖gradientCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)‖ ^ 2 ≤
      reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := (id
  (reverseTimeGalerkinPrimal_gradient_energy r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hcNonpos N initial (r₁ - r₀) ⟨sub_nonneg.mpr (LT.lt.le h₀₁), le_rfl⟩))

variable (initial : PDE.ScalarLp Ω (2 ))

/-- The canonical reverse-time Galerkin class satisfies the explicit uniform
squared Bochner bound. -/
theorem norm_sq_reverseTimeGalerkinPrimal_le
     (N : ℕ) :
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ^ 2 ≤
      reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := (Exists.casesOn
  (exists_reverseTimeL2V_of_continuousOn_energy hΩ (sub_pos.mpr h₀₁) hlam
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower
      hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth
      hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimal_value_energy_le_bound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth
      hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimal_gradient_energy_le_bound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
      hcSmooth hFSmooth hLower hcNonpos N initial))
  fun W h =>
  And.casesOn h fun hWraw hWbound =>
    Trans.trans
      (Trans.trans
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
                        hLower hcNonpos N initial‖ ^
                    2 =
                  ‖_a‖ ^ 2)
              (MeasureTheory.Lp.ext
                (Filter.EventuallyEq.trans hWraw
                  (Filter.EventuallyEq.symm
                    (ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
                      hcSmooth hFSmooth hLower hcNonpos N initial))))))
          (Eq.refl
            (‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
                  hLower hcNonpos N initial‖ ^
              2)))
        hWbound)
      rfl)

private theorem reverseTimeGalerkinPrimalNormSqBound_nonneg
     :
    0 ≤ reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := (sq_nonneg ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos 0 initial‖).trans
    (norm_sq_reverseTimeGalerkinPrimal_le r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial 0)

/-- The canonical reverse-time Galerkin class lies in its explicit uniform
Bochner radius. -/
theorem norm_reverseTimeGalerkinPrimal_le_radius
     (N : ℕ) :
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ≤
      reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  apply (Real.le_sqrt (norm_nonneg _)
    (reverseTimeGalerkinPrimalNormSqBound_nonneg r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)).mpr
  exact (norm_sq_reverseTimeGalerkinPrimal_le r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial N)

end HypoellipticAleksandrov.Parabolic.Dirichlet
