module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSeparatedDistribution

/-!
# Original-time separated spacetime tests

This module packages literal products of scalar original-time tests and
spatial weak tests as Mathlib test functions on scalar parabolic cylinders.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The open-set carrier of the scalar original-time product cylinder. -/
def originalTimeOpenCylinderOpens
    {d : ℕ} (r₀ r₁ : ℝ) (Ω : PDE.VelocityRegion d) (hΩ : IsOpen Ω) :
    TopologicalSpace.Opens (TimeVelocity d) :=
  ⟨scalarParabolicOpenCylinder r₀ r₁ Ω, isOpen_Ioo.prod hΩ⟩

variable {d : ℕ} {Ω : PDE.VelocityRegion d} {r₀ r₁ : ℝ}

variable (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω)

/-- The literal product of an original-time scalar test and a spatial weak test. -/
def originalTimeSeparatedProduct

     :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => φ z.1 * ψ z.2

/-- The raw separated product has its literal pointwise value. -/
@[simp] theorem originalTimeSeparatedProduct_apply


    (z : TimeVelocity d) :
    originalTimeSeparatedProduct φ ψ z = φ z.1 * ψ z.2 :=
  rfl

/-- The canonical compact carrier of a separated original-time product. -/
def originalTimeSeparatedProductCompact

     :
    TopologicalSpace.Compacts (TimeVelocity d) :=
  ⟨_,
    (hasCompactSupport_def.mp φ.hasCompactSupport).prod
      (hasCompactSupport_def.mp ψ.hasCompactSupport)⟩

/-- The canonical compact carrier lies in the scalar product cylinder. -/
theorem originalTimeSeparatedProductCompact_subset_cylinder

     :
    (originalTimeSeparatedProductCompact φ ψ : HypoellipticAleksandrov.Parabolic.Region d) ⊆
      scalarParabolicOpenCylinder r₀ r₁ Ω := by
  intro z hz
  exact ⟨φ.tsupport_subset hz.1, ψ.tsupport_subset hz.2⟩

/-- The product as a smooth map vanishing outside its canonical compact. -/
def originalTimeSeparatedProductSupportedIn

     :
    ContDiffMapSupportedIn (TimeVelocity d) ℝ (⊤ )
      (originalTimeSeparatedProductCompact φ ψ) where
  toFun := originalTimeSeparatedProduct φ ψ
  contDiff' := (ContDiff.mul (ContDiff.comp (TestFunction.contDiff φ) contDiff_fst) (ContDiff.comp ψ.contDiff contDiff_snd))
  zero_on_compl' := by
    intro z hz
    simp only [mem_compl_iff] at hz
    rcases not_and_or.mp hz with hφ | hψ
    · simp [image_eq_zero_of_notMem_tsupport hφ]
    · simp [image_eq_zero_of_notMem_tsupport hψ]



variable (hΩ : IsOpen Ω) (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω)

/-- The separated product as a Mathlib test on the open scalar cylinder. -/
def originalTimeSeparatedProductTestFunction

     :
    TestFunction (originalTimeOpenCylinderOpens r₀ r₁ Ω hΩ) ℝ (⊤ ) :=
  TestFunction.ofSupportedIn
    (originalTimeSeparatedProductCompact_subset_cylinder φ ψ)
    (originalTimeSeparatedProductSupportedIn φ ψ)



/-- The product test has exactly the product of the factor supports. -/
theorem tsupport_originalTimeSeparatedProductTestFunction

     :
    tsupport
        (originalTimeSeparatedProductTestFunction hΩ φ ψ :
          HypoellipticAleksandrov.Parabolic.ScalarField d) =
      tsupport (φ : ℝ → ℝ) ×ˢ tsupport (ψ : PDE.ScalarField d) := by
  have hsupport : Function.support (fun z : TimeVelocity d => φ z.1 * ψ z.2) =
      Function.support (φ : ℝ → ℝ) ×ˢ Function.support (ψ : PDE.ScalarField d) := by
    ext z
    simp [Function.mem_support]
  change closure (Function.support (fun z : TimeVelocity d => φ z.1 * ψ z.2)) = _
  rw [hsupport, closure_prod_eq]
  rfl





end HypoellipticAleksandrov.Parabolic.Dirichlet
