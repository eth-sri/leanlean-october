module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedSpacetimeCompactSupport
public import HypoellipticAleksandrov.Parabolic.Derivatives
import Aesop



/-!
# Sampled time factors

This module packages a fixed spatial sample of a spacetime test as a scalar time test.
-/

 public section

open Set Topology




namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

variable (y : PDE.Vec d)

private theorem isClosedEmbedding_fixedSpatial   :
    IsClosedEmbedding (fun τ : ℝ => ((τ, y) )) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_id.prodMk continuous_const) (fun x z h => congrArg Prod.fst h) ?_
  intro s hs
  have himage : (fun τ : ℝ => ((τ, y) )) '' s =
      s ×ˢ ({y} : PDE.VelocityRegion d) := by
    ext z
    simp only [mem_image, mem_prod, mem_singleton_iff]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨hτ, rfl⟩
    · aesop
  rw [himage]
  exact hs.prod isClosed_singleton

private theorem hasCompactSupport_fixedSpatial
      (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : HasCompactSupport f) :
    HasCompactSupport (fun τ  => f (τ, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isClosedEmbedding_fixedSpatial y).isCompact_preimage hf) ?_
  intro τ hτ
  exact subset_tsupport f hτ

/-- A sampled time slice is an original-time scalar test, with its expected derivative and
support in the compact time projection. -/
theorem exists_sampledTimeFactor
     {τ₁ τ₂ : ℝ} {O : PDE.VelocityRegion d} {hO : IsOpen O}
    (φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ ))
    (y : PDE.Vec d) :
    ∃ η : OriginalTimeScalarTest τ₁ τ₂,
      (∀ τ, η τ = φ (τ, y)) ∧
      (∀ τ, η.deriv τ = timeDerivative φ (τ, y)) ∧
      tsupport (η : ℝ → ℝ) ⊆
        (spacetimeTestTimeSupportCompact φ : Set ℝ) := by

  let sharedTerm_ad4e8426e9 := ((fun r : ℝ => φ (r, y)))
  let η : OriginalTimeScalarTest τ₁ τ₂ :=
    { toFun := sharedTerm_ad4e8426e9
      contDiff' := φ.contDiff.comp (contDiff_id.prodMk contDiff_const)
      hasCompactSupport' := hasCompactSupport_fixedSpatial y φ φ.hasCompactSupport
      tsupport_subset' := by
        intro τ hτ



        exact (φ.tsupport_subset (closure_minimal (by
            intro r hr
            exact subset_tsupport φ hr) ((isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const)) hτ)).1 }
  refine ⟨η, fun _ => rfl, ?_, ?_⟩
  · intro τ
    rw [OriginalTimeScalarTest.deriv_apply]
    change deriv sharedTerm_ad4e8426e9 τ =
      fderiv ℝ (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (τ, y) (1, 0)
    have hcomp := (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp τ
      (hasFDerivAt_id τ |>.prodMk (hasFDerivAt_const (x := τ) y))
    rw [_root_.deriv]
    have hfderiv : fderiv ℝ sharedTerm_ad4e8426e9 τ =
        (fderiv ℝ (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (τ, y)).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod 0) := by
      simpa only [Function.comp_def, id_eq] using hcomp.fderiv
    rw [hfderiv]
    rfl
  · intro τ hτ
    change τ ∈ Prod.fst '' tsupport (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)


    exact ⟨(τ, y), closure_minimal (by
        intro r hr
        exact subset_tsupport φ hr) ((isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const)) hτ, rfl⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
