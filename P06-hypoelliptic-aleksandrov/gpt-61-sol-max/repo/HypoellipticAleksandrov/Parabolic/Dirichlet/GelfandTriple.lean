module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Density
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The spatial Gelfand triple

This module realizes the dual side of the spatial Gelfand triple
`H¹₀(Ω) → L²(Ω) → (H¹₀(Ω))^*`.  It uses the continuous, injective spatial
value map and its dense-range theorem, together with the real Hilbert-space pairing.

No coercivity, time-dependent, Bochner, or PDE assertion is made here.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

/-- The `H⁻¹` carrier dual to the spatial Hilbert realization of `H¹₀(Ω)`. -/
abbrev H10HilbertGraphDual (hΩ : IsOpen Ω) : Type _ :=
  StrongDual ℝ (H10HilbertGraph hΩ)

variable (hΩ : IsOpen Ω)

/-- The canonical continuous pivot embedding from spatial `L²` into the dual
of the spatial Hilbert realization of `H¹₀`. -/
def scalarLpToH10HilbertGraphDual
     :
    PDE.ScalarLp Ω (2 ) →L[ℝ] H10HilbertGraphDual hΩ :=
  ContinuousLinearMap.toSesqForm (valueCLM hΩ)

variable (h : PDE.ScalarLp Ω (2 ))

@[simp]
theorem scalarLpToH10HilbertGraphDual_apply

    (v : H10HilbertGraph hΩ) :
    scalarLpToH10HilbertGraphDual hΩ h v = inner ℝ (valueCLM hΩ v) h := (id (real_inner_comm ((valueCLM hΩ) v) h))

/-- The pivot embedding is bounded by the operator norm of the spatial value map. -/
theorem norm_scalarLpToH10HilbertGraphDual_apply_le
      :
    ‖scalarLpToH10HilbertGraphDual hΩ h‖ ≤ ‖valueCLM hΩ‖ * ‖h‖ := ContinuousLinearMap.toSesqForm_apply_norm_le

/-- Dense range of the spatial value map makes the pivot embedding injective. -/
theorem scalarLpToH10HilbertGraphDual_injective
     :
    Function.Injective (scalarLpToH10HilbertGraphDual hΩ) := (fun ⦃h k⦄ hhk =>
  Dense.eq_of_inner_right ℝ (valueCLM_denseRange hΩ) fun x hx =>
    Exists.casesOn hx fun v h_1 =>
      h_1 ▸
        id
          (Eq.mp
            (congr (congrArg Eq (scalarLpToH10HilbertGraphDual_apply hΩ h v))
              (scalarLpToH10HilbertGraphDual_apply hΩ k v))
            (congrArg (fun ℓ => ℓ v) hhk)))

end HypoellipticAleksandrov.Parabolic.Dirichlet
