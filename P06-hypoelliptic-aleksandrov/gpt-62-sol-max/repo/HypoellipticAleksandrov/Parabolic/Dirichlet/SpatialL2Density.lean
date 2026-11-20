module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.SmoothApprox
import HypoellipticAleksandrov.Analysis.InteriorSmoothDensity

/-!
# Interior-supported smooth tests are dense in spatial `L²`

On every open native-vector domain, actual bundled smooth compactly supported
test functions are dense for the restricted-volume `L²` norm.  The proof first
uses global smooth compact approximation, localizes by a compact core and a
Urysohn cutoff, and smooths once more without enlarging topological support.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
include hΩ

/-- Actual smooth compactly supported tests are dense in restricted-volume
`L²` on every open native-vector domain. -/
theorem weakTestFunction_toScalarLp_dense :
    Dense (Set.range fun φ : PDE.WeakTestFunction Ω =>
      φ.toScalarLp (2 : ℝ≥0∞)) := by
  refine (Analysis.dense_interior_smooth_toLp volume hΩ).mono ?_
  rintro _ ⟨φ, hm, hs, hc, hsub, rfl⟩
  exact ⟨⟨φ, hs, hc, hsub⟩, rfl⟩

/-- The spatial `H¹₀` value map has dense range in restricted-volume `L²`. -/
theorem valueCLM_denseRange :
    DenseRange (valueCLM hΩ) := by
  change Dense (Set.range (valueCLM hΩ))
  refine (weakTestFunction_toScalarLp_dense hΩ).mono ?_
  rintro y ⟨φ, rfl⟩
  exact ⟨smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ,
    rfl⟩

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
