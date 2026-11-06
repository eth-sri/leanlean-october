module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/

@[expose] public section

namespace PDE

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on project vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Scalar functions of the velocity variable. -/
abbrev ScalarField (d : ℕ) := Vec d → ℝ
/-- Velocity-dependent vector fields. -/
abbrev VectorField (d : ℕ) := Vec d → Vec d
/-- Time-dependent scalar fields. -/
abbrev TimeScalarField (d : ℕ) := ℝ → Vec d → ℝ
/-- Time-dependent vector fields. -/
abbrev TimeVectorField (d : ℕ) := ℝ → Vec d → Vec d
/-- Regions in velocity space. -/
abbrev VelocityRegion (d : ℕ) := Set (Vec d)

end PDE
