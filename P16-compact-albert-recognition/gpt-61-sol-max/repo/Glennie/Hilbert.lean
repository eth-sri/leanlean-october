/- The positive native trace form as a real Hilbert space.
Diagonalizing a multiplication operator is not yet a Jordan-frame theorem. -/
module
public import Glennie.Native.CubicIdentity
public import Glennie.Automorphism
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
namespace Glennie
noncomputable section

def Albert.coordinateLinearEquiv : Albert ≃ₗ[ℝ] Albert.Coordinates where
  __ := Albert.coordinateAddEquiv
  map_smul' _ _ := rfl

instance : FiniteDimensional ℝ Albert := by
  letI : FiniteDimensional ℝ Albert.Coordinates := Module.Finite.prod
  exact Albert.coordinateLinearEquiv.symm.finiteDimensional

theorem albert_finrank : Module.finrank ℝ Albert = 27 := by
  rw [Albert.coordinateLinearEquiv.finrank_eq]
  simp [Albert.Coordinates, Octonion, Quaternion.finrank_eq_four]

instance : Inner ℝ Albert := ⟨Glennie.inner⟩

@[instance_reducible] def nativeInnerCore : InnerProductSpace.Core ℝ Albert where
  toInner := inferInstance
  conj_inner_symm x y := by
    change inner y x = inner x y
    exact inner_comm y x
  re_inner_nonneg := inner_self_nonneg
  definite x := (inner_self_eq_zero x).mp
  add_left := inner_add_left
  smul_left x y r := by
    change inner (r • x) y = r * inner x y
    exact inner_smul_left r x y

instance : NormedAddCommGroup Albert := nativeInnerCore.toNormedAddCommGroup

instance : InnerProductSpace ℝ Albert :=
  InnerProductSpace.ofCore nativeInnerCore.toCore




theorem native_norm_sq (x : Albert) : ‖x‖ ^ 2 = inner x x := real_inner_self_eq_norm_sq x |>.symm

/-- Native algebra automorphisms preserve the Hilbert norm. -/
theorem CompactAutomorphism.norm_map (g : CompactAutomorphism) (x : Albert) :
    ‖g.equiv x‖ = ‖x‖ := (g.equiv.isometryOfInner g.inner_map).norm_map x

end
end Glennie
