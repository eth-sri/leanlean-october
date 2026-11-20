/- Native compact-Albert reference for the bounded curvature-recognition gate.
The metric is explicitly trace/3. No global metric instance is introduced.
This file does not assert the fixed-frame or geometric recognition theorem. -/
module

public import Glennie.Native.CubicIdentity
public import Mathlib.LinearAlgebra.BilinearForm.Basic
@[expose] public section
namespace AlbertRecognition
noncomputable section

open Glennie
open scoped BigOperators

abbrev V := traceLinear.ker

@[simp] theorem trace_V (x : V) : Glennie.trace (x : Albert) = 0 := x.property

def traceThird : Albert →ₗ[ℝ] ℝ where
  toFun x := Glennie.trace x / 3
  map_add' x y := by rw [trace_add, add_div]
  map_smul' r x := by simp [trace_smul, smul_eq_mul, mul_div_assoc]

def project : Albert →ₗ[ℝ] V :=
  LinearMap.codRestrict _ (LinearMap.id - traceThird.smulRight (1 : Albert)) trace_traceless

@[simp] theorem project_coe (x : Albert) :
    (project x : Albert) = Glennie.traceless x := rfl

@[simp] theorem project_V (x : V) : project (x : Albert) = x := by grind [project_coe, Glennie.traceless, trace_V, zero_div, zero_smul, sub_zero]

/-- The specified scaled trace metric, carried explicitly throughout this gate. -/
def gA (x y : V) : ℝ := Glennie.inner (x : Albert) (y : Albert) / 3

theorem gA_comm (x y : V) : gA x y = gA y x := by
  exact congrArg (fun r : ℝ => r / 3) (Glennie.inner_comm _ _)

/-- The scaled trace metric as a curried bilinear form. -/
def metricBilin : LinearMap.BilinForm ℝ V :=
  (jordanLinear.compl₁₂ traceLinear.ker.subtype traceLinear.ker.subtype).compr₂ traceThird

@[simp] theorem metricBilin_apply (x y : V) : metricBilin x y = gA x y := rfl

theorem gA_self_eq_zero (x : V) : gA x x = 0 ↔ x = 0 := by simp [gA, div_eq_zero_iff, inner_self_eq_zero, Submodule.coe_eq_zero]

/-- Orthogonal tracefree projection in the exact scale used by the target. -/
theorem project_pairing (u : Albert) (z : V) :
    gA (project u) z = Glennie.inner u (z : Albert) / 3 := by
  have hz : Glennie.inner (1 : Albert) (z : Albert) = 0 := by simp [Glennie.inner]
  simp [gA, traceless, inner_sub_left, inner_smul_left, hz]

/-- The literal projected native Jordan multiplication. -/
def KA : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  (jordanLinear.compl₁₂ traceLinear.ker.subtype traceLinear.ker.subtype).compr₂ project

@[simp] theorem KA_apply (x y : V) : KA x y = project (jordan (x : Albert) (y : Albert)) := by simp [KA, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Submodule.subtype_apply, jordanLinear_apply]

theorem KA_comm (x y : V) : KA x y = KA y x := by
  simp only [KA_apply, Glennie.jordan_comm]

def CA (x y z : V) : ℝ := gA (KA x y) z

theorem CA_eq_native (x y z : V) :
    CA x y z = Glennie.inner (Glennie.jordan (x : Albert) (y : Albert))
      (z : Albert) / 3 :=
  project_pairing _ _

theorem CA_swap12 (x y z : V) : CA x y z = CA y x z := by
  unfold CA
  rw [KA_comm]

theorem CA_swap23 (x y z : V) : CA x y z = CA x z y := by
  rw [CA_eq_native, CA_eq_native,
    Glennie.inner_jordan_associative, Glennie.inner_jordan_associative,
    Glennie.jordan_comm (y : Albert) (z : Albert)]

/-- Arbitrary symmetric real trilinear forms on the actual tracefree space.
Adjacent-swap symmetry and real multilinearity are the only fields. -/
@[ext] structure SymmetricCubic where
  form : V →ₗ[ℝ] (V →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
  swap12 : ∀ x y z, form x y z = form y x z
  swap23 : ∀ x y z, form x y z = form x z y

/-- Native zero-based diagonal idempotent coordinates, independent of any
spectral-decomposition or automorphic-diagonalization module. -/
def e : Fin 3 → Albert :=
  ![⟨1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩]

@[simp] theorem trace_e (i : Fin 3) : Glennie.trace (e i) = 1 := by
  fin_cases i <;> norm_num [e, Glennie.trace]

def h (i : Fin 3) : V :=
  ⟨(1 : Albert) - (3 : ℝ) • e i, by simp⟩

theorem h_sum_zero : h 0 + h 1 + h 2 = 0 := by
  apply Subtype.ext
  apply Albert.ext <;> norm_num [h, e, Glennie.unit]

def X12 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, 0, 0, a⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' a b := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' r a := by apply Subtype.ext; apply Albert.ext <;> simp

end
end AlbertRecognition
