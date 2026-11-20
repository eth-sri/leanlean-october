/- Native compact-Albert reference for the bounded curvature-recognition gate.
The metric is explicitly trace/3. No global metric instance is introduced.
This file does not assert the fixed-frame or geometric recognition theorem. -/
module

public import Glennie.Hilbert
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section
namespace AlbertRecognition
noncomputable section

open Glennie
open scoped BigOperators

def traceFreeSpace : Submodule ℝ Albert := traceLinear.ker
abbrev V := traceFreeSpace

@[simp] theorem trace_V (x : V) : Glennie.trace (x : Albert) = 0 := x.property

def project : Albert →ₗ[ℝ] V where
  toFun x := ⟨Glennie.traceless x, Glennie.trace_traceless x⟩
  map_add' x y := by
    apply Subtype.ext
    change Glennie.traceless (x + y) = Glennie.traceless x + Glennie.traceless y
    simp only [Glennie.traceless, Glennie.trace_add, add_div, add_smul]
    module
  map_smul' r x := by
    apply Subtype.ext
    change Glennie.traceless (r • x) = r • Glennie.traceless x
    simp only [Glennie.traceless, Glennie.trace_smul, smul_sub, smul_smul,
      mul_div_assoc]

@[simp] theorem project_coe (x : Albert) :
    (project x : Albert) = Glennie.traceless x := rfl

@[simp] theorem project_V (x : V) : project (x : Albert) = x := by
  simp [V, project, project_coe, Glennie.traceless, trace_V]

/-- The specified scaled trace metric, carried explicitly throughout this gate. -/
def gA (x y : V) : ℝ := Glennie.inner (x : Albert) (y : Albert) / 3

theorem gA_comm (x y : V) : gA x y = gA y x := by simp [gA,Glennie.inner_comm]

def metricBilin : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ gA
  (by intros; simp [gA,Glennie.inner_add_left,add_div]) (by intros; simp [gA,Glennie.inner_smul_left,mul_div_assoc])
  (by intros; simp [gA,Glennie.inner_add_right,add_div]) (by intros; simp [gA,Glennie.inner_smul_right,mul_div_assoc])
theorem gA_add_left (x y z : V) : gA (x+y) z = gA x z + gA y z := congrArg (fun f : V →ₗ[ℝ] ℝ => f z) (metricBilin.map_add x y)
theorem gA_smul_left (r : ℝ) (x y : V) : gA (r • x) y = r * gA x y := congrArg (fun f : V →ₗ[ℝ] ℝ => f y) (metricBilin.map_smul r x)
theorem gA_ext {x y : V} (h : ∀ v, gA x v = gA y v) : x = y := by
  apply ext_inner_right ℝ; intro v
  exact (div_left_inj' (by norm_num : (3:ℝ) ≠ 0)).mp (h v)

/-- Orthogonal tracefree projection in the exact scale used by the target. -/
theorem project_pairing (u : Albert) (z : V) :
    gA (project u) z = Glennie.inner u (z : Albert) / 3 := by
  change Glennie.inner (Glennie.traceless u) (z : Albert) / 3 = _
  rw [Glennie.traceless, Glennie.inner_sub_left, Glennie.inner_smul_left]
  have hunit : Glennie.inner (1 : Albert) (z : Albert) = 0 := by
    simp [Glennie.inner, Glennie.jordan_unit_left]
  simp_all

/-- The literal projected native Jordan multiplication, bilinear in both inputs. -/
def KA : V →ₗ[ℝ] (V →ₗ[ℝ] V) :=
  (jordanLinear.compl₁₂ traceFreeSpace.subtype traceFreeSpace.subtype).compr₂ project

@[simp] theorem KA_apply (x y : V) :
    KA x y = project (Glennie.jordan (x : Albert) (y : Albert)) := rfl

theorem KA_comm (x y : V) : KA x y = KA y x := by
  simp [Glennie.jordan_comm]

def CA (x y z : V) : ℝ := gA (KA x y) z

theorem CA_eq_native (x y z : V) :
    CA x y z = Glennie.inner (Glennie.jordan (x : Albert) (y : Albert))
      (z : Albert) / 3 :=
  project_pairing _ _

theorem CA_swap12 (x y z : V) : CA x y z = CA y x z := by
  unfold CA
  rw [KA_comm]

theorem CA_swap23 (x y z : V) : CA x y z = CA x z y := by
  simp [CA_eq_native, Glennie.inner_jordan_associative, Glennie.jordan_comm]

/-- A symmetric cubic represented by its metric-raised multiplication. This
is the form in which the curvature supplies the commutators. -/
structure SymmetricCubic where
  K : V →ₗ[ℝ] V →ₗ[ℝ] V
  comm : ∀ x y, K x y = K y x
  symm : ∀ x y z, gA (K x y) z = gA (K x z) y

def SymmetricCubic.form (B : SymmetricCubic) := B.K.compr₂ metricBilin
theorem SymmetricCubic.swap12 (B : SymmetricCubic) (x y z : V) : B.form x y z = B.form y x z :=
  congrArg (fun w => gA w z) (B.comm x y)
theorem SymmetricCubic.swap23 (B : SymmetricCubic) (x y z : V) : B.form x y z = B.form x z y := B.symm ..

/-- Native zero-based diagonal idempotent coordinates, independent of any
spectral-decomposition or automorphic-diagonalization module. -/
def e : Fin 3 → Albert :=
  ![⟨1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩]

@[simp] theorem trace_e (i : Fin 3) : Glennie.trace (e i) = 1 := by
  fin_cases i <;> norm_num [e, Glennie.trace]

def h (i : Fin 3) : V :=
  ⟨(1 : Albert) - (3 : ℝ) • e i, by
    change Glennie.trace ((1 : Albert) - (3 : ℝ) • e i) = 0
    rw [Glennie.trace_sub, Glennie.trace_unit, Glennie.trace_smul, trace_e]
    norm_num⟩

theorem h_sum_zero : h 0 + h 1 + h 2 = 0 := by
  ext <;> norm_num [h, e, Glennie.unit] <;> norm_num

/-- Three native upper-entry octonion slots; the lower entries are determined
by native Hermitian conjugation, never by inherited pair multiplication. -/
def X12 : Octonion →ₗ[ℝ] V where
  toFun a := ⟨⟨0, 0, 0, 0, 0, a⟩, by change (0 : ℝ) + 0 + 0 = 0; norm_num⟩
  map_add' a b := by apply Subtype.ext; apply Albert.ext <;> simp
  map_smul' r a := by apply Subtype.ext; apply Albert.ext <;> simp

end
end AlbertRecognition
