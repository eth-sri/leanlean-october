/- Exact arbitrary-cubic/operator dictionary for the scaled compact reference.
The dual equivalence is derived from the actual positive metric and dimension.
No Jordan or reference-invariance hypothesis is imposed on the unknown cubic. -/
module
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import AlbertRecognition.Reference
public import Glennie.Hilbert
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section
namespace AlbertRecognition
noncomputable section

/-- The explicit trace/3 metric as a curried bilinear map. -/
def metricBilin : LinearMap.BilinForm ℝ V :=
  (innerₛₗ ℝ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ).compr₂ (LinearMap.mulRight ℝ (3⁻¹ : ℝ))

theorem metric_nondegenerate : metricBilin.Nondegenerate :=
  ⟨fun x hx => (gA_self_eq_zero x).mp (hx x),
    fun x hx => (gA_self_eq_zero x).mp (hx x)⟩

/-- The metric-dual isomorphism uses the actual scaled form, not unscaled Riesz. -/
def metricDual : V ≃ₗ[ℝ] Module.Dual ℝ V := metricBilin.toDual metric_nondegenerate

/-- Every arbitrary symmetric trilinear form has its unique actual multiplication
operators obtained by raising one index with the specified scaled metric. -/
def KB (B : SymmetricCubic) : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  B.form.compr₂ metricDual.symm.toLinearMap

theorem KB_pairing (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = B.form x y z := by
  change metricBilin
    ((metricBilin.toDual metric_nondegenerate).symm (B.form x y)) z = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

theorem KB_comm (B : SymmetricCubic) (x y : V) : KB B x y = KB B y x := by
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  change gA (KB B x y) z = gA (KB B y x) z
  rw [KB_pairing, KB_pairing, B.swap12]

theorem KB_selfadjoint (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = gA y (KB B x z) := by
  rw [gA_comm y (KB B x z), KB_pairing, KB_pairing, B.swap23]

/-- Native CA packaged as a genuine symmetric trilinear form. -/
def referenceForm : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  KA.compr₂ metricBilin

def referenceCubic : SymmetricCubic where
  form := referenceForm
  swap12 := CA_swap12
  swap23 := CA_swap23

theorem KB_referenceCubic : KB referenceCubic = KA := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply metricDual.injective
  apply LinearMap.ext
  intro z
  change gA (KB referenceCubic x y) z = gA (KA x y) z
  exact KB_pairing referenceCubic x y z

/-- Faithfulness: raising an index loses no information about an arbitrary B. -/
theorem KB_injective : Function.Injective KB := by
  intro B C h
  have hform : B.form = C.form := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    rw [← KB_pairing B x y z, ← KB_pairing C x y z, h]
  exact SymmetricCubic.ext hform

/-- Native linear-operator commutator, independent of any geometric connection. -/
@[simps! apply] def operatorComm (P Q : V →ₗ[ℝ] V) : V →ₗ[ℝ] V := P.comp Q - Q.comp P

def q (B : SymmetricCubic) (x y : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (KB B y)

/-- Literal cyclic Jacobi map on every symmetric cubic, with no extra premises. -/
def A (T : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic)
    (x y z : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (T y z) + operatorComm (KB B y) (T z x) +
    operatorComm (KB B z) (T x y)

def wedge (x y : V) : V →ₗ[ℝ] V where
  toFun z := gA y z • x - gA x z • y
  map_add' z w := by
    simp only [gA_add_right, add_smul]
    module
  map_smul' r z := by
    simp only [RingHom.id_apply, gA_smul_right, mul_smul, smul_sub]

/-- The native algebraic reference tensor; this is not a definition of the
actual Levi-Civita curvature required by the complete geometric endpoint. -/
def D (x y : V) : V →ₗ[ℝ] V := wedge x y + q referenceCubic x y

end
end AlbertRecognition
