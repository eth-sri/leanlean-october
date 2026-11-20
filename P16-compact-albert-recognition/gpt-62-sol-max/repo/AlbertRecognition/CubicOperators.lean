/- Exact arbitrary-cubic/operator dictionary for the scaled compact reference.
The dual equivalence is derived from the actual positive metric and dimension.
No Jordan or reference-invariance hypothesis is imposed on the unknown cubic. -/
module

public import AlbertRecognition.ReferenceCoordinates
public import Mathlib.LinearAlgebra.BilinearForm.Properties
@[expose] public section
namespace AlbertRecognition
noncomputable section

theorem metric_nondegenerate : metricBilin.Nondegenerate :=
  ⟨fun x hx => (gA_self_eq_zero x).mp (hx x),
    fun x hx => (gA_self_eq_zero x).mp (hx x)⟩

/-- The metric-dual isomorphism uses the actual scaled form, not unscaled Riesz. -/
def metricDual : V ≃ₗ[ℝ] Module.Dual ℝ V := metricBilin.toDual metric_nondegenerate

@[simp] theorem metricDual_apply (x y : V) : metricDual x y = gA x y := rfl

/-- Every arbitrary symmetric trilinear form has its unique actual multiplication
operators obtained by raising one index with the specified scaled metric. -/
def KB (B : SymmetricCubic) : V →ₗ[ℝ] V →ₗ[ℝ] V := B.form.compr₂ metricDual.symm.toLinearMap

theorem KB_pairing (B : SymmetricCubic) (x y z : V) : gA (KB B x y) z = B.form x y z := by
  rw [← metricDual_apply, KB, LinearMap.compr₂_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem KB_comm (B : SymmetricCubic) (x y : V) : KB B x y = KB B y x :=
  congrArg metricDual.symm (LinearMap.ext (B.swap12 x y))

theorem KB_selfadjoint (B : SymmetricCubic) (x y z : V) :
    gA (KB B x y) z = gA y (KB B x z) := by
  rw [gA_comm y (KB B x z), KB_pairing, KB_pairing, B.swap23]

/-- Native CA packaged as a genuine symmetric trilinear form. -/
def referenceForm : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ := KA.compr₂ metricBilin

private theorem referenceForm_apply (x y z : V) : referenceForm x y z = CA x y z := by simp [referenceForm, LinearMap.compr₂_apply, metricBilin_apply, CA]

def referenceCubic : SymmetricCubic where
  form := referenceForm
  swap12 x y z := by simpa only [referenceForm_apply] using CA_swap12 x y z
  swap23 x y z := by simpa only [referenceForm_apply] using CA_swap23 x y z

theorem KB_referenceCubic : KB referenceCubic = KA := by
  ext x y : 2
  simp only [KB, referenceCubic, referenceForm, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
  exact metricDual.symm_apply_apply (KA x y)

/-- Native linear-operator commutator, independent of any geometric connection. -/
def operatorComm (P Q : V →ₗ[ℝ] V) : V →ₗ[ℝ] V := P.comp Q - Q.comp P

def q (B : SymmetricCubic) (x y : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (KB B y)

/-- Literal cyclic Jacobi map on every symmetric cubic, with no extra premises. -/
def A (T : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic)
    (x y z : V) : V →ₗ[ℝ] V :=
  operatorComm (KB B x) (T y z) + operatorComm (KB B y) (T z x) +
    operatorComm (KB B z) (T x y)

def wedge (x y : V) : V →ₗ[ℝ] V := (metricBilin y).smulRight x - (metricBilin x).smulRight y

@[simp] theorem wedge_apply (x y z : V) : wedge x y z = gA y z • x - gA x z • y := by
  simp [wedge]

/-- The native algebraic reference tensor; this is not a definition of the
actual Levi-Civita curvature required by the complete geometric endpoint. -/
def D (x y : V) : V →ₗ[ℝ] V := wedge x y + q referenceCubic x y

end
end AlbertRecognition
