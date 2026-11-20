/- Exact arbitrary-cubic/operator dictionary for the scaled compact reference.
The dual equivalence is derived from the actual positive metric and dimension.
No Jordan or reference-invariance hypothesis is imposed on the unknown cubic. -/
module

public import AlbertRecognition.Reference
public import Glennie.Hilbert
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section
namespace AlbertRecognition
noncomputable section

def referenceCubic : SymmetricCubic := ⟨KA,KA_comm,CA_swap23⟩
@[simp] theorem refForm (u v w : V) : referenceCubic.form u v w = CA u v w := rfl
/-- The measured part of the commutator independent of the metric wedge. -/
def q (B : SymmetricCubic) (x y : V) : V →ₗ[ℝ] V := (B.K x).comp (B.K y) - (B.K y).comp (B.K x)
theorem q_apply (B : SymmetricCubic) (x y z : V) : q B x y z = B.K x (B.K y z) - B.K y (B.K x z) := rfl

def wedge (x y : V) := (metricBilin y).smulRight x - (metricBilin x).smulRight y
def D (x y : V) := wedge x y + q referenceCubic x y
end
end AlbertRecognition
