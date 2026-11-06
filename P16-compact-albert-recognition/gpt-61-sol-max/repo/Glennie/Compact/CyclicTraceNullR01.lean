/- Associative cyclic-trace scalar-null kernel. -/
module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Aesop
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section
namespace Glennie.Compact.CyclicTraceNullR01
noncomputable section

variable {M : Type*} [Ring M] [Algebra ℝ M]

def symmProd (a b : M) : M := (1 / 2 : ℝ) • (a * b + b * a)

def quadratic (a b : M) : M :=
  (2 : ℝ) • symmProd a (symmProd a b) - symmProd (symmProd a a) b

/-- Associativity expands the symmetrized quadratic representation to aba. -/
theorem quadratic_eq_sandwich (a b : M) : quadratic a b = a * b * a := by
  simp only [quadratic, symmProd, smul_mul_assoc, mul_smul_comm,
    mul_add, add_mul, smul_add, smul_smul, mul_assoc]
  module

/-- Only cyclicity and linearity are needed for the degree-nine cancellation. -/
theorem cyclic_word_cancel (τ : M →ₗ[ℝ] ℝ)
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a)) (P Q : M) :
    τ (P * Q * P + P * Q * Q - Q * P * P - Q * P * Q) = 0 := by
  grind

def scalarPhi (τ : M →ₗ[ℝ] ℝ) (x y z : M) : ℝ :=
  τ ((quadratic x (quadratic y z) - quadratic y (quadratic x z)) *
    quadratic z (symmProd x y))

/-- This is vanishing for the explicitly compatible pairing τ(ab).
It does not assert that this pairing is positive on the whole associative algebra. -/
theorem scalarPhi_eq_zero (τ : M →ₗ[ℝ] ℝ)
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a)) (x y z : M) :
    scalarPhi τ x y z = 0 := by
  have h := cyclic_word_cancel τ hcyclic (x * y * z) (y * x * z)
  simp only [scalarPhi, quadratic_eq_sandwich, symmProd, mul_add, add_mul,
    sub_mul, mul_smul_comm, smul_mul_assoc, map_add, map_sub, map_smul,
    smul_eq_mul, mul_assoc] at h ⊢
  linarith only [h]

section Represented

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def quadraticWith (j : E → E → E) (a b : E) : E :=
  (2 : ℝ) • j a (j a b) - j (j a a) b

def phiWith (j : E → E → E) (B : E → E → ℝ) (x y z : E) : ℝ :=
  B (quadraticWith j x (quadraticWith j y z) -
    quadraticWith j y (quadraticWith j x z)) (quadraticWith j z (j x y))

theorem map_quadraticWith (j : E → E → E) (ρ : E →ₗ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ρ (quadraticWith j a b) = quadratic (ρ a) (ρ b) := by
  simp only [quadraticWith, map_sub, map_smul, hj, quadratic]

/-- Actual compatible special-null producer: product and form compatibility
are hypotheses; scalar nullness is proved by the associative cyclic kernel. -/
theorem phiWith_eq_zero_of_compatible_trace
    (j : E → E → E) (B : E → E → ℝ) (ρ : E →ₗ[ℝ] M)
    (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, B a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a)) (x y z : E) :
    phiWith j B x y z = 0 := by
  unfold phiWith
  rw [hB]
  simp only [map_sub, map_quadraticWith j ρ hj, hj]
  exact scalarPhi_eq_zero τ hcyclic (ρ x) (ρ y) (ρ z)

end Represented
end
end Glennie.Compact.CyclicTraceNullR01
