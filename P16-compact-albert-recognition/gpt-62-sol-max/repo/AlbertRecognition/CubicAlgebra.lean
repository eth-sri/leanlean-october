/- Native arbitrary-cubic scaling and universal associative commutator Jacobi.
-/
module

public import AlbertRecognition.CubicOperators
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Tactic.NoncommRing
@[expose] public section
namespace AlbertRecognition
noncomputable section
attribute [local instance] LieRing.ofAssociativeRing

theorem symmetricCubic_eq_of_form_eq {B C : SymmetricCubic}
    (hform : B.form = C.form) : B = C := SymmetricCubic.ext hform

/-- Literal real scaling of a genuine symmetric trilinear form. -/
def scalarCubic (r : ℝ) (B : SymmetricCubic) : SymmetricCubic where
  form := r • B.form
  swap12 x y z := congrArg (fun a : ℝ => r * a) (B.swap12 x y z)
  swap23 x y z := congrArg (fun a : ℝ => r * a) (B.swap23 x y z)

@[simp] theorem scalarCubic_form (r : ℝ) (B : SymmetricCubic) (x y z : V) :
    (scalarCubic r B).form x y z = r * B.form x y z := rfl

/-- Raising the index with the same trace/3 metric commutes with real scaling. -/
theorem KB_scalarCubic (r : ℝ) (B : SymmetricCubic) : KB (scalarCubic r B) = r • KB B :=
  LinearMap.ext fun x => LinearMap.ext fun y => metricDual.symm.map_smul r (B.form x y)

theorem operatorComm_eq_lie (P Q : Module.End ℝ V) : operatorComm P Q = ⁅P,Q⁆ := rfl

section SelfJacobi

/- Keep index raising opaque during specialization only; its definition and
kernel body remain unchanged. -/
attribute [local irreducible] KB

/-- Every genuine cubic satisfies Jacobi for its own q, without a Jordan premise. -/
theorem A_q_self (B : SymmetricCubic) : A (q B) B = 0 := by
  set_option backward.isDefEq.respectTransparency true in
    with_reducible
      funext x y z
      simpa only [A, q, operatorComm_eq_lie, Pi.zero_apply] using
        lie_jacobi (KB B x) (KB B y) (KB B z)

end SelfJacobi

/-- Quadratic scaling for the literal native commutator tensor. -/
theorem q_scalarCubic (r : ℝ) (B : SymmetricCubic) :
    q (scalarCubic r B) = r^2 • q B := by
  funext x y
  simp only [q, operatorComm_eq_lie, KB_scalarCubic, Pi.smul_apply, LinearMap.smul_apply,
    smul_lie, lie_smul, smul_smul, pow_two]

end
end AlbertRecognition
