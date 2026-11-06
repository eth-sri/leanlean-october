module

public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.WeakDerivative.Algebra
import Aesop



/-!
# Linear algebra for representative-level `W^{1,p}`

For `1 ≤ p`, every stored `L^p` value and gradient component is locally
integrable. The raw weak-derivative algebra therefore gives
`W1pFunction U p` its natural real module structure without adding
integrability assumptions to each operation.

The restriction `1 ≤ p` is analytically substantive: below that exponent the
stored `L^p` hypotheses do not imply the local integrability needed for
additivity of the distributional identities.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The value representative of a `W1pFunction` is locally integrable with
respect to restricted volume when `1 ≤ p`. -/
theorem locallyIntegrable_toFun [Fact (1 ≤ p)]
    (u : W1pFunction U p) :
    MeasureTheory.LocallyIntegrable u.toFun (volumeOn U) :=
  u.memLp.locallyIntegrable Fact.out

/-- Every chosen gradient component of a `W1pFunction` is locally integrable
with respect to restricted volume when `1 ≤ p`. -/
theorem locallyIntegrable_grad [Fact (1 ≤ p)]
    (u : W1pFunction U p) (i : Fin d) : type_of% ((u.gradMemLp i).locallyIntegrable Fact.out) :=
  (u.gradMemLp i).locallyIntegrable Fact.out

instance : Zero (W1pFunction U p) where
  zero :=
    { toFun := 0
      grad := 0
      memLp := MeasureTheory.MemLp.zero
      gradMemLp := (fun i => MeasureTheory.MemLp.zero)
      hasWeakGradient := HasWeakGradientOn.zero }

instance [Fact (1 ≤ p)] : Add (W1pFunction U p) where
  add u v :=
    { toFun := u.toFun + v.toFun
      grad := u.grad + v.grad
      memLp := u.memLp.add v.memLp
      gradMemLp := by
        intro i
        exact (u.gradMemLp i).add (v.gradMemLp i)
      hasWeakGradient :=
        u.hasWeakGradient.add v.hasWeakGradient
          u.locallyIntegrable_toFun v.locallyIntegrable_toFun
          u.locallyIntegrable_grad v.locallyIntegrable_grad }

instance : Neg (W1pFunction U p) where
  neg u :=
    { toFun := -u.toFun
      grad := -u.grad
      memLp := u.memLp.neg
      gradMemLp := by
        intro i
        exact (u.gradMemLp i).neg
      hasWeakGradient := u.hasWeakGradient.neg }

instance [Fact (1 ≤ p)] : Sub (W1pFunction U p) where
  sub u v :=
    { toFun := u.toFun - v.toFun
      grad := u.grad - v.grad
      memLp := u.memLp.sub v.memLp
      gradMemLp := by
        intro i
        exact (u.gradMemLp i).sub (v.gradMemLp i)
      hasWeakGradient :=
        u.hasWeakGradient.sub v.hasWeakGradient
          u.locallyIntegrable_toFun v.locallyIntegrable_toFun
          u.locallyIntegrable_grad v.locallyIntegrable_grad }

instance : SMul ℝ (W1pFunction U p) where
  smul c u :=
    { toFun := c • u.toFun
      grad := c • u.grad
      memLp := u.memLp.const_smul c
      gradMemLp := by
        intro i
        exact (u.gradMemLp i).const_smul c
      hasWeakGradient := u.hasWeakGradient.smul c }

@[simp]
theorem zero_toFun :
    (0 : W1pFunction U p).toFun = 0 :=
  rfl

@[simp]
theorem zero_grad :
    (0 : W1pFunction U p).grad = 0 :=
  rfl



@[simp]
theorem add_grad [Fact (1 ≤ p)] (u v : W1pFunction U p) :
    (u + v).grad = fun x => u.grad x + v.grad x :=
  rfl

variable (u : W1pFunction U p)

@[simp]
theorem neg_toFun  :
    (-u).toFun = fun x => -u x :=
  rfl

@[simp]
theorem neg_grad  :
    (-u).grad = fun x => -u.grad x :=
  rfl

@[simp]
theorem sub_toFun [Fact (1 ≤ p)] (u v : W1pFunction U p) :
    (u - v).toFun = fun x => u x - v x :=
  rfl

@[simp]
theorem sub_grad [Fact (1 ≤ p)] (u v : W1pFunction U p) :
    (u - v).grad = fun x => u.grad x - v.grad x :=
  rfl

variable (c : ℝ) (u : W1pFunction U p)

@[simp]
theorem smul_toFun  :
    (c • u).toFun = fun x => c * u x :=
  rfl

@[simp]
theorem smul_grad  :
    (c • u).grad = fun x => c • u.grad x :=
  rfl

instance [Fact (1 ≤ p)] : SMul ℕ (W1pFunction U p) where
  smul n u := (n : ℝ) • u

instance [Fact (1 ≤ p)] : SMul ℤ (W1pFunction U p) where
  smul n u := (n : ℝ) • u

/-- The value-gradient projection is injective; proof fields carry no
additional data. -/
theorem toFunGrad_injective :
    Function.Injective
      (fun u : W1pFunction U p => (u.toFun, u.grad)) := (fun ⦃u v⦄ h => ext (congrArg Prod.fst h) (congrArg Prod.snd h))

instance [Fact (1 ≤ p)] : AddCommGroup (W1pFunction U p) :=
  Function.Injective.addCommGroup
    (fun u  => (u.toFun, u.grad))
    toFunGrad_injective
    rfl
    (fun _ _ => rfl)
    (fun _ => by
      rfl)
    (fun _ _ => by
      rfl)
    (fun u n => by
      apply Prod.ext
      · funext x
        change (((n : ℝ) • u).toFun x) = (n • u.toFun) x
        simp only [smul_toFun, Pi.smul_apply, nsmul_eq_mul]
      · funext x
        ext i
        change (((n : ℝ) • u).grad x i) = (n • u.grad) x i
        simp only [smul_grad, Pi.smul_apply, nsmul_eq_mul,
          smul_eq_mul])
    (fun u n => by
      simp_all <;> aesop)

/-- Additive value-gradient projection used to transfer the real module laws
without inspecting proof fields. -/
def toFunGradAddMonoidHom [Fact (1 ≤ p)] :
    W1pFunction U p →+ ((Vec d → ℝ) × (Vec d → Vec d)) where
  toFun := fun u => (u.toFun, u.grad)
  map_zero' := rfl
  map_add' _ _ := rfl

instance [Fact (1 ≤ p)] : Module ℝ (W1pFunction U p) :=
  Function.Injective.module ℝ
    toFunGradAddMonoidHom
    toFunGrad_injective
    (fun _ _ => rfl)

end W1pFunction

end PDE
