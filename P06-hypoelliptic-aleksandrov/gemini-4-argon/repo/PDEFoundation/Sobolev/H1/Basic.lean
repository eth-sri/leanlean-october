module

public import PDEFoundation.Sobolev.W1p.Basic

/-!
# Representative-level `H¹`

This file supplies the field-name-compatible `H1Function` interface used by
the application repositories. It is exactly the `p = 2` specialization of the
representative-level `W1pFunction` API: the explicit equivalence below loses
neither the chosen value representative nor the chosen gradient
representative.

The representative bundle is convenient for pointwise formulas. It is not the
complete Sobolev carrier; `PDEFoundation.Sobolev.H1.Graph` names the canonical
quotient graph.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

/- Scalar `L²` membership on a restricted domain. -/
abbrev MemL2On {d } (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u

/- Coordinatewise gradient `L²` membership on a restricted domain. -/
abbrev GradMemL2On {d }
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du

/- A concrete scalar representative and a chosen coordinate weak gradient in
`L²(U)`.

This deliberately matches the established application-repository field names.
Use `H1Graph U` when completeness or quotient-level functional analysis is
required.
-/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

namespace H1Function

@[ext]
theorem ext {d } {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

/- The `i`th chosen gradient component belongs to `L²(U)`. -/
theorem grad_memL2 {d U}
    (u : H1Function U) (i : Fin d) :
    MemL2On U (fun x => u.grad x i) :=
  u.gradMemL2 i

/- Regard an `H1Function` as the exactly corresponding `W1pFunction` at
`p = 2`. -/
def toW1pFunction {d } {U : Set (Vec d)}
    (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

@[simp]
theorem toW1pFunction_toFun {d } {U : Set (Vec d)} (u : H1Function U) :
    u.toW1pFunction.toFun = u.toFun := rfl

@[simp]
theorem toW1pFunction_grad {d } {U : Set (Vec d)} (u : H1Function U) :
    u.toW1pFunction.grad = u.grad := rfl

end H1Function

namespace W1pFunction

/- Regard a representative-level `W1pFunction` at `p = 2` as the exactly
corresponding `H1Function`. -/
def toH1Function {d } {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient

@[simp]
theorem toH1Function_toFun {d } {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toFun = u.toFun := rfl

@[simp]
theorem toH1Function_grad {d } {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.grad = u.grad := rfl

end W1pFunction

namespace H1Function

@[simp]
theorem toH1Function_toW1pFunction {d } {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toH1Function = u := by
  apply H1Function.ext <;> rfl

def restrict {d } {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    H1Function V :=
  (u.toW1pFunction.restrict hVOpen hVU).toH1Function

@[simp]
theorem restrict_toFun {d } {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).toFun = u.toFun := rfl

@[simp]
theorem restrict_grad {d } {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).grad = u.grad := rfl

@[simp]
theorem restrict_apply {d U V}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) (x : Vec d) :
    u.restrict hVOpen hVU x = u x := rfl

end H1Function

namespace W1pFunction

@[simp]
theorem toW1pFunction_toH1Function {d } {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toW1pFunction = u := by
  apply W1pFunction.ext <;> rfl

end W1pFunction

/- `H1Function U` and `W1pFunction U 2` carry exactly the same representative
data. -/
def h1FunctionEquivW1pFunction {d } {U : Set (Vec d)} :
    H1Function U ≃ W1pFunction U (2 : ℝ≥0∞) where
  toFun := H1Function.toW1pFunction
  invFun := W1pFunction.toH1Function
  left_inv := H1Function.toH1Function_toW1pFunction
  right_inv := W1pFunction.toW1pFunction_toH1Function

end PDE
