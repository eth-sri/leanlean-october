module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Algebra
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Linear algebra for representative-level `H¹`

The algebraic structure on `H1Function U` is transported across the exact
equivalence with `W1pFunction U 2`. Thus all analytic closure facts come from
the generic `W^{1,p}` layer; this file contains only the `p = 2`
compatibility surface used by the application repositories.
-/

@[expose] public section

namespace PDE

namespace H1Function
section
variable {d : ℕ} {U : Set (Vec d)}

instance  : Zero (H1Function U) :=
  h1FunctionEquivW1pFunction.zero

instance  : Add (H1Function U) :=
  h1FunctionEquivW1pFunction.add

instance  : Neg (H1Function U) :=
  h1FunctionEquivW1pFunction.Neg

instance  : Sub (H1Function U) :=
  h1FunctionEquivW1pFunction.sub

instance  : SMul ℝ (H1Function U) :=
  h1FunctionEquivW1pFunction.smul ℝ

@[simp]
theorem zero_toFun  :
    (0 : H1Function U).toFun = 0 :=
  rfl

@[simp]
theorem zero_grad  :
    (0 : H1Function U).grad = 0 :=
  rfl

@[simp]
theorem add_toFun 
    (u v : H1Function U) :
    (u + v).toFun = fun x => u x + v x :=
  rfl

@[simp]
theorem add_grad 
    (u v : H1Function U) :
    (u + v).grad = fun x => u.grad x + v.grad x :=
  rfl

@[simp]
theorem neg_toFun 
    (u : H1Function U) :
    (-u).toFun = fun x => -u x :=
  rfl

@[simp]
theorem neg_grad 
    (u : H1Function U) :
    (-u).grad = fun x => -u.grad x :=
  rfl

@[simp]
theorem sub_toFun 
    (u v : H1Function U) :
    (u - v).toFun = fun x => u x - v x :=
  rfl

@[simp]
theorem sub_grad 
    (u v : H1Function U) :
    (u - v).grad = fun x => u.grad x - v.grad x :=
  rfl

@[simp]
theorem smul_toFun 
    (c : ℝ) (u : H1Function U) :
    (c • u).toFun = fun x => c * u x :=
  rfl

@[simp]
theorem smul_grad 
    (c : ℝ) (u : H1Function U) :
    (c • u).grad = fun x => c • u.grad x :=
  rfl

instance  : AddCommGroup (H1Function U) :=
  h1FunctionEquivW1pFunction.addCommGroup

instance  : Module ℝ (H1Function U) :=
  h1FunctionEquivW1pFunction.addEquiv.module ℝ
end

end H1Function

end PDE
