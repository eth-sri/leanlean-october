module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Induced groups of equivariant functions

For a subgroup `H` of `G` acting on a commutative group `B`, the induced
group consists of functions satisfying `f (h * x) = h • f x`. Right
translation gives its `G`-action. Evaluation at the identity is an
`H`-equivariant epimorphism, without any finite-index assumption.
-/

namespace ProCGroups.InducedFunctions

universe uG uB

variable {G : Type uG} {B : Type uB}

/-- The subgroup of equivariant functions defining the induced group. -/
def inducedSubgroup [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] : Subgroup (G → B) where
  carrier := {f | ∀ (h : H) (x : G), f (h.1 * x) = h • f x}
  one_mem' := by
    intro h x
    exact (smul_one h).symm
  mul_mem' := by
    intro f k hf hk h x
    simp only [Pi.mul_apply, hf h x, hk h x]
    exact (MulDistribMulAction.smul_mul h (f x) (k x)).symm
  inv_mem' := by
    intro f hf h x
    simp only [Pi.inv_apply, hf h x]
    exact (map_inv (MulDistribMulAction.toMonoidHom B h) (f x)).symm

/-- The commutative group of equivariant functions. -/
abbrev InducedModule [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :=
  inducedSubgroup (G := G) (B := B) H

/-- The canonical right-translation action on equivariant functions. -/
instance inducedMulDistribMulAction [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    MulDistribMulAction G (InducedModule (B := B) H) where
  smul g f := ⟨fun x ↦ f.1 (x * g), by
    intro h x
    simpa only [mul_assoc] using f.2 h (x * g)⟩
  one_smul := by
    intro f
    apply Subtype.ext
    funext x
    change f.1 (x * 1) = f.1 x
    rw [mul_one]
  mul_smul := by
    intro g k f
    apply Subtype.ext
    funext x
    change f.1 (x * (g * k)) = f.1 ((x * g) * k)
    rw [mul_assoc]
  smul_mul := by
    intro g f k
    ext x
    rfl
  smul_one := by
    intro g
    ext x
    rfl

/-- Evaluation at the identity element of the ambient group. -/
def inducedEvaluation [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    InducedModule (B := B) H →* B where
  toFun f := f.1 1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem inducedEvaluation_apply [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] (f : InducedModule (B := B) H) :
    inducedEvaluation H f = f.1 1 :=
  rfl





end ProCGroups.InducedFunctions
