module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionNorm
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Core comparisons for finite-tower idèle-class norms

This internal provider isolates the tensor base-change, embedding-product,
and direct-limit comparison lemmas used by the non-Galois finite-tower norm
theorem.  Keeping these commands in their own leaf prevents the endpoint
proof from rebuilding the helper environment.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity
namespace FiniteTowerNormCore

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

universe u

 theorem finiteTowerIdeleIsMulCommutative
    {K M L : Type u}
    [Field K] [NumberField K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] :
    IsMulCommutative (TowerRelativeIdeleGroup K M L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] finiteTowerIdeleIsMulCommutative

/-- Algebra homomorphisms into an ambient field are equivalent to algebra
homomorphisms into the normal closure inside that field. -/
noncomputable def normalClosureAlgHomEquiv
    {F E L : Type u}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] :
    (E →ₐ[F] L) ≃
      (E →ₐ[F] IntermediateField.normalClosure F E L) :=
  (normalClosure.algHomEquiv F E L).symm

/-- Lift an algebra homomorphism to the normal closure in its codomain. -/
noncomputable def normalClosureLiftAlgHom
    {F E L : Type u}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    (f : E →ₐ[F] L) :
    E →ₐ[F] IntermediateField.normalClosure F E L :=
  normalClosureAlgHomEquiv f

/-- Promote a ring homomorphism compatible with the scalar maps to an
algebra homomorphism. -/
def algHomOfCompatibleRingHom
    {R S A : Type u}
    [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R S] [Algebra R A]
    (f : S →+* A)
    (h : ∀ x : R, f (algebraMap R S x) = algebraMap R A x) :
    S →ₐ[R] A where
  toRingHom := f
  commutes' := h





















end FiniteTowerNormCore
end Reciprocity
end GlobalClassFieldTheory

end
