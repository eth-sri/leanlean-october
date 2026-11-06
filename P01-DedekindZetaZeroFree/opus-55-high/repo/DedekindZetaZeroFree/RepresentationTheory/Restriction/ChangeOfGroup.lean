module

public import Mathlib.RepresentationTheory.Invariants

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/RepresentationTheory/Rep/ChangeOfGroup.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

public noncomputable section

universe u uG uH uK uL uV uW uU

namespace Representation

section Monoid

variable {R : Type u} {G : Type uG} {H : Type uH} {K : Type uK}
  {V : Type uV} {W : Type uW} {U : Type uU}
  [Semiring R] [Monoid G] [Monoid H] [Monoid K]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]

instance isTrivial_comp (σ : Representation R H W) [σ.IsTrivial] (f : G →* H) :
    Representation.IsTrivial (σ.comp f) :=
  ⟨fun g ↦ IsTrivial.out (f g)⟩
