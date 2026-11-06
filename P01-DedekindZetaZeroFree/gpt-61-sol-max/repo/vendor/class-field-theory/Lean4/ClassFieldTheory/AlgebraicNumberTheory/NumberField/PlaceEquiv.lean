module

public import Mathlib

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Places under a number-field equivalence

A field equivalence bijects both the finite and infinite places. These
equivalences reindex placewise products without changing their mathematics.
-/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v









/-- Infinite places correspond by pulling embeddings back along the inverse
field equivalence. -/
def infinitePlaceEquivOfRingEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) :
    NumberField.InfinitePlace F ≃ NumberField.InfinitePlace G where
  toFun w := w.comap e.symm.toRingHom
  invFun w := w.comap e.toRingHom
  left_inv w := by
    simp_all [NumberField.InfinitePlace.comap_comp, NumberField.InfinitePlace.comap_id] <;> aesop
  right_inv w := by
    simp_all [NumberField.InfinitePlace.comap_comp, NumberField.InfinitePlace.comap_id] <;> aesop

end ClassFieldTheory

end
