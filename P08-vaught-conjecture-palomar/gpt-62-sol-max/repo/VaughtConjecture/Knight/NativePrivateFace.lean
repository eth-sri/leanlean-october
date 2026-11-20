/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageSemantics
public import VaughtConjecture.Knight.ExactSemanticFace
public import VaughtConjecture.Knight.CappedDonorSource

@[expose] public section

namespace VaughtConjecture.Knight.NativePrivateFace

open Transform Value ExtOrd CappedDonor

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A S : Finset ι} {D : CellScheme A}

variable {N : ℕ} (C : SemScheme N) (place : Fin N ↪ ι) (hS : Finset.univ.image place = S)

variable {sem : Semantics D}

variable (E : ExactSemanticFace (PointImageSemantics.rows C.scheme place hS C.rows) sem)

abbrev fullEquiv : C.scheme.below (effC N N) ≃ D.below (S, N) :=
  E.fullEquiv grade_le_effC

theorem fullEquiv_grade (d : C.scheme.below (effC N N)) :
    D.grade (fullEquiv C place hS E d).1 = C.scheme.grade d.1 :=
  congrArg Prod.snd (E.index d.1)

theorem respects_iff (p : D.below (S, N) → ExtOrd) :
    RespectsSemanticsBelow sem (S, N) p ↔
      RespectsSemanticsBelow C.rows (effC N N) (p ∘ fullEquiv C place hS E) :=
  E.full_respects_iff _ p

end

end VaughtConjecture.Knight.NativePrivateFace
