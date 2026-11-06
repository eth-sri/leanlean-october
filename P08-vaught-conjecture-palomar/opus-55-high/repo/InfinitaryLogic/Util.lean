/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# Utility Lemmas

Small lemmas about `Empty.elim`, `Fin.elim0`, `Fin.snoc`, and `Fin.append` that are used
across the infinitary logic library but not (yet) in Mathlib.
-/

@[expose] public section

universe u v

/-- Any function composed with `Empty.elim` is `Empty.elim`. -/
theorem comp_empty_elim {α : Sort u} {β} (f : α → β) :
    f ∘ (Empty.elim : Empty → α) = Empty.elim :=
  funext (fun x => x.elim)

/-- Any function composed with `Fin.elim0` is `Fin.elim0`. -/
theorem comp_fin_elim0 {α : Type u} {β : Type v} f :
    f ∘ (Fin.elim0 : Fin 0 → α) = (Fin.elim0 : Fin 0 → β) :=
  funext (fun x => x.elim0)

/-- Any function from `Fin 0` equals `Fin.elim0`. -/
theorem Fin.eq_elim0 {α : Type u} (f : Fin 0 → α) : f = Fin.elim0 :=
  funext (fun x => x.elim0)

