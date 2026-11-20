/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RootedExtension
public import VaughtConjecture.Knight.TerminalBase
public import VaughtConjecture.Knight.ReceiveCover
public import VaughtConjecture.Knight.PairedTrace

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

variable {α : LimitStage} {M : Type w}

/-- **Literal one-point rooted transfer** (Prop. 7.3.3's shape): over every evaluated tuple
containing the root, every admissible one-point extension of the realized label is realized
(the new point is the last coordinate). -/
def OnePointRootedExtensionOver (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ (P : S α.1 (n + 1)), typeMap Fin.castSuccEmb P = some p → Adm Fin.castSuccEmb p P →
      ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ W.eval u = some P

open AmalgamationPlan

/-- The trivial admissibility predicate. -/
def AdmTop (α : LimitStage) : RootedAdmissibility α := fun _ _ _ => True

/-- **One-point rooted transfer iterates to finite-extension rooted transfer** (trivial
admissibility). -/
theorem rootedExtensionOver_of_onePoint {W : KnightRealization α M}
    (hcons : W.IsExactParentConsistent) {c₀ : ℕ} {core : Fin c₀ ↪ M}
    (hone : OnePointRootedExtensionOver W core (AdmTop α)) :
    RootedExtensionOver W core (AdmTop α) := by
  intro n t p hroot ht N f P hfP _
  obtain ⟨u, Q, hu, hEval, he⟩ := receiveCover hcons
    (Inv := fun t _ => ∃ e : Fin c₀ ↪ _, e.trans t = core)
    (Rel := fun P Q => P = Q) (fun _ => rfl) Eq.trans
    (fun P g hg t p ht hroot hcof => by
      obtain ⟨u, hu, hEval⟩ := hone t p hroot ht _ hcof trivial
      obtain ⟨e, he⟩ := hroot
      have hr : (e.trans Fin.castSuccEmb).trans u = core := by
        aesop
      exact ⟨u, P, P.restrictFace g hg, hu, ⟨_, hr⟩, rfl, typeMap_eq_some g P hg, hEval⟩)
    P f t p hfP ht hroot
  aesop

end VaughtConjecture.Knight
