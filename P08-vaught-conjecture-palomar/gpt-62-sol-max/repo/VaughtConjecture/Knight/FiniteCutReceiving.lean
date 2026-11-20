/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

variable {α : LimitStage} {M : Type w}

abbrev FiniteCutReceiving.At (R : KnightRealization α M) (n : ℕ) : Prop :=
  ∀ (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
    ∀ (P : S α.1 (n + 1)), IsCoface p P →
      ∀ δ : ExtOrd, ⊥ < δ → δ < ofOrd α.1 →
        ∃ (y : M) (hy : y ∉ Set.range t) (q : S α.1 (n + 1)), R.eval (snoc t y hy) = some q ∧
          ∃ h : q.scheme = P.scheme,
            ∀ d, min (q.label d) δ = min (P.label (SemScheme.castCell h d)) δ
/-- **Finite-cut receiving** (FC): over a realized root `t ↦ p`, a legal one-point candidate `P`
over `p`, and a proper cutoff `δ` below the stage, some actual coface `q` over `t` on the exact
scheme of `P` agrees with `P` below `δ`. -/
def FiniteCutReceiving (R : KnightRealization α M) : Prop :=
  ∀ {n}, FiniteCutReceiving.At R n

end VaughtConjecture.Knight
