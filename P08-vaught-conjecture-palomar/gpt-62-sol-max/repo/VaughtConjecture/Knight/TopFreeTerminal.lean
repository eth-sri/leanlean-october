/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopWitness

@[expose] public section

namespace VaughtConjecture.Knight.KnightRealization

open TypeTower

universe w

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

theorem noProlongation_of_topFree {β : LimitStage} (hαβ : α < β)
    (htop : ∀ {n} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ d, p.label d ≠ ⊤)
    {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n) (hp : R.eval t = some p) :
    R.NoProlongationToIn IsModelClass hαβ.le := by
  intro hprol
  obtain ⟨y, hy, q, hq, d, _, hd⟩ := sourceTopProduction_of_prolongsToIn hαβ hprol t p hp
  tauto

theorem IsModel.noProlongation_of_topFree (hR : R.IsModel) {β : LimitStage} (hαβ : α < β)
    (htop : ∀ {n} (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p →
      ∀ d, p.label d ≠ ⊤) : R.NoProlongationToIn IsModelClass hαβ.le := by
  obtain ⟨k, t, _, ht⟩ := hR.covering (Function.Embedding.ofIsEmpty : Fin 0 ↪ M)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ht
  exact KnightRealization.noProlongation_of_topFree hαβ htop t p hp

end VaughtConjecture.Knight.KnightRealization
