/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows
public import VaughtConjecture.Knight.ReceivingCatalogueRanks

@[expose] public section

namespace VaughtConjecture.Knight.RungTableRendering

open Transform Value ExtOrd LadderScalarRendering

noncomputable section

variable {X : Type*} [Fintype X]

/-- A monotone finite round trip transports every occupied and unused level. -/
theorem level_decode (p : X → ExtOrd) {f g : ExtOrd → ExtOrd}
    (hf : Monotone f) (hg : Monotone g) (hfbot : f ⊥ = ⊥) (hgbot : g ⊥ = ⊥)
    (hinv : ∀ d, g (f (p d)) = p d) (C : ExtOrd) (i : ℕ) :
    g (LadderScalarRendering.level (values (fun d => f (p d))) C i) =
      LadderScalarRendering.level (values p) (g C) i := by
  classical
  obtain ⟨he, hinj⟩ := ReceivingCatalogueRanks.values_transport p hfbot hgbot hinv
  change g (level (values (f ∘ p)) C i) = _
  unfold level
  rw [show (values (f ∘ p)).card = (values p).card by rw [he, Finset.card_image_of_injOn hinj]]
  split_ifs
  · rfl
  · rw [he, Finset.filter_image, Finset.sup_image,
      Finset.apply_sup_eq_sup_comp_of_linearOrder g hg hgbot]
    apply Finset.sup_congr
    · apply Finset.filter_congr
      intro x hx
      obtain ⟨_, d, rfl⟩ := mem_values.mp hx
      rw [← he]
      change fieldRank (fun d => f (p d)) d ≤ i ↔ fieldRank p d ≤ i
      rw [ReceivingCatalogueRanks.fieldRank_of_leftInverse p hf hg hfbot hgbot hinv]
    · intro x hx
      obtain ⟨_, d, rfl⟩ := mem_values.mp ((Finset.mem_filter.mp hx).1)
      exact hinv d

end

end VaughtConjecture.Knight.RungTableRendering
