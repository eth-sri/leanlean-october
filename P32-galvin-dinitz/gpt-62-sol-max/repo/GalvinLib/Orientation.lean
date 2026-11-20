/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GalvinLib.GaleShapley
public import Konig.Basic

/-! # Galvin’s orientation from a proper edge colouring -/

public section

namespace Galvin

open Finset Function

/-- Galvin's list colouring argument for edges given by their ordered endpoints. -/
theorem listsOfMatrix {V E C : Type*} [Fintype V] (l r : E → V)
    (hinj : Injective fun x => (l x, r x)) {d : ℕ} (A : V → V → ℕ)
    (hr : ∀ i, ∑ j, A i j = d) (hc : ∀ j, ∑ i, A i j = d)
    (he : ∀ x, 0 < A (l x) (r x)) (L : E → Finset C) (hL : ∀ x, d ≤ #(L x)) :
    ∃ f : E → C, (∀ x, f x ∈ L x) ∧ ∀ x y, Incident l r x y → f x ≠ f y := by
  classical
  let _ := Fintype.ofInjective _ hinj
  obtain ⟨p, hp⟩ := Konig.cover d A hr hc
  choose φ hφ using fun x => hp _ _ (he x)
  have hproper (x y : E) (h : φ x = φ y)
      (hi : l x = l y ∨ r x = r y) : x = y := by
    grind [Injective, Equiv.apply_eq_iff_eq]
  let D := Pref l r φ (fun x => (φ x).rev)
  -- Out-neighbours have distinct colours, none equal to the current edge’s colour.
  obtain ⟨f, hf, hp⟩ := kernelList _ D (stable l r φ _ (by grind) (by grind [Fin.rev_inj]))
    univ L (by
      intro x _
      apply lt_of_lt_of_le _ (hL x)
      simpa only [Fintype.card_coe, Fintype.card_fin] using
        Fintype.card_lt_of_injective_not_surjective
          (fun y : ↥(univ.filter (D x)) => φ y) (by grind [Injective, Pref]) (by
            intro h
            specialize h (φ x)
            grind [Pref]))
  exact ⟨fun x => f ⟨x, mem_univ x⟩, fun _ => hf _, by grind⟩

end Galvin
