/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.OrdinalUtil
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

universe u v w

open Cardinal Ordinal Set

namespace InfinitaryLogic

variable {X : Type u}

/-- **Countable complements from countable successor losses and limit continuity.**  No
monotonicity of `D` is assumed; the limit hypothesis is necessary. -/
theorem compl_countable_of_loss (D : Ordinal.{0} → Set X) (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < (aleph 1).ord → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ l, Order.IsSuccLimit l → l < (aleph 1).ord → (⋂ ξ < l, D ξ) ⊆ D l) :
    ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable := by
  intro β
  induction β using WellFoundedLT.induction with
  | _ β ih =>
    intro hβ
    rcases Ordinal.zero_or_succ_or_isSuccLimit β with rfl | ⟨ξ, rfl⟩ | hl
    · simp_all
    · have hξ : ξ < (aleph 1).ord := lt_trans (Order.lt_succ ξ) hβ
      refine ((ih ξ (Order.lt_succ ξ) hξ).union (hsucc ξ hξ)).mono fun x hx => ?_
      rw [Order.succ_eq_add_one] at hx
      by_cases hxξ : x ∈ D ξ
      · exact Or.inr ⟨hxξ, hx⟩
      · exact Or.inl hxξ
    · refine (Set.Countable.biUnion (setCountable_Iio_of_lt_omega1 β (by rwa [← ord_aleph])) fun ξ hξ =>
        ih ξ hξ (lt_trans hξ hβ)).mono fun x hx => ?_
      by_contra hall
      apply hx
      apply hlim β hl hβ
      simp_all

end InfinitaryLogic
