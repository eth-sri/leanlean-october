/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Logic.Function.Defs

@[expose] public section

namespace VaughtConjecture.CapCompatibleExtension

variable {X Y Γ : Type*} (restrict : X → Y)
  (capX : Γ → X → X) (capY : Γ → Y → Y)

/-- Any extension preserves all compatible caps against all ambients. -/
theorem preserves_all (hinj : Function.Injective restrict)
    (hcomm : ∀ γ x, restrict (capX γ x) = capY γ (restrict x))
    {p : Y} {z : X} (hz : restrict z = p) :
    ∀ γ q, capY γ p = capY γ (restrict q) → capX γ z = capX γ q := by grind

/-- Choose the extension once, independently of both the cap and the ambient. -/
theorem exists_extension (hr : Function.Bijective restrict)
    (hcomm : ∀ γ x, restrict (capX γ x) = capY γ (restrict x)) (p : Y) :
    ∃ z : X, restrict z = p ∧
      ∀ γ q, capY γ p = capY γ (restrict q) → capX γ z = capX γ q := by
  obtain ⟨z, hz⟩ := hr.2 p
  exact ⟨z, hz, preserves_all restrict capX capY hr.1 hcomm hz⟩

end VaughtConjecture.CapCompatibleExtension
