module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

def quadParity (f : Fin 4 → Bool) : Bool := ((f 0 ^^ f 1) ^^ f 2) ^^ f 3

/-- In a diamond, a subset closed under sharing that diamond either contains
every ambient cut edge or contains none. It therefore inherits even parity.
The four slots need not name distinct edges. -/
theorem quadParity_closed_subset (F C : Fin 4 → Bool)
    (hsub : ∀ i, F i = true → C i = true)
    (hclosed : ∀ i j, F i = true → C j = true → F j = true)
    (hC : quadParity C = false) : quadParity F = false := by
  by_cases h : ∃ i, F i = true
  · obtain ⟨i, hi⟩ := h
    have he : F = C := by
      funext j
      have hc := hclosed i j hi
      cases hf : F j <;> cases hc : C j <;> simp_all
    simp_all
  · have he : F = fun _ => false := by
      grind
    aesop

end HordijkSteelThreshold
