module

public import RequestProject.OrderNerveSingularCarriers


@[expose] public section

namespace FiniteChains.Comb
open scoped Classical

section

variable {P : Type*} [PartialOrder P]

/-- The lower of a vertex and a fixed comparable center. -/
noncomputable def orderComparableLower (v p : P) :=
  if p ≤ v then p else v

theorem orderComparableLower_monotone (v : P) :
    Monotone (orderComparableLower v) := by
  intro a b hab
  by_cases ha : a ≤ v
  · by_cases hb : b ≤ v
    · simp_all [orderComparableLower, ha, hb]
    · simp [orderComparableLower, ha, hb]
  · have hb : ¬ b ≤ v := fun h => ha (hab.trans h)
    simp [orderComparableLower, ha, hb]

theorem orderComparableLower_le_center (v p : P) :
    orderComparableLower v p ≤ v := by
  by_cases h : p ≤ v
  · simp [orderComparableLower, h]
  · simp [orderComparableLower, h]

section

variable (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p)
include v hv

theorem orderComparableLower_le_self (p : P) : orderComparableLower v p ≤ p := by
  by_cases h : p ≤ v
  · simp [orderComparableLower, h]
  · simpa [orderComparableLower, h] using (hv p).resolve_left h

/-- A universally comparable vertex gives explicit augmented nerve fillings
in every degree via the already proved prism contraction. -/
theorem orderNerve_cycle_bounds_of_comparable
    {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) (hcycle : Nerve.bdry c = 0) :
    ∃ b ∈ Nerve.Inc P, Nerve.bdry b = c :=
  Nerve.exists_bdry_eq_of_cycle _ v
    (orderComparableLower_monotone v) (orderComparableLower_le_self v hv)
    (orderComparableLower_le_center v) hc hcycle

end

end

end FiniteChains.Comb
