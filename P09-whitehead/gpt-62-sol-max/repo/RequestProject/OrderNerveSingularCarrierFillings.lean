module

public import RequestProject.OrderNerveSingularCarriers
public import RequestProject.NerveSupport

@[expose] public section

namespace FiniteChains.Comb
open scoped Classical

/-- The lower of a vertex and a fixed comparable center. -/
noncomputable def orderComparableLower {P : Type*} [PartialOrder P] (v p : P) : P :=
  if p ≤ v then p else v

theorem orderComparableLower_monotone {P : Type*} [PartialOrder P] (v : P) :
    Monotone (orderComparableLower v) := by
  intro a b hab
  grind +locals

theorem orderComparableLower_le_center {P : Type*} [PartialOrder P] (v p : P) :
    orderComparableLower v p ≤ v := by
  by_cases h : p ≤ v
  · simp [orderComparableLower, h]
  · simp [orderComparableLower, h]

theorem orderComparableLower_le_self {P : Type*} [PartialOrder P] (v : P)
    (hv : ∀ p, p ≤ v ∨ v ≤ p) (p : P) : orderComparableLower v p ≤ p := by
  grind +locals

/-- A universally comparable vertex gives explicit augmented nerve fillings
in every degree via the already proved prism contraction. -/
theorem orderNerve_cycle_bounds_of_comparable {P : Type*} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p)
    {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) (hcycle : Nerve.bdry c = 0) :
    ∃ b ∈ Nerve.Inc P, Nerve.bdry b = c :=
  Nerve.exists_bdry_eq_of_cycle (orderComparableLower v) v
    (orderComparableLower_monotone v) (orderComparableLower_le_self v hv)
    (orderComparableLower_le_center v) hc hcycle


end FiniteChains.Comb
