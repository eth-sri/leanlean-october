import Mathlib.Tactic

import RequestProject.OrderNerveSingularCarriers
import RequestProject.NerveSupport

namespace FiniteChains.Comb
open scoped Classical

variable {P : Type*}
/-- The lower of a vertex and a fixed comparable center. -/
noncomputable def orderComparableLower  [PartialOrder P] (v p : P)  :=
  if p ≤ v then p else v

theorem orderComparableLower_monotone  [PartialOrder P] (v : P) :
    Monotone (orderComparableLower v) := by
  intro a b hab
  by_cases ha : a ≤ v
  · classical aesop (add simp [orderComparableLower])
  · grind [orderComparableLower]

theorem orderComparableLower_le_center  [PartialOrder P] (v p : P) :
    orderComparableLower v p ≤ v := by aesop (add simp [orderComparableLower])

theorem orderComparableLower_le_self  [PartialOrder P] (v : P)
    (hv : ∀ p, p ≤ v ∨ v ≤ p) (p : P) : orderComparableLower v p ≤ p := by
  classical grind [orderComparableLower]

/-- A universally comparable vertex gives explicit augmented nerve fillings
in every degree via the already proved prism contraction. -/
abbrev orderNerve_cycle_bounds_of_comparable  [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p)
    {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) (hcycle : Nerve.bdry c = 0)  :=
  FiniteChains.Nerve.exists_bdry_eq_of_cycle (FiniteChains.Comb.orderComparableLower v) v
    (FiniteChains.Comb.orderComparableLower_monotone v) (FiniteChains.Comb.orderComparableLower_le_self v hv)
    (FiniteChains.Comb.orderComparableLower_le_center v) hc hcycle

/-- The carrier used for a small singular simplex is also acyclic on the
combinatorial side. Both exactness statements are proved independently. -/
theorem orderNerveSingularCarrier_nerve_acyclic {P : Type} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) :
    Nerve.AcyclicIn (orderNerveSingularCarrier σ) := by
  obtain ⟨v, hv⟩ := hσ
  have hv' := orderNerveSingularStarIndices_subset_carrier σ hv
  apply Nerve.acyclicIn_of_subtype (orderNerveSingularCarrier σ) ⟨v, hv'⟩
  intro c hc hcycle
  exact orderNerve_cycle_bounds_of_comparable
    (⟨v, hv'⟩ : orderNerveSingularCarrier σ) (fun p => p.property v hv) hc hcycle

end FiniteChains.Comb
