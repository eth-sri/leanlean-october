module

public import RequestProject.OrderComparableCycleHomotopy
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Actual strict cycle fillings from a componentwise downward collapse. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizedStrictChain2_zero_of_comparable_equal (g : P → P) (hg : Monotone g)
    (he : ∀ {a b : P}, a ≤ b → g a = g b) (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 g hg c = 0 := by
  finsupp_basis c
  intro t
  rw [normalizedStrictChain2_single]
  have ht  := he t.2.1.le
  simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, ht]

/-- A downward monotone map that identifies comparable vertices gives genuine finite
strict three-fillings of all strict two-cycles, even when the poset is disconnected. -/
theorem strict_cycle_boundary_of_downward_collapse (g : P → P) (hg : Monotone g)
    (hle : ∀ x, g x ≤ x) (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c := by
  obtain ⟨y, hy⟩ := strict_cycle_comparable_boundary g id hg monotone_id hle c hc
  rw [normalizedStrictChain2_id, normalizedStrictChain2_zero_of_comparable_equal g hg he, sub_zero] at hy
  exact ⟨y, hy⟩

end FiniteChains.Comb
