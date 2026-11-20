module

public import RequestProject.CellComplex
public import RequestProject.FinsuppBasis

@[expose] public section

namespace FiniteChains.Comb

/-- Each endpoint contributes its signed pushforward along the incidence map. -/
theorem bdry1_eq_mapDomain {X : Complex2} (c : X.E →₀ ℤ) :
    bdry1 X c = Finsupp.mapDomain X.tgt c - Finsupp.mapDomain X.src c := by
  finsupp_basis c
  simp

private theorem mapDomain_pair {E V : Type*} {f : E → V} {v : V} {a b : E} (hab : a ≠ b)
    (h : ∀ e, f e = v ↔ e = a ∨ e = b) (c : E →₀ ℤ) :
    Finsupp.mapDomain f c v = c a + c b := by
  classical
  finsupp_basis c
  intro e
  simp only [Finsupp.mapDomain_single, Finsupp.single_apply, h]
  split_ifs <;> grind

/-- A vertex with two incoming edges and no outgoing edges receives their sum. -/
theorem bdry1_pair_target {X : Complex2} {v : X.V} {a b : X.E} (hab : a ≠ b)
    (ht : ∀ e, X.tgt e = v ↔ e = a ∨ e = b) (hs : ∀ e, X.src e ≠ v) (c : X.E →₀ ℤ) :
    bdry1 X c v = c a + c b := by
  rw [bdry1_eq_mapDomain, Finsupp.sub_apply, mapDomain_pair hab ht,
    Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Set.mem_range] using hs), sub_zero]

/-- At a vertex with just two outgoing edges the contributions have negative sign. -/
theorem bdry1_pair_source {X : Complex2} {v : X.V} {a b : X.E} (hab : a ≠ b)
    (hs : ∀ e, X.src e = v ↔ e = a ∨ e = b) (ht : ∀ e, X.tgt e ≠ v) (c : X.E →₀ ℤ) :
    bdry1 X c v = -c a - c b := by
  rw [bdry1_eq_mapDomain, Finsupp.sub_apply, mapDomain_pair hab hs,
    Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Set.mem_range] using ht)]
  ring

end FiniteChains.Comb
