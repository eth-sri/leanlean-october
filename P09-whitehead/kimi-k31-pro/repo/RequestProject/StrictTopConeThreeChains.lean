module

public import RequestProject.Oriented

public import RequestProject.StrictTopConeChains

@[expose] public section

backwardOptions



/-! Genuine strict tetrahedron fans, with their alternating boundary. -/

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c)

def strictTopConeTriangleTetrahedron (t : (strictOrderCx P).F) : StrictOrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2, c), hf t.2.1, hf t.2.2, hc _⟩

noncomputable def strictTopConeTriangleChain : ((strictOrderCx P).F →₀ ℤ) →ₗ[ℤ] (StrictOrdTet Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (strictTopConeTriangleTetrahedron f hf c hc)

/-- The sign of the upper cone is fixed by the actual alternating tetrahedron boundary. -/
theorem strictTopConeTriangleTetrahedron_boundary (t : (strictOrderCx P).F) :
    strictOrdTetBoundary (strictTopConeTriangleTetrahedron f hf c hc t) =
      strictTopConeEdgeChain f hf c hc (bdry2 (strictOrderCx P) (Finsupp.single t 1)) -
        Finsupp.single ((strictOrderCxMap f hf).onF t) 1 := by
  rw [bdry2_single (X := strictOrderCx P)]
  simp only [one_smul]
  simp only [pathChain, strictOrderCx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp [map_add, map_neg, Finsupp.linearCombination_single, strictOrdTetBoundary, strictTopConeTriangleTetrahedron, strictTopConeEdgeChain, strictTopConeEdgeTriangle,
    bdry2, strictOrderCx, strictOrderCxMap, pathChain]
  rwd [map_add, map_add, map_neg]
  rwd [Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  simp only [one_smul]
  abel

theorem strictTopConeTriangleChain_boundary (z : (strictOrderCx P).F →₀ ℤ) :
    strictOrdBoundary3 (strictTopConeTriangleChain f hf c hc z) =
      strictTopConeEdgeChain f hf c hc (bdry2 (strictOrderCx P) z) - chain2 (strictOrderCxMap f hf) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single t n =>
      change strictOrdBoundary3 (Finsupp.mapDomain (strictTopConeTriangleTetrahedron f hf c hc)
        (Finsupp.single t n)) = _
      rw [Finsupp.mapDomain_single, strictOrdBoundary3, Finsupp.linearCombination_single,
        strictTopConeTriangleTetrahedron_boundary, smul_sub]
      change _ = _ - Finsupp.mapDomain (strictOrderCxMap f hf).onF (Finsupp.single t n)
      rw [Finsupp.mapDomain_single]
      simp [bdry2]

end FiniteChains.Comb
