module

public import RequestProject.CellularChainMapZero
public import RequestProject.FinsuppBasis
public import RequestProject.OrderThreeNormalization

@[expose] public section

/-! Upper cones in the genuine strict simplicial cell model. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c)

def strictTopConeEdgeTriangle (e : (strictOrderCx P).E) : (strictOrderCx Q).F :=
  ⟨(f e.1.1, f e.1.2, c), hf e.2, hc _⟩

noncomputable def strictTopConeEdgeChain : ((strictOrderCx P).E →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx Q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (strictTopConeEdgeTriangle f hf c hc e) 1)

def strictTopConeRadialEdge (x : P) : (strictOrderCx Q).E := ⟨(f x, c), hc x⟩

noncomputable def strictTopConeRadialChain : (P →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx Q).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (strictTopConeRadialEdge f c hc x) 1)

theorem strictTopConeEdgeTriangle_boundary (e : (strictOrderCx P).E) :
    bdry2 (strictOrderCx Q) (Finsupp.single (strictTopConeEdgeTriangle f hf c hc e) 1) =
      Finsupp.single ((strictOrderCxMap f hf).onE e) 1 +
        Finsupp.single (strictTopConeRadialEdge f c hc e.1.2) 1 -
        Finsupp.single (strictTopConeRadialEdge f c hc e.1.1) 1 := by
  simp [bdry2, strictTopConeEdgeTriangle, strictTopConeRadialEdge,
    strictOrderCx, strictOrderCxMap, pathChain]
  abel

theorem strictTopConeEdgeChain_boundary (z : (strictOrderCx P).E →₀ ℤ) :
    bdry2 (strictOrderCx Q) (strictTopConeEdgeChain f hf c hc z) =
      chain1 (strictOrderCxMap f hf) z +
        strictTopConeRadialChain f c hc (bdry1 (strictOrderCx P) z) := by
  finsupp_basis z
  intro e
  rw [strictTopConeEdgeChain, Finsupp.linearCombination_single, map_smul,
    strictTopConeEdgeTriangle_boundary]
  change _ = Finsupp.mapDomain (strictOrderCxMap f hf).onE (Finsupp.single e 1) + _
  rw [Finsupp.mapDomain_single]
  simp [strictTopConeRadialChain, bdry1, smul_add, smul_sub]
  abel

/-- Every mapped strict edge cycle has an explicit nondegenerate upper-cone filling. -/
theorem strictTopConeEdgeChain_cycle_boundary (z : (strictOrderCx P).E →₀ ℤ)
    (hz : bdry1 (strictOrderCx P) z = 0) :
    bdry2 (strictOrderCx Q) (strictTopConeEdgeChain f hf c hc z) =
      chain1 (strictOrderCxMap f hf) z := by
  rw [strictTopConeEdgeChain_boundary, hz, map_zero, add_zero]

/-- Every triangle of the upper fan ends at its actual cone vertex. -/
theorem strictTopConeEdgeChain_eq_zero_off_top (z : (strictOrderCx P).E →₀ ℤ)
    (t : (strictOrderCx Q).F) (ht : t.1.2.2 ≠ c) :
    strictTopConeEdgeChain f hf c hc z t = 0 := by
  classical
  finsupp_basis z
  intro e
  have hne : strictTopConeEdgeTriangle f hf c hc e ≠ t := by
    intro h
    exact ht (congrArg (·.1.2.2) h).symm
  simp [strictTopConeEdgeChain, hne]

end FiniteChains.Comb
