module

public import RequestProject.StrictTriangleBoundary

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

variable (v : P)

def StrictBelow := {p : P // p < v}

instance : PartialOrder (StrictBelow v) := Subtype.partialOrder _

def strictRayEdge (e : StrictOrdEdge P) : StrictBelow v →₀ ℤ := by
  classical
  exact if h : e.1.2 = v then Finsupp.single ⟨e.1.1, h ▸ e.2⟩ 1 else 0

def strictRayChain :=
  Finsupp.linearCombination ℤ (strictRayEdge v)

def strictTopLinkTriangle (t : StrictOrdTri P) :
    StrictOrdEdge (StrictBelow v) →₀ ℤ := by
  classical
  exact if h : t.1.2.2 = v then Finsupp.single
    ⟨(⟨t.1.1, h ▸ t.2.1.trans t.2.2⟩, ⟨t.1.2.1, h ▸ t.2.2⟩), t.2.1⟩ 1 else 0

def strictTopLinkChain :=
  Finsupp.linearCombination ℤ (strictTopLinkTriangle v)

variable (hm : ∀ p, v ≤ p → p = v) (c : StrictOrdTri P →₀ ℤ)
include hm

/-- At a maximal vertex, extracting cone rays from the actual triangle boundary
is the actual boundary of the extracted link edge chain. -/
theorem strictTopLink_boundary :
    strictRayChain v (bdry2 (strictOrderCx P) c) =
      bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm _ (he ▸ t.2.2.le)
      grind
    rw [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.2.2 = v
    · simp [strictRayChain, strictRayEdge, strictTopLinkChain, strictTopLinkTriangle,
        strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, hmid, ht,
        bdry1, strictOrderCx, smul_sub]
    · simp [strictRayChain, strictRayEdge, strictTopLinkChain, strictTopLinkTriangle,
        strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, hmid, ht]

/-- Genuine cover two-cycles give genuine one-cycles in the link of each maximal apex. -/
theorem strictTopLink_cycle (hc : bdry2 (strictOrderCx P) c = 0) :
    bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) = 0 := by
  rw [← strictTopLink_boundary v hm, hc, map_zero]

end FiniteChains.Comb
