import RequestProject.StrictTriangleBoundary
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictBelow (v : P) := {p : P // p < v}

instance (v : P) : PartialOrder (StrictBelow v) := Subtype.partialOrder _

def strictRayEdge (v : P) (e : StrictOrdEdge P) : StrictBelow v →₀ ℤ := by
  classical
  exact if h : e.1.2 = v then Finsupp.single ⟨e.1.1, h ▸ e.2⟩ 1 else 0

def strictRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictBelow v →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictRayEdge v)

def strictTopLinkTriangle (v : P) (t : StrictOrdTri P) :
    StrictOrdEdge (StrictBelow v) →₀ ℤ := by
  classical
  exact if h : t.1.2.2 = v then Finsupp.single
    ⟨(⟨t.1.1, h ▸ t.2.1.trans t.2.2⟩, ⟨t.1.2.1, h ▸ t.2.2⟩), t.2.1⟩ 1 else 0

def strictTopLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictBelow v) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictTopLinkTriangle v)

/-- At a maximal vertex, extracting cone rays from the actual triangle boundary
is the actual boundary of the extracted link edge chain. -/
theorem strictTopLink_boundary v (hm : ∀ p, v ≤ p → p = v)
    (c : StrictOrdTri P →₀ ℤ) :
    strictRayChain v (bdry2 (strictOrderCx P) c) =
      bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) := by
  classical
  lin_ind c t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm t.1.2.2 (he ▸ t.2.2.le)
      grind
    rw [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.2.2 = v
    · simp [strictRayChain, strictRayEdge, strictTopLinkChain, strictTopLinkTriangle,
        strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, hmid, ht,
        bdry1, strictOrderCx, smul_sub]
    · simp [strictRayChain, strictRayEdge, strictTopLinkChain, strictTopLinkTriangle,
        strictTriangleEdge01, strictTriangleEdge12, strictTriangleEdge02, hmid, ht]

/-- Genuine cover two-cycles give genuine one-cycles in the link of each maximal apex. -/
theorem strictTopLink_cycle v (hm : ∀ p, v ≤ p → p = v)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    bdry1 (strictOrderCx (StrictBelow v)) (strictTopLinkChain v c) = 0 := by
  rw [← strictTopLink_boundary v hm, hc, map_zero]
