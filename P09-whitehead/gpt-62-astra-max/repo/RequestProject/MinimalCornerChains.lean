module

public import RequestProject.OrderNormalizationHomotopy

@[expose] public section

/-! Relative chains at a minimal vertex of an actual order complex. -/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (p : P)

def cornerTriangleEdge (t : OrdTri P) :
    (orderCx (Set.Ioi p)).E →₀ ℤ := by
  classical
  exact if h : t.1.1 = p ∧ p < t.1.2.1 then
    Finsupp.single ⟨(⟨t.1.2.1, h.2⟩, ⟨t.1.2.2, h.2.trans_le t.2.2⟩), t.2.2⟩ 1 else 0

def cornerChain2 :=
  Finsupp.linearCombination ℤ (cornerTriangleEdge p)

def cornerTetrahedronTriangle (t : OrdTet P) :
    (orderCx (Set.Ioi p)).F →₀ ℤ := by
  classical
  exact if h : t.1.1 = p ∧ p < t.1.2.1 then
    Finsupp.single ⟨(⟨t.1.2.1, h.2⟩,
      ⟨t.1.2.2.1, h.2.trans_le t.2.2.1⟩,
      ⟨t.1.2.2.2, (h.2.trans_le t.2.2.1).trans_le t.2.2.2⟩), t.2.2⟩ 1 else 0

def cornerChain3 :=
  Finsupp.linearCombination ℤ (cornerTetrahedronTriangle p)

variable (hp : ∀ v : P, v ≤ p → v = p)
include hp

/-- Extracting a minimal corner from a three-boundary gives the negative boundary
of its actual upper-interval triangle chain. -/
theorem cornerTriangleEdge_ordTetBoundary (t : OrdTet P) :
    cornerChain2 p (relTetBoundary t) =
      -bdry2 _ (cornerTetrahedronTriangle p t) := by
  classical
  obtain ⟨⟨a, b, c, d⟩, hab, hbc, hcd⟩ := t
  by_cases ha : a = p
  · subst a
    by_cases hb : b = p
    · simp_all [relTetBoundary, cornerChain2, cornerTriangleEdge, cornerTetrahedronTriangle]
    · have hpb := lt_of_le_of_ne hab (Ne.symm hb)
      simp only [relTetBoundary, cornerChain2, map_add, map_sub, Finsupp.linearCombination_single]
      simp [relTetBoundary, cornerChain2, cornerTriangleEdge,
        cornerTetrahedronTriangle, hpb, (hpb.trans_le hbc), hb,
        map_add, map_sub, map_smul, Finsupp.linearCombination_single,
        bdry2, orderCx, pathChain]
      abel
  · have hb : b ≠ p := by
      intro h
      simp_all
    simp [relTetBoundary, cornerChain2, cornerTriangleEdge,
      cornerTetrahedronTriangle, ha, hb]

theorem cornerChain2_ordBoundary3
    (c : OrdTet P →₀ ℤ) :
    cornerChain2 p (ordBoundary3 c) = -bdry2 _ (cornerChain3 p c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add, neg_add]
  | single t n =>
      simp_all [ordBoundary3, Finsupp.linearCombination_single, map_smul, cornerTriangleEdge_ordTetBoundary, cornerChain3, smul_neg]

end FiniteChains.Comb
