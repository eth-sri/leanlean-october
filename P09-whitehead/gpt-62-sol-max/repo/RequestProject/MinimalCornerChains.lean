module

public import RequestProject.OrderNormalizationHomotopy
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Relative chains at a minimal vertex of an actual order complex. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (p : P)

noncomputable def cornerTriangleEdge (t : OrdTri P) :
    (orderCx (Set.Ioi p)).E →₀ ℤ := by
  classical
  exact if h : t.1.1 = p ∧ p < t.1.2.1 then
    Finsupp.single ⟨(⟨t.1.2.1, h.2⟩, ⟨t.1.2.2, h.2.trans_le t.2.2⟩), t.2.2⟩ 1 else 0

noncomputable def cornerChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    ((orderCx (Set.Ioi p)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (cornerTriangleEdge p)

noncomputable def cornerTetrahedronTriangle (t : OrdTet P) :
    (orderCx (Set.Ioi p)).F →₀ ℤ := by
  classical
  exact if h : t.1.1 = p ∧ p < t.1.2.1 then
    Finsupp.single ⟨(⟨t.1.2.1, h.2⟩,
      ⟨t.1.2.2.1, h.2.trans_le t.2.2.1⟩,
      ⟨t.1.2.2.2, (h.2.trans_le t.2.2.1).trans_le t.2.2.2⟩), t.2.2⟩ 1 else 0

noncomputable def cornerChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    ((orderCx (Set.Ioi p)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (cornerTetrahedronTriangle p)

/-- Extracting a minimal corner from a three-boundary gives the negative boundary
of its actual upper-interval triangle chain. -/
theorem cornerTriangleEdge_ordTetBoundary
    (hp : ∀ v : P, v ≤ p → v = p) (t : OrdTet P) :
    cornerChain2 p (ordTetBoundary t) =
      -bdry2 (orderCx (Set.Ioi p)) (cornerTetrahedronTriangle p t) := by
  classical
  obtain ⟨⟨a, b, c, d⟩, hab, hbc, hcd⟩ := t
  by_cases ha : a = p
  · subst a
    by_cases hb : b = p
    · subst b
      simp [ordTetBoundary, tetrahedronBoundary, cornerChain2, cornerTriangleEdge,
        cornerTetrahedronTriangle, ordTetFace, ChainTet.face]
    · have hpb  := lt_of_le_of_ne hab (Ne.symm hb)
      have hpc := hpb.trans_le hbc
      simp only [ordTetBoundary, tetrahedronBoundary, cornerChain2, map_add, map_sub, Finsupp.linearCombination_single, ordTetFace, ChainTet.face]
      simp [cornerTriangleEdge,
        cornerTetrahedronTriangle, hpb, hpc, hb,
        Finsupp.linearCombination_single,
        bdry2, orderCx, pathChain]
      abel
  · have hb : b ≠ p := by
      intro h
      exact ha (hp a (h ▸ hab))
    simp [ordTetBoundary, tetrahedronBoundary, cornerChain2, cornerTriangleEdge,
      cornerTetrahedronTriangle, ha, hb, ordTetFace, ChainTet.face]

theorem cornerChain2_ordBoundary3 (hp : ∀ v : P, v ≤ p → v = p)
    (c : OrdTet P →₀ ℤ) :
    cornerChain2 p (ordBoundary3 c) = -bdry2 (orderCx (Set.Ioi p)) (cornerChain3 p c) := by
  finsupp_basis c
  simp [ordBoundary3, Finsupp.linearCombination_single, cornerTriangleEdge_ordTetBoundary p hp, cornerChain3]

end FiniteChains.Comb
