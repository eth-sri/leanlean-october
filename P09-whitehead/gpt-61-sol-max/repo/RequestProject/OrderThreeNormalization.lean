import Mathlib.Tactic

import RequestProject.OrderNerveCellMaps

/-! Degree-three normalization of the full weak order nerve. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P]

def StrictOrdTet (P : Type u) [PartialOrder P] :=
  {t : P × P × P × P // t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2}

noncomputable def strictOrdTetBoundary (t : StrictOrdTet P) : StrictOrdTri P →₀ ℤ :=
  Finsupp.single ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ 1 +
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ 1

noncomputable def strictOrdBoundary3 : (StrictOrdTet P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri P →₀ ℤ) := Finsupp.linearCombination ℤ strictOrdTetBoundary

noncomputable def normalizeOrdTetrahedron (t : OrdTet P) : StrictOrdTet P →₀ ℤ := by
  classical
  exact if h : t.1.1 < t.1.2.1 ∧ t.1.2.1 < t.1.2.2.1 ∧ t.1.2.2.1 < t.1.2.2.2 then
    Finsupp.single ⟨t.1, h⟩ 1 else 0

noncomputable def normalizeOrdChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTet P →₀ ℤ) := Finsupp.linearCombination ℤ normalizeOrdTetrahedron

/-- Repeated-vertex tetrahedra normalize compatibly with every boundary face. -/
theorem normalizeOrdTetBoundary (t : OrdTet P) :
    normalizeOrdChain2 (ordTetBoundary t) =
      strictOrdBoundary3 (normalizeOrdTetrahedron t) := by
  classical
  obtain ⟨⟨a, b, c, d⟩, hab, hbc, hcd⟩ := t
  by_cases he1 : a = b
  · simp_all [ordTetBoundary, normalizeOrdTriangle, normalizeOrdTetrahedron]
  · by_cases he2 : b = c
    · simp_all [ordTetBoundary, normalizeOrdTriangle, normalizeOrdTetrahedron]
    · by_cases he3 : c = d
      · simp_all [ordTetBoundary, normalizeOrdTriangle, normalizeOrdTetrahedron]
      · have hab'  := lt_of_le_of_ne hab he1
        have hbc'  := lt_of_le_of_ne hbc he2
        have hcd'  := lt_of_le_of_ne hcd he3
        simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
          normalizeOrdTetrahedron, strictOrdBoundary3, strictOrdTetBoundary,
          hab', hbc', hcd', hab'.trans hbc', hbc'.trans hcd']

/-- Normalization commutes with the full three-boundary on arbitrary finite chains. -/
theorem normalizeOrdChain2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 c) = strictOrdBoundary3 (normalizeOrdChain3 c) := by
  induction c using Finsupp.induction_linear <;> simp_all [ordBoundary3, normalizeOrdTetBoundary, normalizeOrdChain3]

/-- A full weak-nerve boundary normalizes to an actual strict three-boundary. -/
theorem normalized_boundary3 (c : OrdTri P →₀ ℤ)
    (h : ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = normalizeOrdChain2 c := by
  aesop (add simp [normalizeOrdChain2_ordBoundary3])

end FiniteChains.Comb
