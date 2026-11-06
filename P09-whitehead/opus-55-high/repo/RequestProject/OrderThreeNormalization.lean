import RequestProject.OrderNerveCellMaps
import RequestProject.Tac
noncomputable section


/-! Degree-three normalization of the full weak order nerve. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictOrdTet (P : Type u) [PartialOrder P] :=
  {t : P × P × P × P // t.1 < t.2.1 ∧ t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2}

def strictOrdTetBoundary (t : StrictOrdTet P) : StrictOrdTri P →₀ ℤ :=
  Finsupp.single ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ 1 +
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ 1

def strictOrdBoundary3 : (StrictOrdTet P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTri P →₀ ℤ) := Finsupp.linearCombination ℤ strictOrdTetBoundary

def normalizeOrdTetrahedron (t : OrdTet P) : StrictOrdTet P →₀ ℤ := by
  classical
  exact if h : t.1.1 < t.1.2.1 ∧ t.1.2.1 < t.1.2.2.1 ∧ t.1.2.2.1 < t.1.2.2.2 then
    Finsupp.single ⟨t.1, h⟩ 1 else 0

def normalizeOrdChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ]
    (StrictOrdTet P →₀ ℤ) := Finsupp.linearCombination ℤ normalizeOrdTetrahedron

/-- Repeated-vertex tetrahedra normalize compatibly with every boundary face. -/
theorem normalizeOrdTetBoundary (t : OrdTet P) :
    normalizeOrdChain2 (ordTetBoundary t) =
      strictOrdBoundary3 (normalizeOrdTetrahedron t) := by
  classical
  obtain ⟨⟨a, b, c, d⟩, hab, hbc, hcd⟩ := t
  by_cases he1 : a = b
  · subst b
    simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
      normalizeOrdTetrahedron]
  · by_cases he2 : b = c
    · subst c
      simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
        normalizeOrdTetrahedron]
    · by_cases he3 : c = d
      · subst d
        simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
          normalizeOrdTetrahedron]
      · have hab' := lt_of_le_of_ne hab he1
        have hbc' := lt_of_le_of_ne hbc he2
        have hcd' := lt_of_le_of_ne hcd he3
        simp [ordTetBoundary, normalizeOrdChain2, normalizeOrdTriangle,
          normalizeOrdTetrahedron, strictOrdBoundary3, strictOrdTetBoundary,
          hab', hbc', hcd', hab'.trans hbc', hbc'.trans hcd']

/-- Normalization commutes with the full three-boundary on arbitrary finite chains. -/
theorem normalizeOrdChain2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 c) = strictOrdBoundary3 (normalizeOrdChain3 c) := by
  lin_ind c t n =>
      simp [ordBoundary3, Finsupp.linearCombination_single, map_smul, normalizeOrdTetBoundary, normalizeOrdChain3]

/-- A full weak-nerve boundary normalizes to an actual strict three-boundary. -/
theorem normalized_boundary3 c
    (h : ∃ y, ordBoundary3 y = c) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = normalizeOrdChain2 c := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨normalizeOrdChain3 y, (normalizeOrdChain2_ordBoundary3 y).symm⟩
