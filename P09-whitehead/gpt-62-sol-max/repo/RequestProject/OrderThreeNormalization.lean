module

public import RequestProject.OrderNerveCellMaps
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Degree-three normalization of the full weak order nerve. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictOrdTet (P : Type u) [PartialOrder P] := ChainTet ((· < ·) : P → P → Prop)

/-- A strict rank in `{0,1,2}` excludes strict tetrahedra. -/
theorem strictOrdTet_isEmpty_of_rank (r : P → ℕ) (hr : StrictMono r) (hb : ∀ x, r x ≤ 2) :
    IsEmpty (StrictOrdTet P) :=
  ⟨fun t => by
    have := hr t.2.1
    have := hr t.2.2.1
    have := hr t.2.2.2
    have := hb t.1.2.2.2
    omega⟩

noncomputable def strictOrdTetBoundary (t : StrictOrdTet P) : StrictOrdTri P →₀ ℤ :=
  tetrahedronBoundary (ChainTet.face ⟨fun _ _ _ => lt_trans⟩ t)

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
  · subst b
    simp [ordTetBoundary, tetrahedronBoundary, normalizeOrdTriangle,
      normalizeOrdTetrahedron, ordTetFace, ChainTet.face]
  · by_cases he2 : b = c
    · subst c
      simp [ordTetBoundary, tetrahedronBoundary, normalizeOrdTriangle,
        normalizeOrdTetrahedron, ordTetFace, ChainTet.face]
    · by_cases he3 : c = d
      · subst d
        simp [ordTetBoundary, tetrahedronBoundary, normalizeOrdTriangle,
          normalizeOrdTetrahedron, ordTetFace, ChainTet.face]
      · have hab'  := lt_of_le_of_ne hab he1
        have hbc'  := lt_of_le_of_ne hbc he2
        have hcd'  := lt_of_le_of_ne hcd he3
        simp [ordTetBoundary, tetrahedronBoundary, normalizeOrdTriangle,
          normalizeOrdTetrahedron, strictOrdBoundary3, strictOrdTetBoundary,
          hab', hbc', hcd', hab'.trans hbc', hbc'.trans hcd', ordTetFace, ChainTet.face]

/-- Normalization commutes with the full three-boundary on arbitrary finite chains. -/
theorem normalizeOrdChain2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 c) = strictOrdBoundary3 (normalizeOrdChain3 c) := by
  finsupp_basis c
  simp [ordBoundary3, Finsupp.linearCombination_single, normalizeOrdTetBoundary, normalizeOrdChain3]

theorem normalizeOrdBoundary3_eq_zero [IsEmpty (StrictOrdTet P)] (c : OrdTet P →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 c) = 0 := by
  rw [normalizeOrdChain2_ordBoundary3, Subsingleton.elim (normalizeOrdChain3 c) 0, map_zero]

/-- A full weak-nerve boundary normalizes to an actual strict three-boundary. -/
theorem normalized_boundary3 (c : OrdTri P →₀ ℤ)
    (h : ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = normalizeOrdChain2 c := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨normalizeOrdChain3 y, (normalizeOrdChain2_ordBoundary3 y).symm⟩

end FiniteChains.Comb
