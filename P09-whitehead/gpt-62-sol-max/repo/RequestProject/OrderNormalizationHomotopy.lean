module

public import RequestProject.StrictOrderChains
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Explicit degree-two normalization homotopy in the full weak order nerve. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- Four vertices and the three consecutive incidences, for weak or strict chains. -/
abbrev ChainTet {P : Type u} (r : P → P → Prop) :=
  {t : P × P × P × P // r t.1 t.2.1 ∧ r t.2.1 t.2.2.1 ∧ r t.2.2.1 t.2.2.2}

abbrev ChainTet.face {P : Type u} {r : P → P → Prop} (h : IsTrans P r)
    (t : ChainTet r) (i : Fin 4) : ChainTri r :=
  match i.val with
  | 0 => ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩
  | 1 => ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), h.trans _ _ _ t.2.1 t.2.2.1, t.2.2.2⟩
  | 2 => ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, h.trans _ _ _ t.2.2.1 t.2.2.2⟩
  | _ => ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩

noncomputable def tetrahedronBoundary {E : Type u} (f : Fin 4 → E) : E →₀ ℤ :=
  Finsupp.single (f 0) 1 - Finsupp.single (f 1) 1 +
    Finsupp.single (f 2) 1 - Finsupp.single (f 3) 1

theorem mapDomain_tetrahedronBoundary {E F : Type u} (f : E → F) (v : Fin 4 → E) :
    Finsupp.mapDomain f (tetrahedronBoundary v) = tetrahedronBoundary (f ∘ v) := by
  simp [tetrahedronBoundary, Finsupp.mapDomain_sub, Finsupp.mapDomain_add]

def OrdTet (P : Type u) [PartialOrder P] := ChainTet ((· ≤ ·) : P → P → Prop)

abbrev ordTetFace (t : OrdTet P) : Fin 4 → OrdTri P :=
  ChainTet.face ⟨fun _ _ _ => le_trans⟩ t

noncomputable def ordTetBoundary (t : OrdTet P) : OrdTri P →₀ ℤ :=
  tetrahedronBoundary (ordTetFace t)

noncomputable def ordBoundary3 : (OrdTet P →₀ ℤ) →ₗ[ℤ] (OrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ ordTetBoundary

/-- The alternating three-simplex boundary is a genuine cellular two-cycle. -/
theorem bdry2_ordTetBoundary (t : OrdTet P) :
    bdry2 (orderCx P) (ordTetBoundary t) = 0 := by
  simp only [ordTetBoundary, tetrahedronBoundary, map_sub, map_add, bdry2_single (X := orderCx P), one_smul, ordTetFace, ChainTet.face]
  simp [orderCx, pathChain]
  all_goals abel

theorem bdry2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    bdry2 (orderCx P) (ordBoundary3 c) = 0 := by
  finsupp_basis c
  intro t
  simp only [ordBoundary3, Finsupp.linearCombination_single, map_smul,
    bdry2_ordTetBoundary, smul_zero]

noncomputable def ordNormalizationHomotopy1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ]
    (OrdTri P →₀ ℤ) := by
  classical
  exact Finsupp.linearCombination ℤ (fun e =>
    if e.1.1 = e.1.2 then
      Finsupp.single ⟨(e.1.1, e.1.1, e.1.1), le_rfl, le_rfl⟩ 1 else 0)

noncomputable def ordNormalizationTriangleHomotopy (t : OrdTri P) : OrdTet P →₀ ℤ := by
  classical
  exact if h : t.1.1 = t.1.2.1 then
    Finsupp.single ⟨(t.1.1, t.1.1, t.1.1, t.1.2.2), le_rfl, le_rfl,
      h ▸ t.2.2⟩ 1 else if h' : t.1.2.1 = t.1.2.2 then
    -Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.1, t.1.2.1), t.2.1, le_rfl, le_rfl⟩ 1
    else 0

noncomputable def ordNormalizationHomotopy2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    (OrdTet P →₀ ℤ) :=
  Finsupp.linearCombination ℤ ordNormalizationTriangleHomotopy

/-- The discrepancy on a triangle is an explicit three-boundary plus the homotopy of
its edge boundary. This includes triangles with coinciding vertices. -/
theorem ordNormalization_triangle_identity (t : OrdTri P) :
    Finsupp.single t (1 : ℤ) -
      (Finsupp.mapDomain (strictOrderIncl P).onF (normalizeOrdTriangle t) : OrdTri P →₀ ℤ) =
    ordNormalizationHomotopy1 (pathChain ((orderCx P).att t)) +
      ordBoundary3 (ordNormalizationTriangleHomotopy t) := by
  classical
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  by_cases heab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary, tetrahedronBoundary, ordTetFace, ChainTet.face]
    · simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary, tetrahedronBoundary, ordTetFace, ChainTet.face]
  · by_cases hebc : b = c
    · subst c
      simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary, heab, tetrahedronBoundary, ordTetFace, ChainTet.face]
    · have hab'  := lt_of_le_of_ne hab heab
      have hbc'  := lt_of_le_of_ne hbc hebc
      simp [normalizeOrdTriangle, strictOrderIncl, ordNormalizationHomotopy1,
        pathChain, orderCx, ordNormalizationTriangleHomotopy, ordBoundary3,
        hab', hbc', heab, hebc, (hab'.trans hbc').ne]

/-- The inclusion on strict two-chains, as an integer-linear map. -/
noncomputable def ordStrictInclusion2 : (StrictOrdTri P →₀ ℤ) →ₗ[ℤ]
    (OrdTri P →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (strictOrderIncl P).onF

/-- The explicit normalization homotopy on arbitrary finitely supported two-chains. -/
theorem ordNormalization_chain_identity (c : OrdTri P →₀ ℤ) :
    c - ordStrictInclusion2 (normalizeOrdChain2 c) =
    ordNormalizationHomotopy1 (bdry2 (orderCx P) c) +
      ordBoundary3 (ordNormalizationHomotopy2 c) := by
  finsupp_basis c
  intro t
  rw [bdry2_single]
  have h := congrArg (fun x  => 1 • x)
    (ordNormalization_triangle_identity t)
  simpa [ordStrictInclusion2, ordNormalizationHomotopy2, smul_sub,
    smul_add, Finsupp.smul_single] using h

/-- A cellular two-cycle differs from its normalized image by an explicit three-boundary
in the full order nerve. No identification of the truncated second homotopy groups is used. -/
theorem ordNormalization_cycle_boundary (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    c - ordStrictInclusion2 (normalizeOrdChain2 c) =
      ordBoundary3 (ordNormalizationHomotopy2 c) := by
  rw [ordNormalization_chain_identity, hc, map_zero, zero_add]

end FiniteChains.Comb
