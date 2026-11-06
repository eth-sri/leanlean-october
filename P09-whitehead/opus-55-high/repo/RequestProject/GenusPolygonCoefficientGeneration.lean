import RequestProject.GenusPolygonCoefficientBoundaryBridge
import RequestProject.Tac


/-! The actual marking boundary supplies polygon relativity automatically.
Consequently a fixed degree-one geometric reference generates every vector
satisfying the internal B2 equations. Written, unverified proof terms. -/
noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Comb
universe u
variable {P Q I : Type u} [PartialOrder P] [PartialOrder Q]

theorem normalizedWeakChain1To_paths_boundary_support
    f hf (S : Q → Prop)
    (p : I → List (OrdEdge P × Bool))
    (hp : ∀ i a, a ∈ p i → S (f a.1.1.1) ∧ S (f a.1.1.2))
    c :
    ∀ e ∈ (normalizedWeakChain1To f hf (Finsupp.linearCombination ℤ
      (fun i => pathChain (p i)) c)).support, S e.1.1 ∧ S e.1.2 := by
  intro e he
  by_contra hnot
  have hz (i : I) : normalizedWeakChain1To f hf (pathChain (p i)) e = 0 := by
    apply normalizedWeakChain1To_path_apply_zero
    grind
  have hzero : normalizedWeakChain1To f hf
      (Finsupp.linearCombination ℤ (fun i => pathChain (p i)) c) e = 0 := by
    clear he
    induction c using Finsupp.induction_linear <;> simp_all
  simp_all

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q]

/-- Every edge of the original marking has both last vertices on the
identified polygon boundary, including the flags that normalize to zero. -/
theorem gSig_lastEndpoints_boundary (i : Fin q × Bool)
    (a : MarkingSurfaceEdge q × Bool) (ha : a ∈ gSig q (i.1.val, i.2)) :
    InPolygonBoundary (gc q) (chainMax a.1.1.1) ∧
      InPolygonBoundary (gc q) (chainMax a.1.1.2) := by
  rw [gSig_first_edge] at ha
  simp [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [markingFirstEdge, markingBaseFlag, markingBedBaseFlag, markingBedMidFlag,
      markingMidFlag, markingBaseCell, markingMidCell, markingBedCell, InPolygonBoundary]

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem namedAttachingMarkingPath_surface_boundary
    g i
    (a : OrdEdge (namedAttachingCover q ρ u) × Bool)
    (ha : a ∈ namedAttachingMarkingPath q ρ u hrho g i) :
    InPolygonBoundary (gc q)
        (namedSurfaceProjection ρ q u (namedSurfaceForward q ρ u a.1.1.1)) ∧
      InPolygonBoundary (gc q)
        (namedSurfaceProjection ρ q u (namedSurfaceForward q ρ u a.1.1.2)) := by
  have hm : ((namedAttachingProjection q ρ u).onE a.1, a.2) ∈ gSig q (i.1.val, i.2) := by
    rw [← (namedAttachingMarkingPath_spec q ρ u hrho g i).2]
    exact List.mem_map.mpr (by aesop)
  exact gSig_lastEndpoints_boundary q i _ hm

theorem namedSurfaceMarkingChains_boundary_support
    b :
    ∀ e ∈ (normalizedWeakChain1To (namedSurfaceForward q ρ u)
        (namedSurfaceForward_monotone q ρ u) (namedAttachingMarkingChains q ρ u hrho b)).support,
      InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.1) ∧
        InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.2) := normalizedWeakChain1To_paths_boundary_support
    _ _
    (fun p =>
      InPolygonBoundary _ (namedSurfaceProjection ρ q u p))
    _
    (fun x a ha => namedAttachingMarkingPath_surface_boundary q ρ u hrho x.1 x.2 a ha) b

/-- The relative condition follows from the actual marking boundary; it is
not an additional geometric assumption on the arbitrary B2 input chain. -/
theorem namedAttachingNerveSurfaceChain_polygonRelative
    c (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c)
    b
    (hb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b) :
    PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c) := by
  intro e he
  rw [namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho c hc hd b hb] at he
  change e ∈ (normalizedChain1To _ (namedSurfaceForward_monotone q ρ u)
    (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho b))).support at he
  rw [← normalizedWeakChain1To_normalize] at he
  exact namedSurfaceMarkingChains_boundary_support q ρ u hrho b e he

/-- Once the actual geometric reference is fixed, the only assumptions on
an arbitrary coefficient vector are the original internal B2 equations.
Its attaching filling and old correction are provided by the proved cover
filling theorem, and polygon relativity is derived from its marked boundary. -/
theorem finiteSpine_polygon_reference_generates
    γ
    (hγ : ∀ z,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (d : Ch (namedAttachingCover q ρ u)) (hd : d ∈ Inc _)
    (hddegree : lengthProjection 3 d = d)
    (yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    v
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v) :
    ∀ (β : NamedSpineRel q → MonoidAlgebra ℤ
        (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))),
      (∀ z,
        (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
          (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) →
      ∃ a,
        ∀ m, β m = a * γ m := by
  intro β hβ
  obtain ⟨c, hc, hcdegree, hcb, yC, hyC, _hyCdegree, hC⟩ :=
    quotientCorrectedRelative_attaching_filling q ρ u hrho β hβ
  have hrelative := namedAttachingNerveSurfaceChain_polygonRelative q ρ u hrho
    c hc hcdegree _ hcb
  exact finiteSpine_polygon_reference_principal_of_geometry ρ q u hrho β γ hβ hγ
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference hrelative
