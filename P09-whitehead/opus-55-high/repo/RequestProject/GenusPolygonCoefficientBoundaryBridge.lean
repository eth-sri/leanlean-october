import RequestProject.GenusSurfaceMarkingCoefficients
import RequestProject.Tac


/-! The boundary of the actual polygon reconstruction recovers the complete
marked boundary before old-chain comparison. No independent marking-scalar
hypothesis remains.  -/
noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Comb
open Nerve
universe u
variable {P : Type u} [PartialOrder P]

theorem decodeOrdNerve2_boundary_of_encoded_boundary
    c (hc : c ∈ Inc P) (hd : lengthProjection 3 c = c)
    b (hb : Nerve.bdry c = ordNerveChain1 b) :
    Comb.bdry2 (orderCx P) (decodeOrdNerve2 c) = b := by
  apply ordNerveChain1_injective
  rw [ordNerveChain1_bdry2, ordNerveChain2_decode hc, hd, hb]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Decode and normalize the genuine marked boundary of the attaching chain.
All coefficients and cover sheets are retained. -/
theorem namedAttachingNerveSurfaceChain_marked_boundary
    hrho
    c (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c)
    b
    (hb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b) :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedAttachingNerveSurfaceChain ρ q u c) =
      namedAttachingSurfaceChain1 q ρ u
        (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho b)) := by
  have hdecoded :=
    decodeOrdNerve2_boundary_of_encoded_boundary c hc hd
      _ hb
  change Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
      (normalizeOrdChain2 (chain2
        (orderCxMap _ (namedSurfaceForward_monotone q ρ u))
        (decodeOrdNerve2 c))) = _
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, hdecoded]
  exact normalizedWeakChain1To_normalize
    _ (namedSurfaceForward_monotone q ρ u)
    _

/-- The old three-chain in the relative comparison does not alter the
actual attaching boundary. This proves the input of the preceding lemma. -/
theorem namedAttaching_marked_boundary_of_relative_class
    hrho
    β
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (c : Ch (namedAttachingCover q ρ u))
    (y : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry y) :
    Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho
      ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  apply cmap_val_injective _
    ⟨(namedAttachingReference q ρ u hrho 1).1, by grind⟩
  have h := congrArg Nerve.bdry hC
  rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
    map_add, Nerve.bdry_bdry, add_zero, ← cmap_bdry,
    namedAttachingNerveBoundary_image] at h
  exact h.symm

theorem namedPolygonMultipleAt_boundary v
    w :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedPolygonMultipleAt ρ q u v w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonFillingAt ρ q u v))) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      let f := fun g => chain2
        (strictOrderCxMap _ (namedSurfaceDeck ρ q u g).strictMono)
        (namedPolygonFillingAt ρ q u v)
      have hm : namedPolygonMultipleAt ρ q u v (MonoidAlgebra.single g n) = n • f g := by
        change Finsupp.linearCombination ℤ f (Finsupp.single g n) = n • f g
        simp
      rw [hm, map_zsmul, bdry2_chain2]
      simp


/-- Polygon rigidity itself supplies the previously separate equality of
universal-cover marking chains, for the same full quotient-group scalar. -/
theorem namedPolygon_reconstruction_marking_multiple
    hrho
    c d (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    b e
    (hcb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b)
    (hdb : Nerve.bdry d = namedAttachingNerveBoundary q ρ u hrho e)
    v
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    quotientSurfaceMarkingChains q ρ u hrho b =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
          (quotientSurfaceMarkingChains q ρ u hrho e))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hp :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hb := congrArg (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))) hp
  rw [namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho c hc hcdegree b hcb,
    namedPolygonMultipleAt_boundary, ← hreference,
    namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho d hd hddegree e hdb] at hb
  exact namedSurfaceMarking_multiple_reflect q ρ u hrho b e w hb

/-- The geometric principal-vector theorem with the marking comparison
derived from reconstruction, rather than supplied as a hypothesis. -/
theorem finiteSpine_polygon_reference_principal_of_geometry
    hrho
    β γ
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry yC)
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    v
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    ∃ a,
      ∀ m, β m = a * γ m := by
  have hcb := namedAttaching_marked_boundary_of_relative_class ρ q u hrho β hβ c yC hC
  have hdb := namedAttaching_marked_boundary_of_relative_class ρ q u hrho γ hγ d yD hD
  have hmark := namedPolygon_reconstruction_marking_multiple ρ q u hrho c d hc hd
    hcdegree hddegree _ _ hcb hdb v hreference hrelative
  exact finiteSpine_polygon_reference_principal ρ q u hrho β γ hβ hγ
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference hrelative hmark
