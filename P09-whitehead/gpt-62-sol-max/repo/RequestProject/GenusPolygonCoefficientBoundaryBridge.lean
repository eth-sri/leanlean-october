module

public import RequestProject.GenusSurfaceMarkingCoefficients
public import RequestProject.FinsuppBasis

@[expose] public section

/-! The boundary of the actual polygon reconstruction recovers the complete
marked boundary before old-chain comparison. No independent marking-scalar
hypothesis remains.  -/
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open Nerve
universe u
variable {P : Type u} [PartialOrder P]

theorem decodeOrdNerve2_boundary_of_encoded_boundary
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection 3 c = c)
    (b : OrdEdge P →₀ ℤ) (hb : Nerve.bdry c = ordNerveChain1 b) :
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
    (hrho : IsSpineRelator ρ q u)
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c)
    (b : (SpineReplacementGroup ρ q u × (Fin q × Bool)) →₀ ℤ)
    (hb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b) :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedAttachingNerveSurfaceChain ρ q u c) =
      namedAttachingSurfaceChain1 q ρ u
        (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho b)) := by
  have hdecoded  :=
    decodeOrdNerve2_boundary_of_encoded_boundary c hc hd
      (namedAttachingMarkingChains q ρ u hrho b) hb
  change Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
      (normalizeOrdChain2 (chain2
        (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
        (decodeOrdNerve2 c))) = _
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, hdecoded]
  exact normalizedWeakChain1To_normalize
    (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
    (namedAttachingMarkingChains q ρ u hrho b)

/-- The old three-chain in the relative comparison does not alter the
actual attaching boundary. This proves the input of the preceding lemma. -/
theorem namedAttaching_marked_boundary_of_relative_class
    (hrho : IsSpineRelator ρ q u)
    (β : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β)
    (c : Ch (namedAttachingCover q ρ u))
    (y : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry y) :
    Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho
      (singleReceivedSpineMarkingChain q ρ u β) := by
  apply cmap_val_injective _
  have h := congrArg Nerve.bdry hC
  rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
    map_add, Nerve.bdry_bdry, add_zero, ← cmap_bdry,
    namedAttachingNerveBoundary_image] at h
  exact h.symm

theorem namedPolygonMultipleAt_boundary (v : NamedPolygonPole ρ q u)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedPolygonMultipleAt ρ q u v w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonFillingAt ρ q u v))) w.coeff := by
  change Comb.bdry2 _ (MonoidAlgebra.linearCombination _ w) = MonoidAlgebra.linearCombination _ w
  rw [MonoidAlgebra.apply_linearCombination]
  apply congrArg (fun f => MonoidAlgebra.linearCombination f w)
  funext g
  exact bdry2_chain2 _ _

/-- Polygon rigidity itself supplies the previously separate equality of
universal-cover marking chains, for the same full quotient-group scalar. -/
theorem namedPolygon_reconstruction_marking_multiple
    (hrho : IsSpineRelator ρ q u)
    (c d : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (b e : (SpineReplacementGroup ρ q u × (Fin q × Bool)) →₀ ℤ)
    (hcb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b)
    (hdb : Nerve.bdry d = namedAttachingNerveBoundary q ρ u hrho e)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    quotientSurfaceMarkingChains q ρ u hrho b =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
          (quotientSurfaceMarkingChains q ρ u hrho e))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hp  :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hb := congrArg (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))) hp
  rw [namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho c hc hcdegree b hcb,
    namedPolygonMultipleAt_boundary, ← hreference,
    namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho d hd hddegree e hdb] at hb
  exact namedSurfaceMarking_multiple_reflect q ρ u hrho b e w hb

/-- The geometric principal-vector theorem with the marking comparison
derived from reconstruction, rather than supplied as a hypothesis. -/
theorem finiteSpine_polygon_reference_principal_of_geometry
    (hrho : IsSpineRelator ρ q u)
    (β γ : SpineCoefficients ρ q u)
    (hβ : SpineInternalCycle ρ q u β)
    (hγ : SpineInternalCycle ρ q u γ)
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
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    ∃ a : MonoidAlgebra ℤ (SpineReplacementGroup ρ q u),
      ∀ m, β m = a * γ m := by
  have hcb := namedAttaching_marked_boundary_of_relative_class ρ q u hrho β hβ c yC hC
  have hdb := namedAttaching_marked_boundary_of_relative_class ρ q u hrho γ hγ d yD hD
  have hmark := namedPolygon_reconstruction_marking_multiple ρ q u hrho c d hc hd
    hcdegree hddegree _ _ hcb hdb v hreference hrelative
  exact finiteSpine_polygon_reference_principal ρ q u hrho β γ hβ hγ
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference hrelative hmark

end FiniteChains.Davis.Genus
