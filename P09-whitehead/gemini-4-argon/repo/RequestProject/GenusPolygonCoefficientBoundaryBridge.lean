module

public import RequestProject.GenusSurfaceMarkingCoefficients

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

theorem namedAttachingNerveSurfaceChain_marked_boundary
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c)
    (b : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)
    (hb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b) :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedAttachingNerveSurfaceChain ρ q u c) =
      namedAttachingSurfaceChain1 q ρ u
        (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho b)) := by
  have hdecoded : Comb.bdry2 (orderCx (namedAttachingCover q ρ u)) (decodeOrdNerve2 c) =
      namedAttachingMarkingChains q ρ u hrho b :=
    ordNerveChain1_injective (by
      rw [ordNerveChain1_bdry2, ordNerveChain2_decode hc, hd, hb]
      rfl)
  change Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
      (normalizeOrdChain2 (chain2
        (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
        (decodeOrdNerve2 c))) = _
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, hdecoded]
  exact normalizedWeakChain1To_normalize
    (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
    (namedAttachingMarkingChains q ρ u hrho b)

theorem finiteSpine_polygon_reference_principal_of_geometry
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
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
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  have hrel_bdry (δ : NamedSpineRel q → MonoidAlgebra ℤ
        (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
      (hδ : ∀ z : SpinePresentationGen q,
        (∑ m, δ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
          (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
      (x : Ch (namedAttachingCover q ρ u))
      (y : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
      (hX : quotientCorrectedRelativeNerveChain q ρ u hrho δ = cmap Subtype.val x + Nerve.bdry y) :
      Nerve.bdry x = namedAttachingNerveBoundary q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => δ (Sum.inr i))) := by
    apply cmap_val_injective _
      ⟨(namedAttachingReference q ρ u hrho 1).1, (namedAttachingReference q ρ u hrho 1).2⟩
    have h := congrArg Nerve.bdry hX
    rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho δ hδ,
      map_add, Nerve.bdry_bdry, add_zero, ← cmap_bdry, namedAttachingNerveBoundary_image] at h
    exact h.symm
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hmult_bdry :
      Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonMultipleAt ρ q u v w) =
        Finsupp.linearCombination ℤ (fun g =>
          chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
            (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonFillingAt ρ q u v))) w.coeff := by
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add _ _ hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
    | single g n =>
        let f := fun g => chain2
          (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (namedPolygonFillingAt ρ q u v)
        have hm : namedPolygonMultipleAt ρ q u v (MonoidAlgebra.single g n) = n • f g :=
          Finsupp.linearCombination_single ℤ n g
        rw [hm, map_zsmul, bdry2_chain2]
        let h := fun g => chain1
          (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonFillingAt ρ q u v))
        change n • h g = Finsupp.linearCombination ℤ h (Finsupp.single g n)
        exact (Finsupp.linearCombination_single ℤ n g).symm
  have hb := congrArg (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)))
    (namedPolygon_reconstruct_at_pole ρ q u v _ hrelative)
  rw [namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho c hc hcdegree _ (hrel_bdry β hβ c yC hC),
    hmult_bdry, ← hreference,
    namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho d hd hddegree _ (hrel_bdry γ hγ d yD hD)] at hb
  exact finiteSpine_polygon_reference_principal ρ q u hrho β γ hβ hγ
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference hrelative
    (namedSurfaceMarking_multiple_reflect q ρ u hrho _ _ w hb)

end FiniteChains.Davis.Genus
