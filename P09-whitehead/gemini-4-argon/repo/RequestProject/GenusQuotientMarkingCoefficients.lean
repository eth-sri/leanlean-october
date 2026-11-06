module

public import RequestProject.GenusMarkingFirstEdges
public import RequestProject.LiftedMarkedPathCoefficients
public import RequestProject.GenusQuotientAttachingFilling
public import RequestProject.GenusReceivedCoveredSpine

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
variable {G H I : Type} [Group G] [Group H]

def translateCellChain (g : G) (c : (G × I) →₀ ℤ) : (G × I) →₀ ℤ :=
  Finsupp.mapDomain (fun x : G × I => (g * x.1, x.2)) c

def multiplyCellChain (c : (G × I) →₀ ℤ) :
    MonoidAlgebra ℤ G →ₗ[ℤ] ((G × I) →₀ ℤ) :=
  (Finsupp.linearCombination ℤ (fun g => translateCellChain g c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

theorem cellCoefficient_multiply (w : MonoidAlgebra ℤ G)
    (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (multiplyCellChain c w) = w * cellCoefficient i c := by
  have htr (g : G) : cellCoefficient i (translateCellChain g c) =
      MonoidAlgebra.single g 1 * cellCoefficient i c := by
    induction c using Finsupp.induction_linear with
    | zero => simp [translateCellChain]
    | add _ _ hc hd =>
        simp only [translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
        erw [hc, hd, mul_add]
    | single x n =>
        erw [translateCellChain, Finsupp.mapDomain_single, cellCoefficient_single,
          cellCoefficient_single]
        by_cases h : x.2 = i <;> simp [h]
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ hw hz => simp only [map_add, hw, hz, add_mul]
  | single g n =>
      erw [multiplyCellChain, Finsupp.linearCombination_single, map_smul, htr, ← smul_mul_assoc]
      congr 1; simp [MonoidAlgebra.smul_single]

theorem cellCoefficient_map_group (f : G →* H) (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (Finsupp.mapDomain (fun x : G × I => (f x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ f (cellCoefficient i c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add _ _ hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single x n =>
      erw [Finsupp.mapDomain_single, cellCoefficient_single, cellCoefficient_single]
      by_cases h : x.2 = i <;> simp [h, MonoidAlgebra.mapDomainRingHom]

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem namedSurfaceIntoQuotient_onE_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onE := by
  have hV : Function.Injective (namedSurfaceIntoQuotient q ρ u).onV := fun _ _ h =>
    Subtype.ext (congrArg (fun c : QOld (cmpRel (GenusVertex q)) => c.1.spx) (Sum.inl.inj h))
  exact fun _ _ h => Subtype.ext (Prod.ext (hV (congrArg (·.1.1) h)) (hV (congrArg (·.1.2) h)))

def quotientMarkingFirstEdge (i : Fin q × Bool) : (orderCx (namedQuotientPos ρ q u)).E :=
  (namedSurfaceIntoQuotient q ρ u).onE (markingFirstEdge q i)

def quotientMarkingTail (i : Fin q × Bool) : List ((orderCx (namedQuotientPos ρ q u)).E × Bool) :=
  mapPath (namedSurfaceIntoQuotient q ρ u) (markingTail q i)

theorem quotientSurfaceMarking_first_edge (i : Fin q × Bool) :
    mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) =
      (quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i :=
  (mapPath_comp (oldIntoNamedQuotient q ρ u) (surfCx _) _).trans (by
    simpa only [namedSurfaceIntoQuotient, quotientMarkingFirstEdge, quotientMarkingTail, mapPath,
      List.map_cons] using congrArg (mapPath (namedSurfaceIntoQuotient q ρ u)) (gSig_first_edge q i))

def allQuotientMarkingVertex
    (g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  deckV g (quotientCylinderVertex q ρ u)

theorem allQuotientMarkingVertex_end (g) :
    endV (allQuotientMarkingVertex q ρ u g) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) := by
  erw [allQuotientMarkingVertex, endV_deckV, quotientCylinderVertex_end]

theorem quotientSurfaceMarking_isPath (i : Fin q × Bool) :
    IsPath (orderCx (namedQuotientPos ρ q u)).src (orderCx (namedQuotientPos ρ q u)).tgt
      ((quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i)
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
  erw [← quotientSurfaceMarking_first_edge]
  exact isPath_mapPath _ (surfaceOldMarking_isPath q i)

def allQuotientSurfaceMarkingChains :
    ((Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  liftedMarkingChainMap (quotientMarkingFirstEdge q ρ u) (quotientMarkingTail q ρ u)
    (allQuotientMarkingVertex q ρ u)

theorem allQuotientSurfaceMarkingChains_injective :
    Function.Injective (allQuotientSurfaceMarkingChains q ρ u) :=
  liftedMarkingChainMap_injective _ _ _ (quotientSurfaceMarking_isPath q ρ u)
    _ (allQuotientMarkingVertex_end q ρ u)
    ((namedSurfaceIntoQuotient_onE_injective q ρ u).comp (markingFirstEdge_injective q))
    (deckV_injective_in_group _ (quotientCylinderVertex q ρ u))
    fun i j c hc h => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact markingTail_avoids_firstEdge q i j d hd
        (namedSurfaceIntoQuotient_onE_injective q ρ u h)

theorem quotientSurfaceMarkingChains_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    quotientSurfaceMarkingChains q ρ u hrho c =
      allQuotientSurfaceMarkingChains q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add _ _ hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      simp only [Finsupp.mapDomain_single, quotientSurfaceMarkingChains,
        allQuotientSurfaceMarkingChains, liftedMarkingChainMap,
        Finsupp.linearCombination_single, quotientSurfaceMarking_first_edge,
        allQuotientMarkingVertex]
      erw [Finsupp.linearCombination_single]

theorem allQuotientSurfaceMarkingChains_translate
    (g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.translateCellChain g c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [ReceivedTree.translateCellChain]
  | add _ _ hc hd =>
      simp only [ReceivedTree.translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
      erw [hc, hd]
  | single x n =>
      erw [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
      simp only [allQuotientSurfaceMarkingChains, liftedMarkingChainMap]
      erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg (n • ·)
      have hp := quotientSurfaceMarking_isPath q ρ u x.2
      erw [← allQuotientMarkingVertex_end q ρ u x.1] at hp
      erw [univDeck_pathChain _ _ _ hp]
      simp only [allQuotientMarkingVertex, deckV_mul]

theorem allQuotientSurfaceMarkingChains_multiply
    (w : MonoidAlgebra ℤ (Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
          (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      erw [map_smul, allQuotientSurfaceMarkingChains_translate]

end FiniteChains.Davis.Genus
