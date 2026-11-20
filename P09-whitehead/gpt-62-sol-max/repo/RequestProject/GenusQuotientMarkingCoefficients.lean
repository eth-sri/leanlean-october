module

public import RequestProject.GenusMarkingFirstEdges
public import RequestProject.FinsuppBasis
public import RequestProject.LiftedMarkedPathCoefficients
public import RequestProject.GenusQuotientAttachingFilling
public import RequestProject.GenusReceivedCoveredSpine

public import RequestProject.GroupCellChainCoordinates

@[expose] public section

/-! Exact group-ring coefficient recovery from the original lifted surface
markings in the actual quotient.  -/
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
variable {G H I : Type} [Group G] [Group H]

def translateCellChain (g : G) (c : (G × I) →₀ ℤ) : (G × I) →₀ ℤ :=
  Finsupp.mapDomain (fun x  => (g * x.1, x.2)) c

def multiplyCellChain (c : (G × I) →₀ ℤ) :
    MonoidAlgebra ℤ G →ₗ[ℤ] ((G × I) →₀ ℤ) :=
  MonoidAlgebra.linearCombination (fun g => translateCellChain g c)

theorem map_multiplyCellChain {M : Type*} [AddCommGroup M]
    (f : ((G × I) →₀ ℤ) →ₗ[ℤ] M) (c : (G × I) →₀ ℤ) (v : G → M)
    (hv : ∀ g, f (translateCellChain g c) = v g) (w : MonoidAlgebra ℤ G) :
    f (multiplyCellChain c w) = MonoidAlgebra.linearCombination v w := by
  rw [multiplyCellChain, MonoidAlgebra.apply_linearCombination, show f ∘ _ = v from funext hv]

theorem cellCoefficient_translate (g : G) (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (translateCellChain g c) =
      MonoidAlgebra.single g 1 * cellCoefficient i c := by
  finsupp_basis c [ translateCellChain ]
  intro x
  erw [translateCellChain, Finsupp.mapDomain_single, cellCoefficient_single,
    cellCoefficient_single]
  simp

theorem cellCoefficient_multiply (w : MonoidAlgebra ℤ G)
    (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (multiplyCellChain c w) = w * cellCoefficient i c := by
  rw [map_multiplyCellChain _ c _ (fun g => cellCoefficient_translate g c i)]
  change Finsupp.linearCombination ℤ (fun g => MonoidAlgebra.single g 1 * cellCoefficient i c) w.coeff = _
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [MonoidAlgebra.coeff_add, map_add, hw, hz, add_mul]
  | single g n => simp [← smul_mul_assoc]

theorem cellCoefficient_map_group (f : G →* H) (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (Finsupp.mapDomain (fun x : G × I => (f x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ f (cellCoefficient i c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single x n =>
      erw [Finsupp.mapDomain_single, cellCoefficient_single, cellCoefficient_single]
      by_cases h : x.2 = i <;> simp_all

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

theorem namedSurfaceIntoQuotient_onV_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onV := by
  intro σ τ h
  have ho  := Sum.inl.inj h
  exact Subtype.ext (congrArg (·.1.spx) ho)

theorem namedSurfaceIntoQuotient_onE_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onE := by
  intro e f h
  apply Subtype.ext
  exact Prod.ext
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (·.1.1) h))
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (·.1.2) h))

def quotientMarkingFirstEdge (i : Fin q × Bool) : (namedQuotientCx ρ q u).E :=
  (namedSurfaceIntoQuotient q ρ u).onE (markingFirstEdge q i)

def quotientMarkingTail (i : Fin q × Bool) : List ((namedQuotientCx ρ q u).E × Bool) :=
  mapPath (namedSurfaceIntoQuotient q ρ u) (markingTail q i)

theorem quotientSurfaceMarking_first_edge (i : Fin q × Bool) :
    mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) =
      (quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i := by
  change mapPath (oldIntoNamedQuotient q ρ u)
    (mapPath (surfCx _) (gSig q (i.1.val, i.2))) = _
  exact (mapPath_comp (oldIntoNamedQuotient q ρ u) (surfCx _) _).trans (by
    simpa only [namedSurfaceIntoQuotient, quotientMarkingFirstEdge, quotientMarkingTail, mapPath, List.map_cons]
      using congrArg (mapPath (namedSurfaceIntoQuotient q ρ u)) (gSig_first_edge q i))

theorem quotientMarkingFirstEdge_injective :
    Function.Injective (quotientMarkingFirstEdge q ρ u) :=
  (namedSurfaceIntoQuotient_onE_injective q ρ u).comp (markingFirstEdge_injective q)

theorem quotientMarkingTail_avoids (i j : Fin q × Bool)
    (c : (namedQuotientCx ρ q u).E × Bool)
    (hc : c ∈ quotientMarkingTail q ρ u j) : c.1 ≠ quotientMarkingFirstEdge q ρ u i := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  intro h
  exact markingTail_avoids_firstEdge q i j d hd
    (namedSurfaceIntoQuotient_onE_injective q ρ u h)

def allQuotientMarkingVertex
    (g : NamedQuotientGroup ρ q u) :=
  deckV g (quotientCylinderVertex q ρ u)

theorem allQuotientMarkingVertex_end (g) :
    endV (allQuotientMarkingVertex q ρ u g) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) := by
  erw [allQuotientMarkingVertex, endV_deckV, quotientCylinderVertex_end]

theorem quotientSurfaceMarking_isPath (i : Fin q × Bool) :
    IsPath (namedQuotientCx ρ q u).src (namedQuotientCx ρ q u).tgt
      ((quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i)
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
  erw [← quotientSurfaceMarking_first_edge]
  exact isPath_mapPath _ (surfaceOldMarking_isPath q i)

def allQuotientSurfaceMarkingChains :
    ((NamedQuotientGroup ρ q u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((namedQuotientCover ρ q u).E →₀ ℤ) :=
  liftedMarkingChainMap (quotientMarkingFirstEdge q ρ u) (quotientMarkingTail q ρ u)
    (allQuotientMarkingVertex q ρ u)

/-- Every individual sheet coefficient is retained by the actual geometric
marking chains. -/
theorem allQuotientSurfaceMarkingChains_injective :
    Function.Injective (allQuotientSurfaceMarkingChains q ρ u) := liftedMarkingChainMap_injective _ _ _ (quotientSurfaceMarking_isPath q ρ u)
    _ (allQuotientMarkingVertex_end q ρ u) (quotientMarkingFirstEdge_injective q ρ u)
    (deckV_injective_in_group _ (quotientCylinderVertex q ρ u))
    (quotientMarkingTail_avoids q ρ u)

theorem quotientSurfaceMarkingChains_factor
    (c : (SpineReplacementGroup ρ q u × (Fin q × Bool)) →₀ ℤ) :
    quotientSurfaceMarkingChains q ρ u hrho c =
      allQuotientSurfaceMarkingChains q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  finsupp_basis c
  intro x
  simp only [Finsupp.mapDomain_single, quotientSurfaceMarkingChains,
    allQuotientSurfaceMarkingChains, liftedMarkingChainMap,
    Finsupp.linearCombination_single, quotientSurfaceMarking_first_edge,
    allQuotientMarkingVertex]
  erw [Finsupp.linearCombination_single]

theorem allQuotientSurfaceMarkingChains_translate
    (g : NamedQuotientGroup ρ q u) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.translateCellChain g c) =
      chain1 ((namedQuotientDeck ρ q u).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c) := by
  finsupp_basis c [ ReceivedTree.translateCellChain ]
  intro x
  erw [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
  simp only [allQuotientSurfaceMarkingChains, liftedMarkingChainMap]
  erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
  apply congrArg (fun z => 1 • z)
  have hp := quotientSurfaceMarking_isPath q ρ u x.2
  erw [← allQuotientMarkingVertex_end q ρ u x.1] at hp
  erw [univDeck_pathChain _ _ _ hp]
  simp only [allQuotientMarkingVertex, deckV_mul]

theorem allQuotientSurfaceMarkingChains_multiply
    (w : MonoidAlgebra ℤ (NamedQuotientGroup ρ q u)) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 ((namedQuotientDeck ρ q u).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c)) w.coeff :=
  ReceivedTree.map_multiplyCellChain _ c _ (fun g => allQuotientSurfaceMarkingChains_translate q ρ u g c) w

end FiniteChains.Davis.Genus
