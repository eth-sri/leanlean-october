import RequestProject.GenusMarkingFirstEdges
import RequestProject.LiftedMarkedPathCoefficients
import RequestProject.GenusQuotientAttachingFilling
import RequestProject.GenusReceivedCoveredSpine
import RequestProject.Tac


/-! Exact group-ring coefficient recovery from the original lifted surface
markings in the actual quotient.  -/
noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Comb.ReceivedTree
variable {G H I : Type} [Group G] [Group H]

def translateCellChain (g : G) (c : (G × I) →₀ ℤ) : (G × I) →₀ ℤ :=
  Finsupp.mapDomain (fun x => (g * x.1, x.2)) c

def multiplyCellChain (c : (G × I) →₀ ℤ) :
    MonoidAlgebra ℤ G →ₗ[ℤ] ((G × I) →₀ ℤ) :=
  (Finsupp.linearCombination ℤ (translateCellChain · c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

theorem cellCoefficient_translate g (c : (G × I) →₀ ℤ) i :
    cellCoefficient i (translateCellChain g c) =
      MonoidAlgebra.single g 1 * cellCoefficient i c := by
  induction c using Finsupp.induction_linear with
  | zero => aesop
  | add c d hc hd =>
      simp [translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
      aesop
  | single x n =>
      rwd [translateCellChain, Finsupp.mapDomain_single, cellCoefficient_single,
        cellCoefficient_single]
      simp

theorem cellCoefficient_multiply w
    (c : (G × I) →₀ ℤ) i :
    cellCoefficient i (multiplyCellChain c w) = w * cellCoefficient i c := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp [map_add, hw, hz, add_mul]
  | single g n =>
      simp [multiplyCellChain, Finsupp.linearCombination_single, map_smul, cellCoefficient_translate, ← smul_mul_assoc]

theorem cellCoefficient_map_group (f : G →* H) (c : (G × I) →₀ ℤ) i :
    cellCoefficient i (Finsupp.mapDomain (fun x => (f x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ f (cellCoefficient i c) := by
  lin_ind c with c d hc hd => simp [Finsupp.mapDomain_add, map_add, hc, hd]
  | x n =>
      rwd [Finsupp.mapDomain_single, cellCoefficient_single, cellCoefficient_single]
      aesop

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem namedSurfaceIntoQuotient_onV_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onV := by
  intro σ τ h
  have ho := Sum.inl.inj h
  exact Subtype.ext (congrArg (·.1.spx) ho)

theorem namedSurfaceIntoQuotient_onE_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onE := by
  intro e f h
  apply Subtype.ext
  exact Prod.ext
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (·.1.1) h))
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (·.1.2) h))

def quotientMarkingFirstEdge (i : Fin q × Bool) :=
  (namedSurfaceIntoQuotient q ρ u).onE (markingFirstEdge q i)

def quotientMarkingTail (i : Fin q × Bool) :=
  mapPath (namedSurfaceIntoQuotient q ρ u) (markingTail q i)

theorem quotientSurfaceMarking_first_edge i :
    mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) =
      (quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i := (mapPath_comp _ _ _).trans (by
    simpa [namedSurfaceIntoQuotient, quotientMarkingFirstEdge, quotientMarkingTail, mapPath, List.map_cons]
      using congrArg (mapPath (namedSurfaceIntoQuotient q ρ u)) (gSig_first_edge q i))

theorem quotientMarkingFirstEdge_injective :
    Function.Injective (quotientMarkingFirstEdge q ρ u) :=
  (namedSurfaceIntoQuotient_onE_injective q ρ u).comp (markingFirstEdge_injective q)

theorem quotientMarkingTail_avoids i j
    c
    (hc : c ∈ quotientMarkingTail q ρ u j) : c.1 ≠ quotientMarkingFirstEdge q ρ u i := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  intro h
  exact markingTail_avoids_firstEdge q i j d hd
    (namedSurfaceIntoQuotient_onE_injective q ρ u h)

def allQuotientMarkingVertex
    (g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  deckV g (quotientCylinderVertex q ρ u)

theorem allQuotientMarkingVertex_end (g) :
    endV (allQuotientMarkingVertex q ρ u g) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) := by
  simp [allQuotientMarkingVertex, endV_deckV, quotientCylinderVertex_end]

theorem quotientSurfaceMarking_isPath i :
    IsPathX (orderCx (namedQuotientPos ρ q u))
      ((quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i)
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
  trivial

def allQuotientSurfaceMarkingChains :
    ((Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  liftedMarkingChainMap (quotientMarkingFirstEdge q ρ u) (quotientMarkingTail q ρ u)
    (allQuotientMarkingVertex q ρ u)

/-- Every individual sheet coefficient is retained by the actual geometric
marking chains. -/
theorem allQuotientSurfaceMarkingChains_injective :
    Function.Injective (allQuotientSurfaceMarkingChains q ρ u) := liftedMarkingChainMap_injective _ _ _ (quotientSurfaceMarking_isPath q ρ u)
    _ (allQuotientMarkingVertex_end q ρ u) (quotientMarkingFirstEdge_injective q ρ u)
    (deckV_injective_in_group _ _)
    (quotientMarkingTail_avoids q ρ u)

theorem quotientSurfaceMarkingChains_factor
    c :
    quotientSurfaceMarkingChains q ρ u hrho c =
      allQuotientSurfaceMarkingChains q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  lin_ind c with c d hc hd => simp [map_add, Finsupp.mapDomain_add, hc, hd]
  | x n =>
      simp [Finsupp.mapDomain_single, quotientSurfaceMarkingChains,
        allQuotientSurfaceMarkingChains, liftedMarkingChainMap,
        Finsupp.linearCombination_single, quotientSurfaceMarking_first_edge,
        allQuotientMarkingVertex]
      erw [Finsupp.linearCombination_single]

theorem allQuotientSurfaceMarkingChains_translate
    g (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.translateCellChain g c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c) := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd =>
      simp_all [ReceivedTree.translateCellChain, Finsupp.mapDomain_add, map_add]
  | single x n =>
      rwd [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
      erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      have hp := quotientSurfaceMarking_isPath q ρ u x.2
      rwd [← allQuotientMarkingVertex_end q ρ u x.1] at hp
      rwd [univDeck_pathChain _ _ _ hp]
      simp [allQuotientMarkingVertex, deckV_mul]

theorem allQuotientSurfaceMarkingChains_multiply
    w (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
          (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      simp [ReceivedTree.multiplyCellChain, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_smul, allQuotientSurfaceMarkingChains_translate]
