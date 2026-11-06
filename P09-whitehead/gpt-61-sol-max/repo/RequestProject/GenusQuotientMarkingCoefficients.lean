import Mathlib.Tactic

import RequestProject.GenusMarkingFirstEdges
import RequestProject.LiftedMarkedPathCoefficients
import RequestProject.GenusQuotientAttachingFilling
import RequestProject.GenusReceivedCoveredSpine

/-! Exact group-ring coefficient recovery from the original lifted surface
markings in the actual quotient.  -/
noncomputable section


set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
variable {G H I : Type} [Group G] [Group H]

def translateCellChain (g : G) (c : (G × I) →₀ ℤ)  :=
  Finsupp.mapDomain (fun x : G × I => (g * x.1, x.2)) c

def multiplyCellChain (c : (G × I) →₀ ℤ)  :=
  (Finsupp.linearCombination ℤ (fun g => translateCellChain g c)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

theorem cellCoefficient_translate (g : G) (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (translateCellChain g c) =
      MonoidAlgebra.single g 1 * cellCoefficient i c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [translateCellChain]
  | add c d hc hd =>
      ext <;> simp_all [translateCellChain, Finsupp.mapDomain_add]
  | single x n =>
      rw  [translateCellChain, Finsupp.mapDomain_single, cellCoefficient_single,
        cellCoefficient_single]
      simp_all

theorem cellCoefficient_multiply (w : MonoidAlgebra ℤ G)
    (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (multiplyCellChain c w) = w * cellCoefficient i c := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, hw, hz, add_mul]
  | single g n =>
      rw  [multiplyCellChain]
      erw [Finsupp.linearCombination_single]
      rw  [map_smul, cellCoefficient_translate]
      rw  [← smul_mul_assoc]
      congr 1
      simp [MonoidAlgebra.smul_single]

theorem cellCoefficient_map_group (f : G →* H) (c : (G × I) →₀ ℤ) (i : I) :
    cellCoefficient i (Finsupp.mapDomain (fun x : G × I => (f x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ f (cellCoefficient i c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add, map_add]
  | single x n =>
      classical aesop (add simp [Finsupp.mapDomain_single, FiniteChains.Comb.ReceivedTree.cellCoefficient_single])

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem namedSurfaceIntoQuotient_onV_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onV := by
  intro σ τ h
  have ho  := Sum.inl.inj h
  exact Subtype.ext (congrArg (fun c : QOld (cmpRel (GenusVertex q)) => c.1.spx) ho)

theorem namedSurfaceIntoQuotient_onE_injective :
    Function.Injective (namedSurfaceIntoQuotient q ρ u).onE := by
  intro e f h
  apply Subtype.ext
  exact Prod.ext
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (fun e => e.1.1) h))
    (namedSurfaceIntoQuotient_onV_injective q ρ u (congrArg (fun e => e.1.2) h))

variable (i : Fin q × Bool)
def quotientMarkingFirstEdge   :=
  (namedSurfaceIntoQuotient q ρ u).onE (markingFirstEdge q i)

def quotientMarkingTail   :=
  mapPath (namedSurfaceIntoQuotient q ρ u) (markingTail q i)

theorem quotientSurfaceMarking_first_edge  :
    mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) =
      (quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i := (mapPath_comp (oldIntoNamedQuotient q ρ u) (surfCx _) _).trans (by
    simpa [namedSurfaceIntoQuotient, quotientMarkingFirstEdge, quotientMarkingTail, mapPath, List.map_cons]
      using congrArg (mapPath (namedSurfaceIntoQuotient q ρ u)) (gSig_first_edge q i))

abbrev quotientMarkingFirstEdge_injective  :=
  Function.Injective.comp (FiniteChains.Davis.Genus.namedSurfaceIntoQuotient_onE_injective q ρ u)
    (FiniteChains.Davis.Genus.markingFirstEdge_injective q)

theorem quotientMarkingTail_avoids (i j : Fin q × Bool)
    (c : (orderCx (namedQuotientPos ρ q u)).E × Bool)
    (hc : c ∈ quotientMarkingTail q ρ u j) : c.1 ≠ quotientMarkingFirstEdge q ρ u i := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  intro h
  exact markingTail_avoids_firstEdge q i j d hd
    (namedSurfaceIntoQuotient_onE_injective q ρ u h)

variable (g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
def allQuotientMarkingVertex
     :=
  deckV g (quotientCylinderVertex q ρ u)

theorem allQuotientMarkingVertex_end (g) :
    endV (allQuotientMarkingVertex q ρ u g) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) := by
  aesop (add simp [allQuotientMarkingVertex])

theorem quotientSurfaceMarking_isPath  :
    IsPath (orderCx (namedQuotientPos ρ q u)).src (orderCx (namedQuotientPos ρ q u)).tgt
      ((quotientMarkingFirstEdge q ρ u i, true) :: quotientMarkingTail q ρ u i)
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
  rw  [← quotientSurfaceMarking_first_edge]
  exact isPath_mapPath _ (surfaceOldMarking_isPath q i)

def allQuotientSurfaceMarkingChains :
    ((Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  liftedMarkingChainMap (quotientMarkingFirstEdge q ρ u) (quotientMarkingTail q ρ u)
    (allQuotientMarkingVertex q ρ u)

/-- Every individual sheet coefficient is retained by the actual geometric
marking chains. -/
abbrev allQuotientSurfaceMarkingChains_injective  := liftedMarkingChainMap_injective _ _ _ (quotientSurfaceMarking_isPath q ρ u)
    _ (allQuotientMarkingVertex_end q ρ u) (quotientMarkingFirstEdge_injective q ρ u)
    (deckV_injective_in_group _ (quotientCylinderVertex q ρ u))
    (quotientMarkingTail_avoids q ρ u)

theorem quotientSurfaceMarkingChains_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    quotientSurfaceMarkingChains q ρ u hrho c =
      allQuotientSurfaceMarkingChains q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add]
  | single x n =>
      simp only [Finsupp.mapDomain_single, quotientSurfaceMarkingChains,
        allQuotientSurfaceMarkingChains, liftedMarkingChainMap,
        Finsupp.linearCombination_single, quotientSurfaceMarking_first_edge,
        allQuotientMarkingVertex]
      erw [Finsupp.linearCombination_single]

theorem allQuotientSurfaceMarkingChains_translate
     (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.translateCellChain g c) =
      chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
        (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [ReceivedTree.translateCellChain]
  | add c d hc hd =>
      simp only [ReceivedTree.translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
      rw  [hc, hd]
  | single x n =>
      rw  [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
      simp only [allQuotientSurfaceMarkingChains, liftedMarkingChainMap]
      erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg (fun z => n • z)
      have hp := quotientSurfaceMarking_isPath q ρ u x.2
      rw  [← allQuotientMarkingVertex_end q ρ u x.1] at hp
      rw  [univDeck_pathChain _ _ _ hp]
      simp only [allQuotientMarkingVertex, deckV_mul]

theorem allQuotientSurfaceMarkingChains_multiply
    (w : MonoidAlgebra ℤ (Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))) (c) :
    allQuotientSurfaceMarkingChains q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 ((univDeck (orderCx (namedQuotientPos ρ q u))
          (namedQuotientBase ρ q u)).cellHom g) (allQuotientSurfaceMarkingChains q ρ u c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear <;> simp_all [ReceivedTree.multiplyCellChain, allQuotientSurfaceMarkingChains_translate]

end FiniteChains.Davis.Genus
