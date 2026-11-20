module

public import RequestProject.GenusReceivedQuotientComparison
public import RequestProject.LiftedHomotopyChains
public import RequestProject.DeckChainTransport

@[expose] public section

/-! The actual old-cell correction from spine markings to attaching-surface
markings.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
variable {K Y : Complex2}

theorem univLift_pathChain (a : K.V) (f : Hom K Y) (v : UV K a)
    {p : List _} {b : K.V}
    (hp : IsPath K.src K.tgt p (endV v) b) :
    chain1 (univLift K f a) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath (mapPath f p) (univLiftV a f v)) := by
  change Finsupp.mapDomain _ (pathChain _) = _
  erw [← pathChain_map]
  exact congrArg pathChain (uLiftPath_univLiftV a f p v b hp).symm

theorem uCoverPathTransport_pathChain {a b : K.V} {c : List _}
    (hc : IsPath K.src K.tgt c a b) (v : UV K b)
    {p : List _} {d : K.V}
    (hp : IsPath K.src K.tgt p (endV v) d) :
    chain1 (uCoverPathTransport hc) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p ((uCoverPathTransport hc).onV v)) := by
  change Finsupp.mapDomain _ (pathChain _) = _
  erw [← pathChain_map]
  exact congrArg pathChain (uLiftPath_pathTransportV hc p v d hp).symm

theorem univDeck_pathChain (a : K.V) (g : Pi1 K a) (v : UV K a)
    {p : List _} {b : K.V}
    (hp : IsPath K.src K.tgt p (endV v) b) :
    chain1 ((univDeck K a).cellHom g) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p (deckV g v)) := by
  change Finsupp.mapDomain _ (pathChain _) = _
  erw [← pathChain_map _]
  exact congrArg pathChain (uLiftPath_deckV g p v b hp).symm

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical
variable (q : ℕ) [NeZero q]

abbrev spineOldBase := posQCube (gBase q)
abbrev spineOldCx := orderCx (QOld (cmpRel (GenusVertex q)))

variable (i : Fin q × Bool)

def spineOldMarking :=
  mapPath (genusSpineToOld q) (spineMarkedLoop q i).1

def surfaceOldMarking :=
  mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (i.1.val, i.2))

theorem spineOldMarking_isPath :
    IsPath (spineOldCx q).src (spineOldCx q).tgt (spineOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath _ (spineMarkedLoop q i).2

theorem surfaceOldMarking_isPath :
    IsPath (spineOldCx q).src (spineOldCx q).tgt (surfaceOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath _ (isPath_gSig q (i.1.val, i.2))

theorem exists_spineOldMarkingCorrection :
    ∃ d : (uCover (spineOldCx q) _).F →₀ ℤ,
      Comb.bdry2 _ d =
        pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
          pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) := (htpy_uLiftPath
    (spineOldMarking_isPath q i) (spineMarkedLoop_toOld_htpy q i)).exists_boundary

def spineOldMarkingCorrection :=
  Classical.choose (exists_spineOldMarkingCorrection q i)

theorem spineOldMarkingCorrection_boundary :
    Comb.bdry2 _ (spineOldMarkingCorrection q i) =
      pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
        pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) :=
  Classical.choose_spec (exists_spineOldMarkingCorrection q i)

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def oldIntoNamedQuotient :=
  orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone

theorem oldCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u) ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) :=
  by solve_by_elim

def quotientCylinderVertex :
    UV (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  UV.mk ⟨spineQuotientCylinderPath q ρ u, by
    apply oldCylinderPath_isPath⟩

theorem quotientCylinderVertex_end :
    endV (quotientCylinderVertex q ρ u) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) :=
  rfl

/-- Every face of this lift is an actual old face of the quotient. -/
def oldCoverToNamedQuotient :=
  (uCoverPathTransport (oldCylinderPath_isPath q ρ u)).comp
    (univLift (spineOldCx q) (oldIntoNamedQuotient q ρ u) (spineOldBase q))

theorem oldCoverToNamedQuotient_pathChain
    {p : List _} (b : (spineOldCx q).V)
    (hp : IsPath (spineOldCx q).src (spineOldCx q).tgt p (spineOldBase q) b) :
    chain1 (oldCoverToNamedQuotient q ρ u)
      (pathChain (uLiftPath p (UV.base (spineOldCx q) (spineOldBase q)))) =
      pathChain (uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) p)
        (quotientCylinderVertex q ρ u)) := by
  erw [oldCoverToNamedQuotient, chain1_comp_apply, univLift_pathChain _ _ _ hp]
  solve_by_elim [uCoverPathTransport_pathChain, isPath_mapPath]

variable (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u)))

theorem receivedSpineToQuotient_root :
    (receivedSpineToQuotient q ρ u hrho).onV (g, (markedSpineTree q).root) =
      deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u) := by
  change (uCoverPathTransport _).onV
    (deckV (finiteSpineOldRootReceiver q ρ u hrho g)
      (SpanningTree.mappedTreeReference (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root)) = _
  simp only [SpanningTree.mappedTreeReference, SpanningTree.treePath_root,
    mapPath, List.map_nil, extendList_nil]
  erw [uCoverPathTransport_deckV, uCoverPathTransport_base]
  solve_by_elim [spineQuotientCylinderPath_isPath, isPath_revPath, pi1Conj_cancel_reverse]

variable (i : Fin q × Bool)

def quotientMarkingCorrection :=
  (univDeck _ _).faceChains
    (finiteSpineToQuotient ρ q u hrho g)
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

/-- The correction is lifted in the old subcomplex before translation;
its boundary changes exactly the two chosen marking paths. -/
theorem quotientMarkingCorrection_boundary :
    Comb.bdry2 _ (quotientMarkingCorrection q ρ u hrho g i) =
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) -
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) := by
  erw [quotientMarkingCorrection, DeckAction.faceChains_boundary, bdry2_chain2,
    spineOldMarkingCorrection_boundary, map_sub, map_sub]
  erw [oldCoverToNamedQuotient_pathChain q ρ u _ (spineOldMarking_isPath q i),
    oldCoverToNamedQuotient_pathChain q ρ u _ (surfaceOldMarking_isPath q i)]
  have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
    erw [quotientCylinderVertex_end]
    grind [isPath_mapPath, spineOldMarking_isPath]
  have hs : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
    erw [quotientCylinderVertex_end]
    grind [isPath_mapPath, surfaceOldMarking_isPath]
  erw [univDeck_pathChain _ _ _ hp, univDeck_pathChain _ _ _ hs]

def quotientMarkingCorrections :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => quotientMarkingCorrection q ρ u hrho x.1 x.2)

def quotientSpineMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath
    (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q x.2))
    (deckV (finiteSpineToQuotient ρ q u hrho x.1) (quotientCylinderVertex q ρ u))))

def quotientSurfaceMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath
    (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
    (deckV (finiteSpineToQuotient ρ q u hrho x.1) (quotientCylinderVertex q ρ u))))

theorem quotientMarkingCorrections_boundary
    (c : (PresGroup _ × (Fin q × Bool)) →₀ ℤ) :
    Comb.bdry2 _ (quotientMarkingCorrections q ρ u hrho c) =
      quotientSpineMarkingChains q ρ u hrho c - quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      erw [map_add, map_add, hc, hd, map_add, map_add]
      abel
  | single x n =>
      simp [quotientMarkingCorrections, quotientSpineMarkingChains, quotientSurfaceMarkingChains, Finsupp.linearCombination_single, map_smul, quotientMarkingCorrection_boundary, smul_sub]

theorem markedSpineToNamedQuotient_marking_path (i : Fin q × Bool) :
    mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1 =
      mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i) := by
  erw [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]; rfl

/-- The abstractly indexed marked chain map agrees exactly with the actual
translated lifted marking paths at the cylinder endpoint. -/
theorem quotientSpineMarkingChains_eq
    (c : (PresGroup _ × (Fin q × Bool)) →₀ ℤ) :
    chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
      (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
        (treeMarkedSpineLoop q) c) = quotientSpineMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      obtain ⟨g, i⟩ := x
      erw [ReceivedTree.geometricMarkedChainMap, Finsupp.linearCombination_single,
        map_smul, quotientSpineMarkingChains, Finsupp.linearCombination_single]
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1)
          (endV (ReceivedTree.receiverVertex (markedSpineTree q)
            (markedSpineToNamedQuotient q ρ u)
            (finiteSpineOldRootReceiver q ρ u hrho) g (markedSpineTree q).root))
          ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
        erw [ReceivedTree.receiverVertex_end]
        grind [isPath_mapPath]
      erw [uCoverPathTransport_pathChain _ _ hp, markedSpineToNamedQuotient_marking_path]
      erw [receivedSpineToQuotient_root]

variable (β : NamedSpineRel q → MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))

def quotientCorrectedRelativeChain :=
  chain2 (receivedSpineToQuotient q ρ u hrho)
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β) -
      quotientMarkingCorrections q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i)))

/-- Starting with the actual B2 coordinate equation now gives an actual
old two-chain whose boundary lies on the attaching surface with exactly the
original marked coefficients. No absolute-cycle assumption is added. -/
theorem quotientCorrectedRelativeChain_boundary
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ _)
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 _ (quotientCorrectedRelativeChain q ρ u hrho β) =
      quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  erw [quotientCorrectedRelativeChain, map_sub,
    receivedSpineToQuotient_relative_boundary q ρ u hrho β hβ,
    quotientSpineMarkingChains_eq, quotientMarkingCorrections_boundary]
  abel

end FiniteChains.Davis.Genus
