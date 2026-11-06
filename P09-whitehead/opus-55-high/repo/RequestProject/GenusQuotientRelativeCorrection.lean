import RequestProject.GenusReceivedQuotientComparison
import RequestProject.LiftedHomotopyChains
import RequestProject.DeckChainTransport
import RequestProject.Tac
noncomputable section


/-! The actual old-cell correction from spine markings to attaching-surface
markings. 
-/

bwd

namespace FiniteChains.Comb
variable {K Y : Complex2}

theorem univLift_pathChain a (f : Hom K Y) v
    {p} {b}
    (hp : IsPathX K p (endV v) b) :
    chain1 (univLift K f a) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath (mapPath f p) (univLiftV a f v)) := by
  change Finsupp.mapDomain (univLift K f a).onE (pathChain _) = _
  rwd [← pathChain_map]
  exact congrArg pathChain (uLiftPath_univLiftV a f p v b hp).symm

theorem uCoverPathTransport_pathChain {c}
    (hc : IsPathX K c a b) v
    {p} {d}
    (hp : IsPathX K p (endV v) d) :
    chain1 (uCoverPathTransport hc) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p ((uCoverPathTransport hc).onV v)) := by
  change Finsupp.mapDomain (uCoverPathTransport hc).onE (pathChain _) = _
  rwd [← pathChain_map]
  exact congrArg pathChain (uLiftPath_pathTransportV hc p v d hp).symm

theorem univDeck_pathChain a g v
    {p} {b}
    (hp : IsPathX K p (endV v) b) :
    chain1 ((univDeck K a).cellHom g) (pathChain (uLiftPath p v)) =
      pathChain (uLiftPath p (deckV g v)) := by
  change Finsupp.mapDomain ((univDeck K a).cellHom g).onE (pathChain (uLiftPath p v)) = _
  rwd [← pathChain_map _]
  exact congrArg pathChain (uLiftPath_deckV g p v b hp).symm

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
open scoped Classical
variable (q : ℕ) [NeZero q]

abbrev spineOldBase := posQCube (gBase q)
abbrev spineOldCx := orderCx (QOld (cmpRel (GenusVertex q)))

def spineOldMarking (i : Fin q × Bool) : List ((spineOldCx q).E × Bool) :=
  mapPath (genusSpineToOld q) (spineMarkedLoop q i).1

def surfaceOldMarking (i : Fin q × Bool) : List ((spineOldCx q).E × Bool) :=
  mapPath (surfCx _) (gSig q (i.1.val, i.2))

theorem spineOldMarking_isPath i :
    IsPathX (spineOldCx q) (spineOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath _ (spineMarkedLoop q i).2

theorem surfaceOldMarking_isPath i :
    IsPathX (spineOldCx q) (surfaceOldMarking q i)
      (spineOldBase q) (spineOldBase q) :=
  isPath_mapPath _ (isPath_gSig q _)

theorem exists_spineOldMarkingCorrection i :
    ∃ d : (uCover (spineOldCx q) (spineOldBase q)).F →₀ ℤ,
      Comb.bdry2 _ d =
        pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
          pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) := (htpy_uLiftPath (c := UV.base _ _)
    (spineOldMarking_isPath q i) (spineMarkedLoop_toOld_htpy q i)).exists_boundary

def spineOldMarkingCorrection (i : Fin q × Bool) :=
  Classical.choose (exists_spineOldMarkingCorrection q i)

theorem spineOldMarkingCorrection_boundary i :
    Comb.bdry2 _ (spineOldMarkingCorrection q i) =
      pathChain (uLiftPath (spineOldMarking q i) (UV.base _ (spineOldBase q))) -
        pathChain (uLiftPath (surfaceOldMarking q i) (UV.base _ (spineOldBase q))) :=
  Classical.choose_spec (exists_spineOldMarkingCorrection q i)

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def oldIntoNamedQuotient :
    Hom (spineOldCx q) (orderCx (namedQuotientPos ρ q u)) :=
  orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone

theorem oldCylinderPath_isPath :
    IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt (spineQuotientCylinderPath q ρ u)
      (namedQuotientBase ρ q u) ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) :=
  by tauto

def quotientCylinderVertex :
    UV (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  UV.mk ⟨spineQuotientCylinderPath q ρ u, by
    tauto⟩

theorem quotientCylinderVertex_end :
    endV (quotientCylinderVertex q ρ u) =
      (oldIntoNamedQuotient q ρ u).onV (spineOldBase q) :=
  by rfl

/-- Every face of this lift is an actual old face of the quotient. -/
def oldCoverToNamedQuotient :=
  (uCoverPathTransport (oldCylinderPath_isPath q ρ u)).comp
    (univLift _ _ _)

theorem oldCoverToNamedQuotient_pathChain b
    (hp : IsPathX (spineOldCx q) p (spineOldBase q) b) :
    chain1 (oldCoverToNamedQuotient q ρ u)
      (pathChain (uLiftPath p (UV.base (spineOldCx q) (spineOldBase q)))) =
      pathChain (uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) p)
        (quotientCylinderVertex q ρ u)) := by
  rwd [oldCoverToNamedQuotient, chain1_comp_apply, univLift_pathChain _ _ _ hp]
  rwd [uCoverPathTransport_pathChain _ _ (isPath_mapPath _ hp)]
  congr 2

theorem receivedSpineToQuotient_root
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    (receivedSpineToQuotient q ρ u hrho).onV (g, (markedSpineTree q).root) =
      deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u) := by
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (deckV (finiteSpineOldRootReceiver q ρ u hrho g)
      (SpanningTree.mappedTreeReference _
        _ (markedSpineTree q).root)) = _
  simp [SpanningTree.mappedTreeReference, SpanningTree.treePath_root,
    mapPath, List.map_nil, extendList_nil]
  rwd [uCoverPathTransport_deckV, uCoverPathTransport_base]
  change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
    (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
      (finiteSpineToQuotient ρ q u hrho g))) (quotientCylinderVertex q ρ u) = _
  simp [pi1Conj_cancel_reverse]

def quotientMarkingCorrection
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :=
  (univDeck _ _).faceChains
    (finiteSpineToQuotient ρ q u hrho g)
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

/-- The correction is lifted in the old subcomplex before translation;
its boundary changes exactly the two chosen marking paths. -/
theorem quotientMarkingCorrection_boundary
    g i :
    Comb.bdry2 _ (quotientMarkingCorrection q ρ u hrho g i) =
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) -
      pathChain (uLiftPath
        (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u))) := by
  rwd [quotientMarkingCorrection, DeckAction.faceChains_boundary, bdry2_chain2,
    spineOldMarkingCorrection_boundary, map_sub, map_sub]
  rwd [oldCoverToNamedQuotient_pathChain q ρ u _ (spineOldMarking_isPath q i),
    oldCoverToNamedQuotient_pathChain q ρ u _ (surfaceOldMarking_isPath q i)]
  have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := isPath_mapPath _ (spineOldMarking_isPath q i)
  have hs : IsPath (orderCx (namedQuotientPos ρ q u)).src
      (orderCx (namedQuotientPos ρ q u)).tgt
      (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
      (endV (quotientCylinderVertex q ρ u))
      ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := isPath_mapPath _ (surfaceOldMarking_isPath q i)
  simp [univDeck_pathChain _ _ _ hp, univDeck_pathChain _ _ _ hs]

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
    c :
    Comb.bdry2 _ (quotientMarkingCorrections q ρ u hrho c) =
      quotientSpineMarkingChains q ρ u hrho c - quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rwd [map_add, map_add, hc, hd, map_add, map_add]
      abel
  | single x n =>
      simp [quotientMarkingCorrections, quotientSpineMarkingChains,
        quotientSurfaceMarkingChains, Finsupp.linearCombination_single, map_smul,
        quotientMarkingCorrection_boundary, smul_sub]

theorem markedSpineToNamedQuotient_marking_path i :
    mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1 =
      mapPath (oldIntoNamedQuotient q ρ u) (spineOldMarking q i) := by
  rwd [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]
  rfl

/-- The abstractly indexed marked chain map agrees exactly with the actual
translated lifted marking paths at the cylinder endpoint. -/
theorem quotientSpineMarkingChains_eq
    c :
    chain1 (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u))
      (ReceivedTree.geometricMarkedChainMap (markedSpineTree q)
        (markedSpineToNamedQuotient q ρ u) (finiteSpineOldRootReceiver q ρ u hrho)
        (treeMarkedSpineLoop q) c) = quotientSpineMarkingChains q ρ u hrho c := by
  lin_ind c x n =>
      obtain ⟨g, i⟩ := x
      rwd [ReceivedTree.geometricMarkedChainMap, Finsupp.linearCombination_single,
        map_smul, quotientSpineMarkingChains, Finsupp.linearCombination_single]
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (markedSpineToNamedQuotient q ρ u) (treeMarkedSpineLoop q i).1)
          (endV (ReceivedTree.receiverVertex _
            _
            (finiteSpineOldRootReceiver q ρ u hrho) g (markedSpineTree q).root))
          ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) := by
        rwd [ReceivedTree.receiverVertex_end]
        exact isPath_mapPath _ (treeMarkedSpineLoop q i).2
      rwd [uCoverPathTransport_pathChain _ _ hp, markedSpineToNamedQuotient_marking_path]
      rwd [receivedSpineToQuotient_root]

def quotientCorrectedRelativeChain
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  chain2 (receivedSpineToQuotient q ρ u hrho)
    (receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit β) -
      quotientMarkingCorrections q ρ u hrho
        ((ReceivedTree.cellCoordinates _).symm (fun i => β (Sum.inr i)))

/-- Starting with the actual B2 coordinate equation now gives an actual
old two-chain whose boundary lies on the attaching surface with exactly the
original marked coefficients. No absolute-cycle assumption is added. -/
theorem quotientCorrectedRelativeChain_boundary
    β
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    Comb.bdry2 _ (quotientCorrectedRelativeChain q ρ u hrho β) =
      quotientSurfaceMarkingChains q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  rwd [quotientCorrectedRelativeChain, map_sub,
    receivedSpineToQuotient_relative_boundary q ρ u hrho β hβ,
    quotientSpineMarkingChains_eq, quotientMarkingCorrections_boundary]
  abel
