import RequestProject.NormalizedMarkedPathCoefficients
import RequestProject.GenusAllQuotientCorrections
import RequestProject.GenusAttachingRelativeOldBoundary
import RequestProject.Tac


/-! Sheetwise marking coefficients survive the actual lower-lift / chainMax
map and order normalization. Written proof terms; no Lean run performed. -/
noncomputable section
open scoped Classical
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedSurfaceForward : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
  attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

theorem namedSurfaceForward_monotone : Monotone (namedSurfaceForward q ρ u) :=
  attachingToSurfaceCover_monotone _
    _ _

abbrev namedAttachingSurfaceChain1 :=
  attachingSurfaceChain1 (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

abbrev namedAttachingDeckHom (g : QuotientMarkingGroup q ρ u) :=
  orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone

theorem exists_referenceMarkingFirst i :
    ∃ e,
      ∃ p : List (OrdEdge (namedAttachingCover q ρ u) × Bool),
        namedAttachingMarkingPath q ρ u hrho 1 i = (e, true) :: p ∧
        e.1.1 = namedAttachingReference q ρ u hrho 1 ∧
        (namedAttachingProjection q ρ u).onE e = markingFirstEdge q i ∧
        mapPath (namedAttachingProjection q ρ u) p = markingTail q i := by
  have hm := (namedAttachingMarkingPath_spec q ρ u hrho 1 i).2
  rw [gSig_first_edge] at hm
  cases hp : namedAttachingMarkingPath q ρ u hrho 1 i with
  | nil =>
      simp_all
  | cons a p =>
      have hm' : ((namedAttachingProjection q ρ u).onE a.1, a.2) =
          (markingFirstEdge q i, true) ∧
          mapPath (namedAttachingProjection q ρ u) p = markingTail q i := by
        simp_all [hp, mapPath, List.map_cons, List.cons.injEq]
      have hs := (namedAttachingMarkingPath_spec q ρ u hrho 1 i).1
      aesop

def referenceMarkingFirst (i : Fin q × Bool) :=
  Classical.choose (exists_referenceMarkingFirst q ρ u hrho i)

def referenceMarkingTail (i : Fin q × Bool) :=
  Classical.choose (Classical.choose_spec (exists_referenceMarkingFirst q ρ u hrho i))

theorem referenceMarkingFirst_spec i :
    namedAttachingMarkingPath q ρ u hrho 1 i =
        (referenceMarkingFirst q ρ u hrho i, true) :: referenceMarkingTail q ρ u hrho i ∧
      (referenceMarkingFirst q ρ u hrho i).1.1 = namedAttachingReference q ρ u hrho 1 ∧
      (namedAttachingProjection q ρ u).onE (referenceMarkingFirst q ρ u hrho i) =
        markingFirstEdge q i ∧
      mapPath (namedAttachingProjection q ρ u) (referenceMarkingTail q ρ u hrho i) =
        markingTail q i :=
  Classical.choose_spec (Classical.choose_spec (exists_referenceMarkingFirst q ρ u hrho i))

def allNamedAttachingMarkingPath (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  mapPath (namedAttachingDeckHom q ρ u g) (namedAttachingMarkingPath q ρ u hrho 1 i)

def allNamedAttachingFirst (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  (namedAttachingDeckHom q ρ u g).onE (referenceMarkingFirst q ρ u hrho i)

def allNamedAttachingTail (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  mapPath (namedAttachingDeckHom q ρ u g) (referenceMarkingTail q ρ u hrho i)

theorem allNamedAttachingMarkingPath_cons g
    i :
    allNamedAttachingMarkingPath q ρ u hrho g i =
      (allNamedAttachingFirst q ρ u hrho g i, true) :: allNamedAttachingTail q ρ u hrho g i := by
  simpa [allNamedAttachingMarkingPath, allNamedAttachingFirst,
    allNamedAttachingTail, mapPath, List.map_cons] using
    congrArg (mapPath (namedAttachingDeckHom q ρ u g))
      (referenceMarkingFirst_spec q ρ u hrho i).1

theorem allNamedAttachingFirst_lastEndpoints g
    i :
    (namedSurfaceProjection ρ q u
        (namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1),
      namedSurfaceProjection ρ q u
        (namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2)) =
      (markingBaseCell q, markingBedCell q i false) := by
  have he := (referenceMarkingFirst_spec q ρ u hrho i).2.2.1
  have hs := congrArg (·.1.1) he
  have ht := congrArg (·.1.2) he
  change qAttachingCoverEnd _
    (referenceMarkingFirst q ρ u hrho i).1.1 = (markingFirstEdge q i).1.1 at hs
  change qAttachingCoverEnd _
    (referenceMarkingFirst q ρ u hrho i).1.2 = (markingFirstEdge q i).1.2 at ht
  change (chainMax (qAttachingCoverEnd _
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.1)),
    chainMax (qAttachingCoverEnd _
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.2))) = _
  simp [namedAttachingDeck_projection, hs, ht, markingFirstEdge, markingBaseFlag, chainMax_spx1, chainMax_spx2]

theorem allNamedAttachingFirst_surface_strict g
    i :
    namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1 <
      namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2 := by
  apply lt_of_le_of_ne ((namedSurfaceForward_monotone q ρ u)
    (by grind))
  intro he
  have hp := allNamedAttachingFirst_lastEndpoints q ρ u hrho g i
  have hs := congrArg Prod.fst hp
  have ht := congrArg Prod.snd hp
  have hh := congrArg (namedSurfaceProjection ρ q u) he
  dsimp at hs ht
  rw [hs, ht] at hh
  cases hh

def allNamedSurfaceFirst (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    StrictOrdEdge (NamedSurfaceCover ρ q u) :=
  ⟨(namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1,
      namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2),
    allNamedAttachingFirst_surface_strict q ρ u hrho g i⟩

theorem allNamedSurfaceFirst_source g
    i :
    (allNamedSurfaceFirst q ρ u hrho g i).1.1 =
      namedSurfaceDeck ρ q u g
        (namedSurfaceForward q ρ u (namedAttachingReference q ρ u hrho 1)) := by
  change namedSurfaceForward q ρ u
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.1) = _
  rw [(referenceMarkingFirst_spec q ρ u hrho i).2.1]
  exact namedAttachingToSurface_deck ρ q u g _

theorem allNamedSurfaceFirst_target_projection g
    i :
    namedSurfaceProjection ρ q u (allNamedSurfaceFirst q ρ u hrho g i).1.2 =
      markingBedCell q i false :=
  congrArg Prod.snd (allNamedAttachingFirst_lastEndpoints q ρ u hrho g i)

theorem allNamedSurfaceFirst_injective :
    Function.Injective (fun x : QuotientMarkingGroup q ρ u × (Fin q × Bool) =>
      allNamedSurfaceFirst q ρ u hrho x.1 x.2) := by
  intro x y h
  have hs := congrArg (·.1.1) h
  rw [allNamedSurfaceFirst_source, allNamedSurfaceFirst_source] at hs
  have hg := congrArg (·.1.1) hs
  have hg' := deckV_injective_in_group _
    _ hg
  have ht := congrArg (fun e =>
    namedSurfaceProjection ρ q u e.1.2) h
  rw [allNamedSurfaceFirst_target_projection, allNamedSurfaceFirst_target_projection] at ht
  have hi := congrArg (fun z => (z.1, z.2.1)) (Cell.bed.inj ht)
  grind

theorem markingTail_lastEndpoints_avoids i j
    a (ha : a ∈ markingTail q j) :
    (chainMax a.1.1.1, chainMax a.1.1.2) ≠
      (markingBaseCell q, markingBedCell q i false) := by
  simp [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [markingBedBaseFlag, markingBedMidFlag, markingMidFlag, markingBaseFlag,
      markingBaseCell, markingBedCell, markingMidCell]
  all_goals intro h
  · cases h
  · cases h
  grind

theorem allNamedAttachingTail_surface_avoids g h
    i j (a : OrdEdge (namedAttachingCover q ρ u) × Bool)
    (ha : a ∈ allNamedAttachingTail q ρ u hrho h j) :
    (namedSurfaceForward q ρ u a.1.1.1, namedSurfaceForward q ρ u a.1.1.2) ≠
      (allNamedSurfaceFirst q ρ u hrho g i).1 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hb' : ((namedAttachingProjection q ρ u).onE b.1, b.2) ∈ markingTail q j := by
    rw [← (referenceMarkingFirst_spec q ρ u hrho j).2.2.2]
    exact List.mem_map.mpr (by grind)
  intro he
  have hp := (congrArg (fun z =>
    (namedSurfaceProjection ρ q u z.1, namedSurfaceProjection ρ q u z.2)) he).trans
      (allNamedAttachingFirst_lastEndpoints q ρ u hrho g i)
  change (chainMax (qAttachingCoverEnd _
      (namedAttachingDeck ρ q u h b.1.1.1)),
    chainMax (qAttachingCoverEnd _
      (namedAttachingDeck ρ q u h b.1.1.2))) = _ at hp
  rw [namedAttachingDeck_projection, namedAttachingDeck_projection] at hp
  exact markingTail_lastEndpoints_avoids q i j _ hb' hp

def allNamedAttachingMarkingChains :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (allNamedAttachingMarkingPath q ρ u hrho x.1 x.2))

def allNamedSurfaceMarkingChains :=
  (normalizedWeakChain1To _ (namedSurfaceForward_monotone q ρ u)).comp
    (allNamedAttachingMarkingChains q ρ u hrho)

theorem allNamedSurfaceMarkingChains_coefficient
    c
    g i :
    allNamedSurfaceMarkingChains q ρ u hrho c (allNamedSurfaceFirst q ρ u hrho g i) = c (g, i) := by
  lin_ind c x n =>
      change normalizedWeakChain1To _ _
        (allNamedAttachingMarkingChains q ρ u hrho (Finsupp.single x n)) _ = _
      rw [allNamedAttachingMarkingChains, Finsupp.linearCombination_single ℤ, map_zsmul,
        Finsupp.smul_apply, allNamedAttachingMarkingPath_cons,
        normalizedWeakChain1To_positive_first_coefficient _ _ _ _
          (allNamedSurfaceFirst q ρ u hrho x.1 x.2) _ rfl
          (allNamedAttachingTail_surface_avoids q ρ u hrho g x.1 i x.2)]
      have hinj := allNamedSurfaceFirst_injective q ρ u hrho
      have heq : allNamedSurfaceFirst q ρ u hrho x.1 x.2 =
          allNamedSurfaceFirst q ρ u hrho g i ↔ x = (g, i) := by
        constructor
        · tauto
        simp_all
      aesop

theorem allNamedSurfaceMarkingChains_injective :
    Function.Injective (allNamedSurfaceMarkingChains q ρ u hrho) := by
  intro c d he
  ext x
  have h := congrArg (fun z =>
    z (allNamedSurfaceFirst q ρ u hrho x.1 x.2)) he
  simpa [allNamedSurfaceMarkingChains_coefficient] using h

theorem namedAttachingIntoUniversal_chain1_injective :
    Function.Injective (chain1 (namedAttachingIntoUniversal q ρ u)) := by
  apply Finsupp.mapDomain_injective
  intro e f h
  have he := uOrderEdge_injective h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg (·.1.1) he))
    (Subtype.ext (congrArg (·.1.2) he))

theorem allNamedAttachingMarkingChains_image
    c :
    chain1 (namedAttachingIntoUniversal q ρ u) (allNamedAttachingMarkingChains q ρ u hrho c) =
      allQuotientSurfaceMarkingChains q ρ u c := by
  lin_ind c x n =>
      simp [allNamedAttachingMarkingChains, allQuotientSurfaceMarkingChains,
        liftedMarkingChainMap, Finsupp.linearCombination_single ℤ, map_smul]
      erw [Finsupp.linearCombination_single ℤ]
      apply congrArg _
      have hbase : chain1 (namedAttachingIntoUniversal q ρ u)
          (pathChain (namedAttachingMarkingPath q ρ u hrho 1 x.2)) =
          pathChain (uLiftPath
            (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
            (quotientCylinderVertex q ρ u)) := by
        change Finsupp.mapDomain (namedAttachingIntoUniversal q ρ u).onE _ = _
        rw [← pathChain_map]
        change pathChain (mapPath (namedAttachingIntoUniversal q ρ u)
          (namedAttachingMarkingPath q ρ u hrho 1 x.2)) = _
        rw [namedAttachingMarkingPath_image]
        rfl
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
          (endV (quotientCylinderVertex q ρ u))
          ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := isPath_mapPath _ (surfaceOldMarking_isPath q x.2)
      unfold allNamedAttachingMarkingPath
      rw [mapPath, pathChain_map]
      change chain1 (namedAttachingIntoUniversal q ρ u)
        (chain1 (namedAttachingDeckHom q ρ u x.1)
          (pathChain (namedAttachingMarkingPath q ρ u hrho 1 x.2))) = _
      rw [namedAttachingIntoUniversal_chain1_deck, hbase]
      simpa [quotientSurfaceMarking_first_edge, allQuotientMarkingVertex] using
        univDeck_pathChain (K := orderCx (namedQuotientPos ρ q u))
          _ x.1 _ hp

theorem namedAttachingMarkingChains_factor
    c :
    namedAttachingMarkingChains q ρ u hrho c =
      allNamedAttachingMarkingChains q ρ u hrho
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  apply namedAttachingIntoUniversal_chain1_injective q ρ u
  rw [namedAttachingMarkingChains_image, allNamedAttachingMarkingChains_image,
    quotientSurfaceMarkingChains_factor]

theorem namedSurfaceMarkingChains_factor
    c :
    normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
        (namedAttachingMarkingChains q ρ u hrho c) =
      allNamedSurfaceMarkingChains q ρ u hrho
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := congrArg
    _
    (namedAttachingMarkingChains_factor q ρ u hrho c)

theorem allNamedAttachingMarkingChains_translate g
    c :
    allNamedAttachingMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c) =
      chain1 (namedAttachingDeckHom q ρ u g) (allNamedAttachingMarkingChains q ρ u hrho c) := by
  apply namedAttachingIntoUniversal_chain1_injective q ρ u
  rw [allNamedAttachingMarkingChains_image, namedAttachingIntoUniversal_chain1_deck,
    allNamedAttachingMarkingChains_image, allQuotientSurfaceMarkingChains_translate]

theorem namedSurfaceForward_deck_square g :
    (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)).comp
        (namedAttachingDeckHom q ρ u g) =
      (orderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).monotone).comp
        (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)) := by
  apply Hom.ext'
  · funext p
    exact namedAttachingToSurface_deck ρ q u g p
  · funext e
    apply Subtype.ext
    exact Prod.ext (namedAttachingToSurface_deck ρ q u g e.1.1)
      (namedAttachingToSurface_deck ρ q u g e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (namedAttachingToSurface_deck ρ q u g t.1.1)
      (Prod.ext (namedAttachingToSurface_deck ρ q u g t.1.2.1)
        (namedAttachingToSurface_deck ρ q u g t.1.2.2))

theorem allNamedSurfaceMarkingChains_translate g
    c :
    allNamedSurfaceMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c) =
      chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (allNamedSurfaceMarkingChains q ρ u hrho c) := by
  change normalizeOrdChain1
    (chain1 (orderCxMap _ (namedSurfaceForward_monotone q ρ u))
      (allNamedAttachingMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c))) = _
  rw [allNamedAttachingMarkingChains_translate, ← chain1_comp_apply,
    namedSurfaceForward_deck_square, chain1_comp_apply,
    normalizeOrdChain1_strict_map _
      _]
  rfl

theorem allNamedSurfaceMarkingChains_multiply
    w
    c :
    allNamedSurfaceMarkingChains q ρ u hrho (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (allNamedSurfaceMarkingChains q ρ u hrho c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      have hm : ReceivedTree.multiplyCellChain c (MonoidAlgebra.single g n) =
          n • ReceivedTree.translateCellChain g c := by
        simp [ReceivedTree.multiplyCellChain]
      rw [hm, map_zsmul, allNamedSurfaceMarkingChains_translate]
      simp


/-- Exact recovery in the entire quotient group from the normalized surface
boundary. The chain map need only be injective on these genuine markings. -/
theorem namedSurfaceMarking_multiple_reflect
    c d
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (h : namedAttachingSurfaceChain1 q ρ u
        (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho c)) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (namedAttachingSurfaceChain1 q ρ u
            (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho d)))) w.coeff) :
    quotientSurfaceMarkingChains q ρ u hrho c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
          (quotientSurfaceMarkingChains q ρ u hrho d)) w.coeff := by
  change normalizedChain1To _ (namedSurfaceForward_monotone q ρ u)
      (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho c)) =
    Finsupp.linearCombination ℤ (fun g =>
      chain1 (strictOrderCxMap _ (namedSurfaceDeck ρ q u g).strictMono)
        (normalizedChain1To _ (namedSurfaceForward_monotone q ρ u)
          (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho d)))) w.coeff at h
  simp [← normalizedWeakChain1To_normalize, namedSurfaceMarkingChains_factor] at h
  rw [← allNamedSurfaceMarkingChains_multiply] at h
  have hc := allNamedSurfaceMarkingChains_injective q ρ u hrho h
  simp [quotientSurfaceMarkingChains_factor, hc, allQuotientSurfaceMarkingChains_multiply]
