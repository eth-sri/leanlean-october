module

public import RequestProject.NormalizedMarkedPathCoefficients
public import RequestProject.GenusAllQuotientCorrections
public import RequestProject.GenusAttachingRelativeOldBoundary

@[expose] public section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedSurfaceForward : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
  attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

theorem namedSurfaceForward_monotone : Monotone (namedSurfaceForward q ρ u) :=
  attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)

abbrev namedAttachingSurfaceChain1 :=
  attachingSurfaceChain1 (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

abbrev namedAttachingDeckHom (g : QuotientMarkingGroup q ρ u) :=
  orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone

theorem exists_referenceMarkingFirst (i : Fin q × Bool) :
    ∃ e : OrdEdge (namedAttachingCover q ρ u),
      ∃ p : List (OrdEdge (namedAttachingCover q ρ u) × Bool),
        namedAttachingMarkingPath q ρ u hrho 1 i = (e, true) :: p ∧
        e.1.1 = namedAttachingReference q ρ u hrho 1 ∧
        (namedAttachingProjection q ρ u).onE e = markingFirstEdge q i ∧
        mapPath (namedAttachingProjection q ρ u) p = markingTail q i := by
  obtain ⟨hs, hm⟩ := namedAttachingMarkingPath_spec q ρ u hrho 1 i
  rw [gSig_first_edge] at hm
  rcases hp : namedAttachingMarkingPath q ρ u hrho 1 i with _ | ⟨⟨e, b⟩, p⟩
  · simp [hp] at hm
  · rw [hp] at hs hm
    obtain ⟨⟨he, rfl⟩, htail⟩ :
        ((namedAttachingProjection q ρ u).onE e = markingFirstEdge q i ∧ b = true) ∧
        mapPath (namedAttachingProjection q ρ u) p = markingTail q i := by
      simpa [mapPath] using hm
    exact ⟨e, p, rfl, hs.1.symm, he, htail⟩

def referenceMarkingFirst (i : Fin q × Bool) : OrdEdge (namedAttachingCover q ρ u) :=
  (exists_referenceMarkingFirst q ρ u hrho i).choose

def referenceMarkingTail (i : Fin q × Bool) :
    List (OrdEdge (namedAttachingCover q ρ u) × Bool) :=
  (exists_referenceMarkingFirst q ρ u hrho i).choose_spec.choose

theorem referenceMarkingFirst_spec (i : Fin q × Bool) :
    namedAttachingMarkingPath q ρ u hrho 1 i =
        (referenceMarkingFirst q ρ u hrho i, true) :: referenceMarkingTail q ρ u hrho i ∧
      (referenceMarkingFirst q ρ u hrho i).1.1 = namedAttachingReference q ρ u hrho 1 ∧
      (namedAttachingProjection q ρ u).onE (referenceMarkingFirst q ρ u hrho i) =
        markingFirstEdge q i ∧
      mapPath (namedAttachingProjection q ρ u) (referenceMarkingTail q ρ u hrho i) =
        markingTail q i :=
  (exists_referenceMarkingFirst q ρ u hrho i).choose_spec.choose_spec

def allNamedAttachingMarkingPath (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  mapPath (namedAttachingDeckHom q ρ u g) (namedAttachingMarkingPath q ρ u hrho 1 i)

def allNamedAttachingFirst (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  (namedAttachingDeckHom q ρ u g).onE (referenceMarkingFirst q ρ u hrho i)

def allNamedAttachingTail (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  mapPath (namedAttachingDeckHom q ρ u g) (referenceMarkingTail q ρ u hrho i)

theorem allNamedAttachingFirst_lastEndpoints (g : QuotientMarkingGroup q ρ u)
    (i : Fin q × Bool) :
    (namedSurfaceProjection ρ q u
        (namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1),
      namedSurfaceProjection ρ q u
        (namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2)) =
      (markingBaseCell q, markingBedCell q i false) := by
  have he := (referenceMarkingFirst_spec q ρ u hrho i).2.2.1
  have hs : qAttachingCoverEnd (namedQuotientBase ρ q u)
      (referenceMarkingFirst q ρ u hrho i).1.1 = (markingFirstEdge q i).1.1 :=
    congrArg (fun e : MarkingSurfaceEdge q => e.1.1) he
  have ht : qAttachingCoverEnd (namedQuotientBase ρ q u)
      (referenceMarkingFirst q ρ u hrho i).1.2 = (markingFirstEdge q i).1.2 :=
    congrArg (fun e : MarkingSurfaceEdge q => e.1.2) he
  change (chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.1)),
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.2))) = _
  rw [namedAttachingDeck_projection, namedAttachingDeck_projection, hs, ht]
  simp only [markingFirstEdge, markingBaseFlag, chainMax_spx1, chainMax_spx2]

def allNamedSurfaceFirst (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    StrictOrdEdge (NamedSurfaceCover ρ q u) :=
  ⟨(namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1,
      namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2),
    lt_of_le_of_ne ((namedSurfaceForward_monotone q ρ u)
      (allNamedAttachingFirst q ρ u hrho g i).2) fun he => by
      obtain ⟨hs, ht⟩ := Prod.mk.inj (allNamedAttachingFirst_lastEndpoints q ρ u hrho g i)
      exact nomatch hs.symm.trans ((congrArg (namedSurfaceProjection ρ q u) he).trans ht)⟩

theorem allNamedSurfaceFirst_injective :
    Function.Injective (fun x : QuotientMarkingGroup q ρ u × (Fin q × Bool) =>
      allNamedSurfaceFirst q ρ u hrho x.1 x.2) := by
  have hsrc (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
      (allNamedSurfaceFirst q ρ u hrho g i).1.1 =
        namedSurfaceDeck ρ q u g
          (namedSurfaceForward q ρ u (namedAttachingReference q ρ u hrho 1)) := by
    change namedSurfaceForward q ρ u
        (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.1) = _
    rw [(referenceMarkingFirst_spec q ρ u hrho i).2.1]
    exact namedAttachingToSurface_deck ρ q u g _
  intro x y h
  have hs := congrArg (fun e : StrictOrdEdge (NamedSurfaceCover ρ q u) => e.1.1) h
  dsimp only at hs; rw [hsrc, hsrc] at hs
  have hg' : x.1 = y.1 := deckV_injective_in_group _
    (namedSurfaceForward q ρ u (namedAttachingReference q ρ u hrho 1)).1.1
    (congrArg (fun v : NamedSurfaceCover ρ q u => v.1.1) hs)
  have ht : markingBedCell q x.2 false = markingBedCell q y.2 false :=
    (Prod.mk.inj (allNamedAttachingFirst_lastEndpoints q ρ u hrho x.1 x.2)).2.symm.trans
      ((congrArg (fun e : StrictOrdEdge (NamedSurfaceCover ρ q u) =>
        namedSurfaceProjection ρ q u e.1.2) h).trans
        (Prod.mk.inj (allNamedAttachingFirst_lastEndpoints q ρ u hrho y.1 y.2)).2)
  exact Prod.ext hg' (congrArg (fun z : Fin q × Bool × Bool => (z.1, z.2.1)) (Cell.bed.inj ht))

theorem allNamedAttachingTail_surface_avoids (g h : QuotientMarkingGroup q ρ u)
    (i j : Fin q × Bool) (a : OrdEdge (namedAttachingCover q ρ u) × Bool)
    (ha : a ∈ allNamedAttachingTail q ρ u hrho h j) :
    (namedSurfaceForward q ρ u a.1.1.1, namedSurfaceForward q ρ u a.1.1.2) ≠
      (allNamedSurfaceFirst q ρ u hrho g i).1 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hb' : ((namedAttachingProjection q ρ u).onE b.1, b.2) ∈ markingTail q j := by
    rw [← (referenceMarkingFirst_spec q ρ u hrho j).2.2.2]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  intro he
  have hp := (congrArg (fun z : NamedSurfaceCover ρ q u × NamedSurfaceCover ρ q u =>
    (namedSurfaceProjection ρ q u z.1, namedSurfaceProjection ρ q u z.2)) he).trans
      (allNamedAttachingFirst_lastEndpoints q ρ u hrho g i)
  change (chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u h b.1.1.1)),
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u h b.1.1.2))) = _ at hp
  rw [namedAttachingDeck_projection, namedAttachingDeck_projection] at hp
  change (chainMax (((namedAttachingProjection q ρ u).onE b.1, b.2).1.1.1),
    chainMax (((namedAttachingProjection q ρ u).onE b.1, b.2).1.1.2)) = _ at hp
  generalize ((namedAttachingProjection q ρ u).onE b.1, b.2) = c at hb' hp
  revert hp
  simp only [markingTail, List.mem_cons, List.not_mem_nil, or_false] at hb'
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [markingBedBaseFlag, markingBedMidFlag, markingMidFlag, markingBaseFlag,
      markingBaseCell, markingBedCell, markingMidCell] <;> intro hp
  · cases hp
  · cases hp
  · exact nomatch congrArg (fun z : Fin q × Bool × Bool => z.2.2) (Cell.bed.inj hp)

def allNamedAttachingMarkingChains :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (allNamedAttachingMarkingPath q ρ u hrho x.1 x.2))

def allNamedSurfaceMarkingChains :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  (normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)).comp
    (allNamedAttachingMarkingChains q ρ u hrho)

theorem allNamedSurfaceMarkingChains_injective :
    Function.Injective (allNamedSurfaceMarkingChains q ρ u hrho) := by
  have hcoeff (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
      (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
      allNamedSurfaceMarkingChains q ρ u hrho c (allNamedSurfaceFirst q ρ u hrho g i) = c (g, i) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
    | single x n =>
        have hcons : allNamedAttachingMarkingPath q ρ u hrho x.1 x.2 =
            (allNamedAttachingFirst q ρ u hrho x.1 x.2, true) ::
              allNamedAttachingTail q ρ u hrho x.1 x.2 := by
          simpa only [allNamedAttachingMarkingPath, allNamedAttachingFirst,
            allNamedAttachingTail, mapPath, List.map_cons] using
            congrArg (mapPath (namedAttachingDeckHom q ρ u x.1))
              (referenceMarkingFirst_spec q ρ u hrho x.2).1
        change normalizedWeakChain1To _ _
          (allNamedAttachingMarkingChains q ρ u hrho (Finsupp.single x n)) _ = _
        rw [allNamedAttachingMarkingChains, Finsupp.linearCombination_single ℤ, map_zsmul,
          Finsupp.smul_apply, hcons,
          normalizedWeakChain1To_positive_first_coefficient _ _ _ _
            (allNamedSurfaceFirst q ρ u hrho x.1 x.2) _ rfl
            (allNamedAttachingTail_surface_avoids q ρ u hrho g x.1 i x.2)]
        have heq : allNamedSurfaceFirst q ρ u hrho x.1 x.2 =
            allNamedSurfaceFirst q ρ u hrho g i ↔ x = (g, i) :=
          ⟨@allNamedSurfaceFirst_injective q _ _ _ ρ u hrho x (g, i), fun h => h ▸ rfl⟩
        by_cases hx : x = (g, i) <;> simp only [heq, hx, ↓reduceIte, Finsupp.single_apply,
          smul_eq_mul, mul_one, mul_zero]
  intro c d he; ext x
  simpa only [hcoeff] using congrArg (· (allNamedSurfaceFirst q ρ u hrho x.1 x.2)) he

theorem namedAttachingIntoUniversal_chain1_injective :
    Function.Injective (chain1 (namedAttachingIntoUniversal q ρ u)) :=
  Finsupp.mapDomain_injective fun _ _ h => by
    have he := uOrderEdge_injective h
    exact Subtype.ext (Prod.ext (Subtype.ext (congrArg (·.1.1) he))
      (Subtype.ext (congrArg (·.1.2) he)))

theorem allNamedAttachingMarkingChains_image
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u) (allNamedAttachingMarkingChains q ρ u hrho c) =
      allQuotientSurfaceMarkingChains q ρ u c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x n =>
      simp only [allNamedAttachingMarkingChains, allQuotientSurfaceMarkingChains,
        liftedMarkingChainMap, Finsupp.linearCombination_single ℤ, map_smul]
      erw [Finsupp.linearCombination_single ℤ]
      refine congrArg (n • ·) ?_
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
        simp only [map_one, deckV_one]
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
          (endV (quotientCylinderVertex q ρ u))
          ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
        rw [quotientCylinderVertex_end]
        exact isPath_mapPath _ (surfaceOldMarking_isPath q x.2)
      unfold allNamedAttachingMarkingPath
      rw [mapPath, pathChain_map]
      change chain1 (namedAttachingIntoUniversal q ρ u)
        (chain1 (namedAttachingDeckHom q ρ u x.1)
          (pathChain (namedAttachingMarkingPath q ρ u hrho 1 x.2))) = _
      rw [namedAttachingIntoUniversal_chain1_deck, hbase]
      simpa only [quotientSurfaceMarking_first_edge, allQuotientMarkingVertex] using
        univDeck_pathChain (K := orderCx (namedQuotientPos ρ q u))
          (namedQuotientBase ρ q u) x.1 (quotientCylinderVertex q ρ u) hp

theorem namedSurfaceMarkingChains_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
        (namedAttachingMarkingChains q ρ u hrho c) =
      allNamedSurfaceMarkingChains q ρ u hrho
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) :=
  congrArg (normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
    (namedAttachingIntoUniversal_chain1_injective q ρ u (by
      rw [namedAttachingMarkingChains_image, allNamedAttachingMarkingChains_image,
        quotientSurfaceMarkingChains_factor]))

theorem allNamedSurfaceMarkingChains_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allNamedSurfaceMarkingChains q ρ u hrho (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (allNamedSurfaceMarkingChains q ρ u hrho c)) w.coeff := by
  have htr (g : QuotientMarkingGroup q ρ u) :
      allNamedSurfaceMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c) =
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (allNamedSurfaceMarkingChains q ρ u hrho c) := by
    have hatt : allNamedAttachingMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c) =
        chain1 (namedAttachingDeckHom q ρ u g) (allNamedAttachingMarkingChains q ρ u hrho c) :=
      namedAttachingIntoUniversal_chain1_injective q ρ u (by
        rw [allNamedAttachingMarkingChains_image, namedAttachingIntoUniversal_chain1_deck,
          allNamedAttachingMarkingChains_image, allQuotientSurfaceMarkingChains_translate])
    have hsq : (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)).comp
          (namedAttachingDeckHom q ρ u g) =
        (orderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).monotone).comp
          (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)) :=
      Hom.ext' (funext (namedAttachingToSurface_deck ρ q u g))
        (funext fun _ => Subtype.ext (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
          (namedAttachingToSurface_deck ρ q u g _)))
        (funext fun _ => Subtype.ext (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
          (Prod.ext (namedAttachingToSurface_deck ρ q u g _)
            (namedAttachingToSurface_deck ρ q u g _))))
    change normalizeOrdChain1
      (chain1 (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
        (allNamedAttachingMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c))) = _
    rw [hatt, ← chain1_comp_apply, hsq, chain1_comp_apply,
      normalizeOrdChain1_strict_map (namedSurfaceDeck ρ q u g)
        (namedSurfaceDeck ρ q u g).strictMono]
    rfl
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      have hm : ReceivedTree.multiplyCellChain c (MonoidAlgebra.single g n) =
          n • ReceivedTree.translateCellChain g c := by
        simp [ReceivedTree.multiplyCellChain]
      rw [hm, map_zsmul, htr, MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]

theorem namedSurfaceMarking_multiple_reflect
    (c d : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)
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
  change normalizedChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
      (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho c)) =
    Finsupp.linearCombination ℤ (fun g =>
      chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (normalizedChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
          (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho d)))) w.coeff at h
  simp only [← normalizedWeakChain1To_normalize, namedSurfaceMarkingChains_factor] at h
  rw [← allNamedSurfaceMarkingChains_multiply] at h
  simp only [quotientSurfaceMarkingChains_factor,
    allNamedSurfaceMarkingChains_injective q ρ u hrho h, allQuotientSurfaceMarkingChains_multiply]
