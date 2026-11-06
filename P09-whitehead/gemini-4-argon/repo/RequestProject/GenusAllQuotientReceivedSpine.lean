module

public import RequestProject.GenusReceivedCoveredSpine

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  {G H : Type u} [Group G] [Group H]
  (φ : PresGroup (SpanningTree.treeRel T) →* G) (η : G →* H)

theorem liftPath_map_group (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun eb => ((η eb.1.1, eb.1.2), eb.2)) =
      liftPath T (η.comp φ) p (η g) := by
  induction p generalizing g with
  | nil => rfl
  | cons e p ih =>
      erw [liftPath_cons, List.map_cons, liftPath_cons]
      have he : ((η (liftGerm T φ g e).1.1, (liftGerm T φ g e).1.2),
          (liftGerm T φ g e).2) = liftGerm T (η.comp φ) (η g) e := by
        rcases e with ⟨_, _ | _⟩ <;> simp [liftGerm, germValue, map_mul]
      erw [he, ih, map_mul]; rfl

def changeGroup : Hom (cover T φ) (cover T (η.comp φ)) where
  onV x := (η x.1, x.2)
  onE x := (η x.1, x.2)
  onF x := (η x.1, x.2)
  src_onE _ := rfl
  tgt_onE x := by
    change (η x.1 * η (germValue T φ (x.2, true)), _) =
      (η (x.1 * germValue T φ (x.2, true)), _)
    erw [map_mul]; rfl
  base_onF _ := rfl
  att_onF x := (liftPath_map_group T φ η (K.att x.2) x.1).symm

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def allQuotientSpineReceiver : PresGroup (spinePresentation q) →*
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (finiteSpineToQuotient ρ q u hrho).comp
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)

abbrev allQuotientReceivedSpineCover : Complex2 :=
  ReceivedTree.cover (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def allQuotientReceivedSpineProjection :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (markedSpineCx q) :=
  ReceivedTree.projection (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def receivedSpineChangeToAllQuotient :
    Hom (singleReceivedSpineCover q ρ u) (allQuotientReceivedSpineCover q ρ u hrho) :=
  ReceivedTree.changeGroup (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineToQuotient ρ q u hrho)

def allQuotientSpineOldRootReceiver :
    Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →*
      Pi1 (orderCx (namedQuotientPos ρ q u))
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) :=
  pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))

def allQuotientReceivedSpineToQuotient :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
      (allQuotientSpineReceiver q ρ u hrho) (allQuotientSpineOldRootReceiver q ρ u)
      (finiteSpineOldRootReceiver_compatible q ρ u hrho))

theorem allQuotientReceivedSpineToQuotient_projects :
    (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
      (allQuotientReceivedSpineToQuotient q ρ u hrho) =
      (markedSpineToNamedQuotient q ρ u).comp
        (allQuotientReceivedSpineProjection q ρ u hrho) :=
  Hom.ext' (funext fun x => by
    change endV (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (allQuotientSpineOldRootReceiver q ρ u) x.1 x.2)) = _
    erw [endV_pathTransportV, ReceivedTree.receiverVertex_end]; rfl) rfl rfl

theorem allQuotientReceivedSpineToQuotient_chain2_changeGroup
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x =>
        (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) =
      chain2 (receivedSpineToQuotient q ρ u hrho) c := by
  change chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
    (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) c) = _
  erw [← chain2_comp_apply, show (allQuotientReceivedSpineToQuotient q ρ u hrho).comp
    (receivedSpineChangeToAllQuotient q ρ u hrho) = receivedSpineToQuotient q ρ u hrho
    from Hom.ext' rfl rfl rfl]

theorem allQuotientReceivedSpineToQuotient_deckV
    (g h : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
    (a : (markedSpineCx q).V) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onV (g * h, a) =
      deckV g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV (h, a)) := by
  have hs : ReceivedTree.receiverVertex (markedSpineTree q)
      (markedSpineToNamedQuotient q ρ u) (allQuotientSpineOldRootReceiver q ρ u) (g * h) a =
      deckV (allQuotientSpineOldRootReceiver q ρ u g)
        (ReceivedTree.receiverVertex (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (allQuotientSpineOldRootReceiver q ρ u) h a) := by
    simp only [ReceivedTree.receiverVertex, map_mul, deckV_mul]
  change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
    (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
      (allQuotientSpineOldRootReceiver q ρ u) (g * h) a) = _
  erw [hs, uCoverPathTransport_deckV, pi1Conj_cancel_reverse]; rfl

theorem allQuotientReceivedSpineToQuotient_deckF
    (g h : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
    (f : (markedSpineCx q).F) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onF (g * h, f) =
      deckF g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onF (h, f)) :=
  Subtype.ext (Prod.ext (allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g h _) rfl)

def allQuotientReceivedSpineOrderMap :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (orderCx (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :=
  uOrderHomInv.comp (allQuotientReceivedSpineToQuotient q ρ u hrho)

theorem allQuotientReceivedSpineOrderMap_old (a : (allQuotientReceivedSpineCover q ρ u hrho).V) :
    InQOld (uOrderEnd ((allQuotientReceivedSpineOrderMap q ρ u hrho).onV a)) := by
  change InQOld (endV (uOrderHomInv.onV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a)))
  erw [uOrderHomInv_vertex]
  have h : endV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a) =
      (markedSpineToNamedQuotient q ρ u).onV a.2 :=
    congrArg (·.onV a) (allQuotientReceivedSpineToQuotient_projects q ρ u hrho)
  erw [h]; trivial

def allQuotientReceivedSpineToOldCover :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (orderCx (namedOldCover q ρ u)) :=
  orderCxRestrict (allQuotientReceivedSpineOrderMap q ρ u hrho)
    (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho)

def allQuotientReceivedSpineToStrictSpine :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (strictOrderCx (GenusSpineCell q)) :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (allQuotientReceivedSpineProjection q ρ u hrho)

theorem allQuotientReceivedSpine_old_square :
    (orderCxMap (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u).mono).comp
      (allQuotientReceivedSpineToOldCover q ρ u hrho) =
      (orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
        ((strictOrderIncl (GenusSpineCell q)).comp (allQuotientReceivedSpineToStrictSpine q ρ u hrho)) := by
  let j := orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone
  apply Hom.comp_left_cancel_of_injective j
    (fun _ _ h => Sum.inl.inj h)
    (fun _ _ h => Subtype.ext (Prod.ext
      (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.1) h))
      (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.2) h))))
    (fun _ _ h => Subtype.ext (Prod.ext
      (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.1) h))
      (Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.1) h))
        (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.2) h)))))
  calc
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        ((orderCxMap Subtype.val (fun _ _ h => h)).comp
          (allQuotientReceivedSpineToOldCover q ρ u hrho)) := by
      change (j.comp (orderCxMap (namedOldCoverProjection q ρ u)
        (namedOldCoverProjection_isPosetCover q ρ u).mono)).comp _ = _
      dsimp only [j, namedOldCoverProjection]
      erw [qOldCover_projection_square]; rfl
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (allQuotientReceivedSpineOrderMap q ρ u hrho) := by
      erw [allQuotientReceivedSpineToOldCover, orderCxRestrict_projects]
    _ = (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
        (allQuotientReceivedSpineToQuotient q ρ u hrho) := by
      change ((orderCxMap uOrderEnd uOrderEnd_monotone).comp uOrderHomInv).comp _ = _
      erw [uOrderHomInv_projection_square]
    _ = _ := allQuotientReceivedSpineToQuotient_projects q ρ u hrho

def allQuotientReceivedSpineToCoveredSpine :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u))) :=
  (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u))
    (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).strictMono).comp
    (strictOrderPullbackHom (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
      (genusSpineCellToOld_monotone q) (allQuotientReceivedSpineToOldCover q ρ u hrho)
      (allQuotientReceivedSpineToStrictSpine q ρ u hrho) (allQuotientReceivedSpine_old_square q ρ u hrho))

theorem allQuotientReceivedSpineToCoveredSpine_onF_injective :
    Function.Injective (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onF := by
  rintro ⟨g, t⟩ ⟨h, s⟩ he
  have hs : (allQuotientReceivedSpineToStrictSpine q ρ u hrho).onF (g, t) =
      (allQuotientReceivedSpineToStrictSpine q ρ u hrho).onF (h, s) :=
    congrArg (coveredSpineToStrictSpine q ρ u).onF he
  cases Subtype.ext hs
  have hv : (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV
      ((allQuotientReceivedSpineCover q ρ u hrho).base (g, t)) =
      (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV
        ((allQuotientReceivedSpineCover q ρ u hrho).base (h, t)) := by
    erw [← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF,
      ← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF, he]
  have hv' := congrArg (fun a => (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u) a).1) hv
  have hvold (a : (allQuotientReceivedSpineCover q ρ u hrho).V) :
      (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u)
        ((allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV a)).1 =
        (allQuotientReceivedSpineToQuotient q ρ u hrho).onV a :=
    uOrderHomInv_vertex _
  erw [hvold, hvold] at hv'
  have hg := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g 1 ((markedSpineCx q).base t)
  have hh := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho h 1 ((markedSpineCx q).base t)
  erw [mul_one] at hg hh
  exact Prod.ext (deckV_injective_in_group (X := orderCx (namedQuotientPos ρ q u))
    (namedQuotientBase ρ q u) _ (hg.symm.trans (hv'.trans hh))) rfl

theorem allQuotientReceivedSpineCoveredChain_nerve_image
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ) :
    cmap (Subtype.val : namedOldCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))
      (cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c)))) =
      universalNerveChain2 (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c) := by
  change cmap Subtype.val
    (cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
      (ordNerveChain2 (chain2 (strictOrderIncl _)
        (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c)))) =
    ordNerveChain2 (chain2 uOrderHomInv
      (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c))
  erw [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q (namedOldCoverProjection q ρ u)),
    ← ordNerveChain2_chain2 (Subtype.val : namedOldCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)) (fun _ _ h => h)]
  apply congrArg ordNerveChain2
  have hfirst : (orderCxMap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
      (oldCoveredSpineToOld_monotone q (namedOldCoverProjection q ρ u))).comp
      ((strictOrderIncl _).comp (allQuotientReceivedSpineToCoveredSpine q ρ u hrho)) =
      allQuotientReceivedSpineToOldCover q ρ u hrho := Hom.ext' rfl rfl rfl
  have hf2 := congrArg (fun k => chain2 k c) hfirst
  simp only [chain2_comp_apply] at hf2
  erw [hf2]
  have hrestrict := congrArg (fun k => chain2 k c)
    (orderCxRestrict_projects (allQuotientReceivedSpineOrderMap q ρ u hrho)
      (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho))
  simp only [allQuotientReceivedSpineOrderMap, chain2_comp_apply] at hrestrict
  exact hrestrict

theorem allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ)
    (hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = 0)
    (hbound : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2 (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) :
    c = 0 := by
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hy
  have hz : chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c = 0 := by
    refine genus_old_cover_spine_chain_zero_of_boundary q (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u) _ ?_ ⟨b, hb, ?_⟩
    · erw [bdry2_chain2, hc, map_zero]
    · apply cmap_val_injective _
        ⟨(allQuotientReceivedSpineOrderMap q ρ u hrho).onV (1, (markedSpineTree q).root),
          allQuotientReceivedSpineOrderMap_old q ρ u hrho _⟩
      erw [cmap_bdry, hby, hdy]
      exact (allQuotientReceivedSpineCoveredChain_nerve_image q ρ u hrho c).symm
  have hinj : Function.Injective (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho)) :=
    Finsupp.mapDomain_injective (allQuotientReceivedSpineToCoveredSpine_onF_injective q ρ u hrho)
  exact hinj (by simpa only [map_zero] using hz)
