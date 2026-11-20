module

public import RequestProject.GenusReceivedCoveredSpine

@[expose] public section

/-! The received spine on every sheet of the actual quotient group.
The change of coefficient group is a cellular map, and old-cover
three-boundaries are reflected before restricting coefficients again.
 -/

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  {G H : Type u} [Group G] [Group H]
  (φ : PresGroup (SpanningTree.treeRel T) →* G) (η : G →* H)

/-- Changing the sheet group commutes with every lifted attaching path. -/
theorem liftPath_map_group (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun eb => ((η eb.1.1, eb.1.2), eb.2)) =
      liftPath T (η.comp φ) p (η g) :=
  TreeVoltage.liftPath_map T (freeReceiver T φ) (freeReceiver T (η.comp φ)) η
    (fun g e => map_mul η g (germValue T φ e)) p g

/-- An actual cellular map, retaining the original cell in each dimension. -/
def changeGroup : Hom (cover T φ) (cover T (η.comp φ)) where
  onV x := (η x.1, x.2)
  onE x := (η x.1, x.2)
  onF x := (η x.1, x.2)
  src_onE _ := rfl
  tgt_onE x := by
    change (η x.1 * η (germValue T φ (x.2, true)), _) =
      (η (x.1 * germValue T φ (x.2, true)), _)
    erw [map_mul]
    rfl
  base_onF _ := rfl
  att_onF x := (liftPath_map_group T φ η (K.att x.2) x.1).symm

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

def allQuotientSpineReceiver : PresGroup (spinePresentation q) →*
    NamedQuotientGroup ρ q u :=
  (finiteSpineToQuotient ρ q u hrho).comp
    (receivedSpineWordReceiver ρ (fun _  => q) (fun _ => u) PUnit.unit)

abbrev allQuotientReceivedSpineCover : Complex2 :=
  ReceivedTree.cover (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def allQuotientReceivedSpineProjection :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (markedSpineCx q) :=
  ReceivedTree.projection (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def receivedSpineChangeToAllQuotient :
    Hom (singleReceivedSpineCover q ρ u) (allQuotientReceivedSpineCover q ρ u hrho) :=
  ReceivedTree.changeGroup (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _  => q) (fun _ => u) PUnit.unit)
    (finiteSpineToQuotient ρ q u hrho)

def allQuotientSpineOldRootReceiver :
    NamedQuotientGroup ρ q u →*
      Pi1 (namedQuotientCx ρ q u)
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root) :=
  pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))

theorem allQuotientSpineOldRootReceiver_compatible :
    (allQuotientSpineOldRootReceiver q ρ u).comp (allQuotientSpineReceiver q ρ u hrho) =
      (pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) := finiteSpineOldRootReceiver_compatible q ρ u hrho

def allQuotientReceivedSpineToQuotientOldRoot :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (uCover (namedQuotientCx ρ q u)
        ((markedSpineToNamedQuotient q ρ u).onV (markedSpineTree q).root)) :=
  ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (allQuotientSpineReceiver q ρ u hrho) (allQuotientSpineOldRootReceiver q ρ u)
    (allQuotientSpineOldRootReceiver_compatible q ρ u hrho)

def allQuotientReceivedSpineToQuotient :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (namedQuotientCover ρ q u) :=
  (shiftHom (spineQuotientCylinderPath_isPath q ρ u)).comp
    (allQuotientReceivedSpineToQuotientOldRoot q ρ u hrho)

theorem allQuotientReceivedSpineToQuotient_projects :
    (univProj (namedQuotientCx ρ q u) (namedQuotientBase ρ q u)).comp
      (allQuotientReceivedSpineToQuotient q ρ u hrho) =
      (markedSpineToNamedQuotient q ρ u).comp
        (allQuotientReceivedSpineProjection q ρ u hrho) := by
  apply Hom.ext_orderCx
  funext x
  change endV (shiftV (spineQuotientCylinderPath_isPath q ρ u)
    (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
      (allQuotientSpineOldRootReceiver q ρ u) x.1 x.2)) = _
  erw [endV_shiftV, ReceivedTree.receiverVertex_end]
  rfl

theorem allQuotientReceivedSpineToQuotient_changeGroup :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).comp
      (receivedSpineChangeToAllQuotient q ρ u hrho) =
      receivedSpineToQuotient q ρ u hrho := by
  tauto

theorem allQuotientReceivedSpineToQuotient_chain2_changeGroup
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x =>
        (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) =
      chain2 (receivedSpineToQuotient q ρ u hrho) c := by
  change chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
    (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) c) = _
  erw [← chain2_comp_apply, allQuotientReceivedSpineToQuotient_changeGroup]

theorem allQuotientReceivedSpineToQuotient_deckV
    (g h : NamedQuotientGroup ρ q u)
    (a : (markedSpineCx q).V) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onV (g * h, a) =
      deckV g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV (h, a)) := by
  have hs : ReceivedTree.receiverVertex (markedSpineTree q)
      (markedSpineToNamedQuotient q ρ u) (allQuotientSpineOldRootReceiver q ρ u) (g * h) a =
      deckV (allQuotientSpineOldRootReceiver q ρ u g)
        (ReceivedTree.receiverVertex (markedSpineTree q)
          (markedSpineToNamedQuotient q ρ u) (allQuotientSpineOldRootReceiver q ρ u) h a) := by
    simp only [ReceivedTree.receiverVertex, map_mul, deckV_mul]
  change (shiftHom (spineQuotientCylinderPath_isPath q ρ u)).onV
    (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
      (allQuotientSpineOldRootReceiver q ρ u) (g * h) a) = _
  erw [hs, shiftHom_deckV]
  change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
    (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u)) g)) _ = _
  erw [pi1Conj_cancel_reverse]
  rfl

theorem allQuotientReceivedSpineToQuotient_deckF
    (g h : NamedQuotientGroup ρ q u)
    (f : (markedSpineCx q).F) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onF (g * h, f) =
      deckF g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onF (h, f)) := by
  apply Subtype.ext
  exact Prod.ext (allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g h _) rfl

noncomputable def allQuotientReceivedSpineOrderMap :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (orderCx (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))) :=
  uOrderHomInv.comp (allQuotientReceivedSpineToQuotient q ρ u hrho)

theorem allQuotientReceivedSpineOrderMap_old (a : (allQuotientReceivedSpineCover q ρ u hrho).V) :
    InQOld (uOrderEnd ((allQuotientReceivedSpineOrderMap q ρ u hrho).onV a)) := by
  change InQOld (endV (uOrderHomInv.onV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a)))
  erw [uOrderHomInv_vertex]
  have h := congrArg
    (fun k  => k.onV a)
    (allQuotientReceivedSpineToQuotient_projects q ρ u hrho)
  change endV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a) =
    (markedSpineToNamedQuotient q ρ u).onV a.2 at h
  erw [h]
  trivial

noncomputable def allQuotientReceivedSpineToOldCover :
    Hom (allQuotientReceivedSpineCover q ρ u hrho) (orderCx (namedOldCover q ρ u)) :=
  orderCxRestrict (allQuotientReceivedSpineOrderMap q ρ u hrho)
    (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho)

noncomputable def allQuotientReceivedSpineToStrictSpine :
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
  apply Hom.comp_left_cancel_orderCx (j := j) (fun _ _ h => Sum.inl.inj h)
  calc
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        ((orderCxMap Subtype.val (fun _ _ h => h)).comp
          (allQuotientReceivedSpineToOldCover q ρ u hrho)) := by
      change (j.comp (orderCxMap (namedOldCoverProjection q ρ u)
        (namedOldCoverProjection_isPosetCover q ρ u).mono)).comp _ = _
      dsimp only [j, namedOldCoverProjection]
      erw [qOldCover_projection_square]
      rfl
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (allQuotientReceivedSpineOrderMap q ρ u hrho) := by
      tauto
    _ = (univProj (namedQuotientCx ρ q u) (namedQuotientBase ρ q u)).comp
        (allQuotientReceivedSpineToQuotient q ρ u hrho) := by
      change ((orderCxMap uOrderEnd uOrderEnd_monotone).comp uOrderHomInv).comp _ = _
      erw [uOrderHomInv_projection_square]
    _ = _ := allQuotientReceivedSpineToQuotient_projects q ρ u hrho

noncomputable def allQuotientReceivedSpineToPullback :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (strictOrderCx (PosetCoverPullback (namedOldCoverProjection q ρ u) (genusSpineCellToOld q))) :=
  strictOrderPullbackHom (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q) (allQuotientReceivedSpineToOldCover q ρ u hrho)
    (allQuotientReceivedSpineToStrictSpine q ρ u hrho) (allQuotientReceivedSpine_old_square q ρ u hrho)

noncomputable def allQuotientReceivedSpineToCoveredSpine :
    Hom (allQuotientReceivedSpineCover q ρ u hrho)
      (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u))) :=
  (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u))
    (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).strictMono).comp
      (allQuotientReceivedSpineToPullback q ρ u hrho)

theorem allQuotientReceivedSpineToCoveredSpine_first :
    (orderCxMap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
      (oldCoveredSpineToOld_monotone q (namedOldCoverProjection q ρ u))).comp
      ((strictOrderIncl _).comp (allQuotientReceivedSpineToCoveredSpine q ρ u hrho)) =
      allQuotientReceivedSpineToOldCover q ρ u hrho := by
  tauto

theorem allQuotientReceivedSpineToCoveredSpine_vertex_old (a : (allQuotientReceivedSpineCover q ρ u hrho).V) :
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u)
      ((allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV a)).1 =
      (allQuotientReceivedSpineToQuotient q ρ u hrho).onV a := uOrderHomInv_vertex _

/-- Faithfulness of the group receiver preserves the individual sheets over
every spine vertex, including vertices away from the chosen root. -/
theorem allQuotientReceivedSpineToQuotient_sheet_injective (a : (markedSpineCx q).V) :
    Function.Injective (fun g : NamedQuotientGroup ρ q u =>
      (allQuotientReceivedSpineToQuotient q ρ u hrho).onV (g, a)) := by
  intro g h hgh
  apply deckV_injective_in_group (X := namedQuotientCx ρ q u)
    (namedQuotientBase ρ q u)
    ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV (1, a))
  have hg := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g 1 a
  have hh := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho h 1 a
  erw [mul_one] at hg hh
  simp_all

/-- The actual map into the pullback spine is injective on faces: its
spine projection retains the original face, and its old-cover projection
retains the sheet through the proved faithful receiver. -/
theorem allQuotientReceivedSpineToCoveredSpine_onF_injective :
    Function.Injective (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onF := by
  rintro ⟨g, t⟩ ⟨h, s⟩ he
  have hs := congrArg (coveredSpineToStrictSpine q ρ u).onF he
  change (allQuotientReceivedSpineToStrictSpine q ρ u hrho).onF (g, t) =
    (allQuotientReceivedSpineToStrictSpine q ρ u hrho).onF (h, s) at hs
  have hts : t = s := Subtype.ext hs
  subst s
  have hv : (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV
      ((allQuotientReceivedSpineCover q ρ u hrho).base (g, t)) =
      (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV
        ((allQuotientReceivedSpineCover q ρ u hrho).base (h, t)) := by
    erw [← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF,
      ← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF, he]
  have hv' := congrArg (fun a =>
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u) a).1) hv
  erw [allQuotientReceivedSpineToCoveredSpine_vertex_old, allQuotientReceivedSpineToCoveredSpine_vertex_old] at hv'
  have hg  := allQuotientReceivedSpineToQuotient_sheet_injective q ρ u hrho
    ((markedSpineCx q).base t) hv'
  aesop

theorem allQuotientReceivedSpineToCoveredSpine_chain2_injective :
    Function.Injective (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho)) :=
  Finsupp.mapDomain_injective (allQuotientReceivedSpineToCoveredSpine_onF_injective q ρ u hrho)

/-- A received spine cycle which bounds in the actual old cover is zero
already in the original group-indexed face chain. No abstract identification
of covered chains or extra injectivity hypothesis is used. -/
theorem allQuotientReceivedSpine_cycle_zero_of_old_boundary
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ)
    (hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = 0)
    (hbound : ∃ y ∈ Inc (namedOldCover q ρ u), Nerve.bdry y =
      cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c)))) : c = 0 := by
  have hz : chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c = 0 := by
    apply genus_old_cover_spine_chain_zero_of_boundary q (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u) _ _ hbound
    exact chain2_cycle _ hc
  apply allQuotientReceivedSpineToCoveredSpine_chain2_injective q ρ u hrho
  assumption

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
  erw [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q
    (namedOldCoverProjection q ρ u))]
  erw [← ordNerveChain2_chain2
    Subtype.val
    (fun _ _ h => h)]
  apply congrArg ordNerveChain2
  have hfirst := congrArg (fun k => chain2 k c)
    (allQuotientReceivedSpineToCoveredSpine_first q ρ u hrho)
  simp only [chain2_comp_apply] at hfirst
  erw [hfirst]
  have hrestrict := congrArg (fun k => chain2 k c)
    (orderCxRestrict_projects (allQuotientReceivedSpineOrderMap q ρ u hrho)
      (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho))
  simp only [allQuotientReceivedSpineOrderMap, chain2_comp_apply] at hrestrict
  exact hrestrict

/-- This is the precise reflection needed after the old/star relative
filling: a three-boundary supported on actual old cells forces the original
received two-cycle, with its individual sheet coefficients, to vanish. -/
theorem allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary
    (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ)
    (hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = 0)
    (hbound : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2 (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) :
    c = 0 := by
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn
    (fun p  =>
      InQOld (uOrderEnd p)) hy
  apply allQuotientReceivedSpine_cycle_zero_of_old_boundary q ρ u hrho c hc
  refine ⟨b, hb, ?_⟩
  apply cmap_val_injective _
  erw [cmap_bdry, hby, hdy]
  exact (allQuotientReceivedSpineCoveredChain_nerve_image q ρ u hrho c).symm

end FiniteChains.Davis.Genus
