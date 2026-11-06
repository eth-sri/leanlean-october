import Mathlib.Tactic

import RequestProject.GenusReceivedCoveredSpine

/-! The received spine on every sheet of the actual quotient group.
The change of coefficient group is a cellular map, and old-cover
three-boundaries are reflected before restricting coefficients again.
 -/

noncomputable section


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
variable {K : Complex2.{u}} (T : SpanningTree K)
  {G H : Type u} [Group G] [Group H]
  (φ : PresGroup (SpanningTree.treeRel T) →* G) (η : G →* H)

/-- Changing the sheet group commutes with every lifted attaching path. -/
theorem liftPath_map_group (p : List (K.E × Bool)) (g : G) :
    (liftPath T φ p g).map (fun eb => ((η eb.1.1, eb.1.2), eb.2)) =
      liftPath T (η.comp φ) p (η g) := by
  induction p generalizing g <;> aesop (add simp [liftGerm])

/-- An actual cellular map, retaining the original cell in each dimension. -/
def changeGroup : Hom (cover T φ) (cover T (η.comp φ)) where
  onV x := (η x.1, x.2)
  onE x := (η x.1, x.2)
  onF x := (η x.1, x.2)
  src_onE _ := rfl
  tgt_onE x := by
    
    rw (config := { transparency := .default }) [map_mul]
    rfl
  base_onF _ := rfl
  att_onF x := (liftPath_map_group T φ η (K.att x.2) x.1).symm

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def allQuotientSpineReceiver  :=
  (finiteSpineToQuotient ρ q u hrho).comp
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)

abbrev allQuotientReceivedSpineCover  :=
  ReceivedTree.cover (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def allQuotientReceivedSpineProjection  :=
  ReceivedTree.projection (markedSpineTree q) (allQuotientSpineReceiver q ρ u hrho)

def receivedSpineChangeToAllQuotient  :=
  ReceivedTree.changeGroup (markedSpineTree q)
    (receivedSpineWordReceiver ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit)
    (finiteSpineToQuotient ρ q u hrho)

def allQuotientSpineOldRootReceiver  :=
  pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))

abbrev allQuotientSpineOldRootReceiver_compatible :=
  FiniteChains.Davis.Genus.finiteSpineOldRootReceiver_compatible

def allQuotientReceivedSpineToQuotientOldRoot  :=
  ReceivedTree.comparison (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
    (allQuotientSpineReceiver q ρ u hrho) (allQuotientSpineOldRootReceiver q ρ u)
    (allQuotientSpineOldRootReceiver_compatible q ρ u hrho)

def allQuotientReceivedSpineToQuotient  :=
  (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).comp
    (allQuotientReceivedSpineToQuotientOldRoot q ρ u hrho)

theorem allQuotientReceivedSpineToQuotient_projects :
    (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
      (allQuotientReceivedSpineToQuotient q ρ u hrho) =
      (markedSpineToNamedQuotient q ρ u).comp
        (allQuotientReceivedSpineProjection q ρ u hrho) := by
  apply Hom.ext'
  · funext x
    change endV (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (allQuotientSpineOldRootReceiver q ρ u) x.1 x.2)) = _
    rw  [endV_pathTransportV, ReceivedTree.receiverVertex_end]
    rfl
  · rfl
  · rfl

theorem allQuotientReceivedSpineToQuotient_changeGroup :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).comp
      (receivedSpineChangeToAllQuotient q ρ u hrho) =
      receivedSpineToQuotient q ρ u hrho := by
  apply Hom.ext' <;> rfl

theorem allQuotientReceivedSpineToQuotient_chain2_changeGroup
    (c : (singleReceivedSpineCover q ρ u).F →₀ ℤ) :
    chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x =>
        (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) =
      chain2 (receivedSpineToQuotient q ρ u hrho) c := by
  change chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho)
    (chain2 (receivedSpineChangeToAllQuotient q ρ u hrho) c) = _
  rw (config := { transparency := .default }) [← chain2_comp_apply, allQuotientReceivedSpineToQuotient_changeGroup]

variable (g h : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
include g h in
theorem allQuotientReceivedSpineToQuotient_deckV
    
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
  rw  [hs, uCoverPathTransport_deckV]
  
  rw (config := { transparency := .default }) [pi1Conj_cancel_reverse]
  rfl

include g h in
theorem allQuotientReceivedSpineToQuotient_deckF
    
    (f : (markedSpineCx q).F) :
    (allQuotientReceivedSpineToQuotient q ρ u hrho).onF (g * h, f) =
      deckF g ((allQuotientReceivedSpineToQuotient q ρ u hrho).onF (h, f)) := by
  apply Subtype.ext
  exact Prod.ext (allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g h _) rfl

def allQuotientReceivedSpineOrderMap  :=
  uOrderHomInv.comp (allQuotientReceivedSpineToQuotient q ρ u hrho)

variable (a : (allQuotientReceivedSpineCover q ρ u hrho).V)
theorem allQuotientReceivedSpineOrderMap_old  :
    InQOld (uOrderEnd ((allQuotientReceivedSpineOrderMap q ρ u hrho).onV a)) := by
  change InQOld (endV (uOrderHomInv.onV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a)))
  rw  [uOrderHomInv_vertex]
  have h := congrArg
    (fun k : Hom (allQuotientReceivedSpineCover q ρ u hrho) (orderCx (namedQuotientPos ρ q u)) => k.onV a)
    (allQuotientReceivedSpineToQuotient_projects q ρ u hrho)
  change endV ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV a) =
    (markedSpineToNamedQuotient q ρ u).onV a.2 at h
  rw  [h]
  trivial

def allQuotientReceivedSpineToOldCover  :=
  orderCxRestrict (allQuotientReceivedSpineOrderMap q ρ u hrho)
    (fun p => InQOld (uOrderEnd p)) (allQuotientReceivedSpineOrderMap_old q ρ u hrho)

def allQuotientReceivedSpineToStrictSpine  :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (allQuotientReceivedSpineProjection q ρ u hrho)

theorem allQuotientReceivedSpine_old_square :
    (orderCxMap (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u).mono).comp
      (allQuotientReceivedSpineToOldCover q ρ u hrho) =
      (orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
        ((strictOrderIncl (GenusSpineCell q)).comp (allQuotientReceivedSpineToStrictSpine q ρ u hrho)) := by
  let j := orderCxMap (qOldIncl (att := namedAtt ρ q u)) qOldIncl_monotone
  have hv : Function.Injective j.onV := fun _ _ h => Sum.inl.inj h
  have he : Function.Injective j.onE := by
    intro e f h
    apply Subtype.ext
    exact Prod.ext (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.1) h))
      (Sum.inl.inj (congrArg (fun t : OrdEdge (namedQuotientPos ρ q u) => t.1.2) h))
  have ht : Function.Injective j.onF := by
    intro e f h
    apply Subtype.ext
    exact Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.1) h))
      (Prod.ext (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.1) h))
        (Sum.inl.inj (congrArg (fun t : OrdTri (namedQuotientPos ρ q u) => t.1.2.2) h)))
  apply Hom.comp_left_cancel_of_injective j hv he ht
  calc
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        ((orderCxMap Subtype.val (fun _ _ h => h)).comp
          (allQuotientReceivedSpineToOldCover q ρ u hrho)) := by
      change (j.comp (orderCxMap (namedOldCoverProjection q ρ u)
        (namedOldCoverProjection_isPosetCover q ρ u).mono)).comp _ = _
      dsimp only [j, namedOldCoverProjection]
      rw  [qOldCover_projection_square]
      rfl
    _ = (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (allQuotientReceivedSpineOrderMap q ρ u hrho) := by
      rfl
    _ = (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
        (allQuotientReceivedSpineToQuotient q ρ u hrho) := by
      change ((orderCxMap uOrderEnd uOrderEnd_monotone).comp uOrderHomInv).comp _ = _
      rw  [uOrderHomInv_projection_square]
    _ = _ := allQuotientReceivedSpineToQuotient_projects q ρ u hrho

def allQuotientReceivedSpineToPullback  :=
  strictOrderPullbackHom (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q) (allQuotientReceivedSpineToOldCover q ρ u hrho)
    (allQuotientReceivedSpineToStrictSpine q ρ u hrho) (allQuotientReceivedSpine_old_square q ρ u hrho)

def allQuotientReceivedSpineToCoveredSpine  :=
  (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u))
    (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).strictMono).comp
      (allQuotientReceivedSpineToPullback q ρ u hrho)



theorem allQuotientReceivedSpineToCoveredSpine_vertex_old  :
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u)
      ((allQuotientReceivedSpineToCoveredSpine q ρ u hrho).onV a)).1 =
      (allQuotientReceivedSpineToQuotient q ρ u hrho).onV a := uOrderHomInv_vertex _

/-- Faithfulness of the group receiver preserves the individual sheets over
every spine vertex, including vertices away from the chosen root. -/
theorem allQuotientReceivedSpineToQuotient_sheet_injective (a : (markedSpineCx q).V) :
    Function.Injective (fun g : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) =>
      (allQuotientReceivedSpineToQuotient q ρ u hrho).onV (g, a)) := by
  intro g h hgh
  apply deckV_injective_in_group (X := orderCx (namedQuotientPos ρ q u))
    (namedQuotientBase ρ q u)
    ((allQuotientReceivedSpineToQuotient q ρ u hrho).onV (1, a))
  have hg := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho g 1 a
  have hh := allQuotientReceivedSpineToQuotient_deckV q ρ u hrho h 1 a
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
    rw  [← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF,
      ← (allQuotientReceivedSpineToCoveredSpine q ρ u hrho).base_onF, he]
  have hv' := congrArg (fun a =>
    (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u) a).1) hv
  rw  [allQuotientReceivedSpineToCoveredSpine_vertex_old, allQuotientReceivedSpineToCoveredSpine_vertex_old] at hv'
  have hg  := allQuotientReceivedSpineToQuotient_sheet_injective q ρ u hrho
    ((markedSpineCx q).base t) hv'
  exact Prod.ext hg rfl

theorem allQuotientReceivedSpineToCoveredSpine_chain2_injective :
    Function.Injective (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho)) :=
  Finsupp.mapDomain_injective (allQuotientReceivedSpineToCoveredSpine_onF_injective q ρ u hrho)

variable (c : (allQuotientReceivedSpineCover q ρ u hrho).F →₀ ℤ)
variable (hc : Comb.bdry2 (allQuotientReceivedSpineCover q ρ u hrho) c = 0)
include hc in
/-- A received spine cycle which bounds in the actual old cover is zero
already in the original group-indexed face chain. No abstract identification
of covered chains or extra injectivity hypothesis is used. -/
theorem allQuotientReceivedSpine_cycle_zero_of_old_boundary
    
    
    (hbound : ∃ y ∈ Inc (namedOldCover q ρ u), Nerve.bdry y =
      cmap (oldCoveredSpineToOld q (namedOldCoverProjection q ρ u))
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c)))) : c = 0 := by
  have hz : chain2 (allQuotientReceivedSpineToCoveredSpine q ρ u hrho) c = 0 := by
    apply genus_old_cover_spine_chain_zero_of_boundary q (namedOldCoverProjection q ρ u)
      (namedOldCoverProjection_isPosetCover q ρ u) _ _ hbound
    rw  [bdry2_chain2, hc, map_zero]
  apply allQuotientReceivedSpineToCoveredSpine_chain2_injective q ρ u hrho
  simpa only [map_zero] using hz

theorem allQuotientReceivedSpineCoveredChain_nerve_image
     :
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
  rw  [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q
    (namedOldCoverProjection q ρ u))]
  rw  [← ordNerveChain2_chain2
    (Subtype.val : namedOldCover q ρ u →
      UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u))
    (fun _ _ h => h)]
  aesop (add simp [ordNerveChain2])

include hc in
/-- This is the precise reflection needed after the old/star relative
filling: a three-boundary supported on actual old cells forces the original
received two-cycle, with its individual sheet coefficients, to vanish. -/
theorem allQuotientReceivedSpine_cycle_zero_of_quotient_old_boundary
    
    
    (hbound : ∃ y ∈ IncOn (fun p : UOrder (namedQuotientPos ρ q u)
        (namedQuotientBase ρ q u) => InQOld (uOrderEnd p)),
      Nerve.bdry y = universalNerveChain2 (chain2 (allQuotientReceivedSpineToQuotient q ρ u hrho) c)) :
    c = 0 := by
  obtain ⟨y, hy, hdy⟩ := hbound
  obtain ⟨b, hb, hby⟩ := exists_preimage_of_mem_incOn
    (fun p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u) =>
      InQOld (uOrderEnd p)) hy
  apply allQuotientReceivedSpine_cycle_zero_of_old_boundary q ρ u hrho c hc
  refine ⟨b, hb, ?_⟩
  have hne : ∃ p : UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u),
      InQOld (uOrderEnd p) :=
    ⟨(allQuotientReceivedSpineOrderMap q ρ u hrho).onV (1, (markedSpineTree q).root),
      allQuotientReceivedSpineOrderMap_old q ρ u hrho _⟩
  apply cmap_val_injective _ hne
  rw  [cmap_bdry, hby, hdy]
  exact (allQuotientReceivedSpineCoveredChain_nerve_image q ρ u hrho c).symm

end FiniteChains.Davis.Genus
