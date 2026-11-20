module

public import RequestProject.GenusQuotientRelativeSupport

@[expose] public section

/-! Lift the actual surface markings to the genuine attaching cover and apply
the relative old-chain filling theorem. Pending final Lean verification.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem universalNerveChain1_uOrderHom (c : OrdEdge (UOrder P a) →₀ ℤ) :
    universalNerveChain1 (chain1 uOrderHom c) = ordNerveChain1 c := by
  change ordNerveChain1
    (Finsupp.mapDomain uOrderHomInv.onE _) = _
  erw [← Finsupp.mapDomain_comp]
  have h : (uOrderHomInv (a := a)).onE ∘ uOrderHom.onE = id := by
    funext e
    apply homInv_onE_comp
  rw [h, Finsupp.mapDomain_id]

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- The attaching-cover projection reconstructs its actual endpoint in the quotient. -/
theorem qAttachingCoverEnd_spec (a : Qpos A X att) (p : QLiftedAttaching a) :
    qOldIncl (att := att) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := congrArg Subtype.val
    ((qPositiveOldOrderIso (att := att)).symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedAttachingCover := QLiftedAttaching (namedQuotientBase ρ q u)

theorem namedAttachingEnd_isPosetCover :
    IsPosetCover (qAttachingCoverEnd (namedQuotientBase ρ q u)) :=
  qAttachingCoverEnd_isPosetCover _
    (namedBasePos_isConnected ρ q u)

def namedAttachingProjection :=
  orderCxMap _
    (namedAttachingEnd_isPosetCover q ρ u).mono

theorem namedAttachingProjection_isCovering :
    IsCovering (namedAttachingProjection q ρ u) :=
  isCovering_orderCxMap (namedAttachingEnd_isPosetCover q ρ u)

def namedAttachingIntoUniversal :
    Hom (orderCx (namedAttachingCover q ρ u))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  uOrderHom.comp (orderCxMap Subtype.val (fun _ _ h => h))

def namedSurfaceIntoQuotient :=
  (oldIntoNamedQuotient q ρ u).comp (surfCx (cmpRel (GenusVertex q)))

theorem namedAttachingIntoUniversal_projects :
    (univProj _ _).comp
      (namedAttachingIntoUniversal q ρ u) =
      (namedSurfaceIntoQuotient q ρ u).comp (namedAttachingProjection q ρ u) := by
  apply Hom.ext'
  · funext p
    exact (qAttachingCoverEnd_spec _ p).symm
  · funext e
    apply Subtype.ext
    exact Prod.ext
      (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) e.1.1).symm
      (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) e.1.2).symm
  · funext t
    apply Subtype.ext
    exact Prod.ext
      (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.1).symm
      (Prod.ext
        (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.2.1).symm
        (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.2.2).symm)

variable (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u)))

def namedAttachingReference :
    namedAttachingCover q ρ u :=
  ⟨deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u), by
    change InQOld (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u))) ∧
      InQBaseStar (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u)))
    simp only [endV_deckV, quotientCylinderVertex_end]
    solve_by_elim⟩

theorem namedAttachingReference_projects :
    (namedAttachingProjection q ρ u).onV (namedAttachingReference q ρ u hrho g) =
      gBase q := by
  apply (qPositiveOldOrderIso (att := namedAtt ρ q u)).symm.injective
  apply Subtype.ext
  change qOldIncl (att := namedAtt ρ q u)
    (posQCube (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingReference q ρ u hrho g))) =
    qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q))
  erw [qAttachingCoverEnd_spec]
  solve_by_elim [endV_deckV, quotientCylinderVertex_end]

variable (i : Fin q × Bool)

theorem exists_namedAttachingMarkingPath :
    ∃ p : List _,
      ∃ b : namedAttachingCover q ρ u,
        IsPath (orderCx (namedAttachingCover q ρ u)).src
          (orderCx (namedAttachingCover q ρ u)).tgt p
          (namedAttachingReference q ρ u hrho g) b ∧
        mapPath (namedAttachingProjection q ρ u) p = gSig q (i.1.val, i.2) := by
  apply exists_liftPathAt (namedAttachingProjection_isCovering q ρ u).lifts
    _ _ (gBase q)
  simp_all [namedAttachingReference_projects, isPath_gSig]

def namedAttachingMarkingPath :=
  Classical.choose (exists_namedAttachingMarkingPath q ρ u hrho g i)

def namedAttachingMarkingEnd :=
  Classical.choose (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

theorem namedAttachingMarkingPath_spec :
    IsPath (orderCx (namedAttachingCover q ρ u)).src
      (orderCx (namedAttachingCover q ρ u)).tgt (namedAttachingMarkingPath q ρ u hrho g i)
      (namedAttachingReference q ρ u hrho g) (namedAttachingMarkingEnd q ρ u hrho g i) ∧
    mapPath (namedAttachingProjection q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      gSig q (i.1.val, i.2) :=
  Classical.choose_spec (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

/-- The image of the path lifted in the attaching cover is the actual universal-cover lift. -/
theorem namedAttachingMarkingPath_image :
    mapPath (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u)) := by
  have hp := isPath_mapPath (namedAttachingIntoUniversal q ρ u)
    (namedAttachingMarkingPath_spec q ρ u hrho g i).1
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath
      (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u))
      (mapPath (namedAttachingIntoUniversal q ρ u)
        (namedAttachingMarkingPath q ρ u hrho g i)) =
      mapPath (namedSurfaceIntoQuotient q ρ u) (gSig q (i.1.val, i.2)) := by
    calc
      _ = mapPath
          _
          _ := mapPath_comp _ _ _
      _ = mapPath _
          _ :=
        congrArg (fun f => mapPath f _)
          (namedAttachingIntoUniversal_projects q ρ u)
      _ = mapPath _
          _ := (mapPath_comp _ _ _).symm
      _ = _ := congrArg _
        (namedAttachingMarkingPath_spec q ρ u hrho g i).2
  erw [hproj, (mapPath_comp _ _ (gSig q (i.1.val, i.2))).symm] at he <;> assumption

def namedAttachingMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun x => pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2))

theorem namedAttachingMarkingChains_image
    (c : (PresGroup _ × (Fin q × Bool)) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingChains q ρ u hrho c) =
      quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      erw [namedAttachingMarkingChains, quotientSurfaceMarkingChains,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg _
      change Finsupp.mapDomain _
        (pathChain _) = _
      erw [← pathChain_map]
      solve_by_elim [namedAttachingMarkingPath_image]

def namedAttachingNerveBoundary :=
  ordNerveChain1.comp (namedAttachingMarkingChains q ρ u hrho)

variable (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)

theorem namedAttachingNerveBoundary_mem_inc :
    namedAttachingNerveBoundary q ρ u hrho c ∈ Inc _ :=
  ordNerveChain1_mem_inc _

theorem namedAttachingNerveBoundary_image :
    universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho c) =
      cmap Subtype.val (namedAttachingNerveBoundary q ρ u hrho c) := by
  erw [← namedAttachingMarkingChains_image q ρ u hrho c]
  change universalNerveChain1 (chain1
      (uOrderHom.comp (orderCxMap Subtype.val (fun _ _ h => h)))
      _) =
    cmap Subtype.val (ordNerveChain1 (namedAttachingMarkingChains q ρ u hrho c))
  simp [chain1_comp_apply, universalNerveChain1_uOrderHom, ordNerveChain1_chain1]

/-- The actual B2 coordinate equation supplies an actual attaching-cover two-chain
with the original marked boundary, and an old three-chain correcting its image. -/
theorem quotientCorrectedRelative_attaching_filling
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      _)
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ _)
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    ∃ c : Ch _,
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧
      Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧
        quotientCorrectedRelativeNerveChain q ρ u hrho β =
          cmap Subtype.val c + Nerve.bdry y := by
  apply qUniversal_old_cellular_relative_chain_from_attaching
    _ (namedBasePos_isConnected ρ q u) (gBase q)
    _
    (quotientCorrectedRelativeChain_face_support q ρ u hrho β)
    _
    (namedAttachingNerveBoundary_mem_inc q ρ u hrho _)
  simp_all [quotientCorrectedRelativeChain_boundary, namedAttachingNerveBoundary_image]

end FiniteChains.Davis.Genus
