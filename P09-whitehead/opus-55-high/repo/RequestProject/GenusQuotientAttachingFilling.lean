import RequestProject.GenusQuotientRelativeSupport
import RequestProject.Tac
noncomputable section


/-! Lift the actual surface markings to the genuine attaching cover and apply
the relative old-chain filling theorem. Pending final Lean verification.
-/

bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem universalNerveChain1_uOrderHom (c : OrdEdge (UOrder P a) →₀ ℤ) :
    universalNerveChain1 (chain1 uOrderHom c) = ordNerveChain1 c := by
  change ordNerveChain1
    (Finsupp.mapDomain uOrderHomInv.onE (Finsupp.mapDomain uOrderHom.onE c)) = _
  rwd [← Finsupp.mapDomain_comp]
  have h : (uOrderHomInv (P := P) (a := a)).onE ∘ uOrderHom.onE = id := by
    funext e
    exact homInv_onE_comp uOrderHom Function.bijective_id
      _
      _ e
  rwd [h, Finsupp.mapDomain_id]

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- The attaching-cover projection reconstructs its actual endpoint in the quotient. -/
theorem qAttachingCoverEnd_spec a p :
    qOldIncl (att := att) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := congrArg Subtype.val
    ((qPositiveOldOrderIso (att := att)).symm_apply_apply _)

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

def namedAttachingProjection :
    Hom (orderCx (namedAttachingCover q ρ u))
      (orderCx (NeSpx (cmpRel (GenusVertex q)))) :=
  orderCxMap _
    (namedAttachingEnd_isPosetCover q ρ u).mono

theorem namedAttachingProjection_isCovering :
    IsCovering (namedAttachingProjection q ρ u) :=
  isCovering_orderCxMap (namedAttachingEnd_isPosetCover q ρ u)

def namedAttachingIntoUniversal :
    Hom (orderCx (namedAttachingCover q ρ u))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  uOrderHom.comp (orderCxMap Subtype.val (by tauto))

def namedSurfaceIntoQuotient :=
  (oldIntoNamedQuotient q ρ u).comp (surfCx _)

theorem namedAttachingIntoUniversal_projects :
    (univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
      (namedAttachingIntoUniversal q ρ u) =
      (namedSurfaceIntoQuotient q ρ u).comp (namedAttachingProjection q ρ u) := by
  apply Hom.ext'
  · funext p
    exact (qAttachingCoverEnd_spec _ p).symm
  · funext e
    apply Subtype.ext
    exact Prod.ext
      (qAttachingCoverEnd_spec _ e.1.1).symm
      (qAttachingCoverEnd_spec _ e.1.2).symm
  · funext t
    apply Subtype.ext
    exact Prod.ext
      (qAttachingCoverEnd_spec _ t.1.1).symm
      (Prod.ext
        (qAttachingCoverEnd_spec _ t.1.2.1).symm
        (qAttachingCoverEnd_spec _ t.1.2.2).symm)

def namedAttachingReference
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    namedAttachingCover q ρ u :=
  ⟨deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u), by
    change InQOld (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u))) ∧
      InQBaseStar (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u)))
    simp [endV_deckV, quotientCylinderVertex_end]
    tauto⟩

theorem namedAttachingReference_projects
    g :
    (namedAttachingProjection q ρ u).onV (namedAttachingReference q ρ u hrho g) =
      gBase q := by
  apply (qPositiveOldOrderIso (att := namedAtt ρ q u)).symm.injective
  apply Subtype.ext
  change qOldIncl (att := namedAtt ρ q u)
    (posQCube (qAttachingCoverEnd _
      (namedAttachingReference q ρ u hrho g))) =
    qOldIncl (att := namedAtt ρ q u) (posQCube (gBase q))
  rwd [qAttachingCoverEnd_spec]
  change endV (deckV _ (quotientCylinderVertex q ρ u)) = _
  aesop

theorem exists_namedAttachingMarkingPath
    g (i : Fin q × Bool) :
    ∃ p,
      ∃ b : namedAttachingCover q ρ u,
        IsPath (orderCx (namedAttachingCover q ρ u)).src
          (orderCx (namedAttachingCover q ρ u)).tgt p
          (namedAttachingReference q ρ u hrho g) b ∧
        mapPath (namedAttachingProjection q ρ u) p = gSig q (i.1.val, i.2) := by
  apply exists_liftPathAt (namedAttachingProjection_isCovering q ρ u)
    _ _ _
  rwd [namedAttachingReference_projects]
  exact isPath_gSig q _

def namedAttachingMarkingPath
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :=
  Classical.choose (exists_namedAttachingMarkingPath q ρ u hrho g i)

def namedAttachingMarkingEnd
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :=
  Classical.choose (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

theorem namedAttachingMarkingPath_spec
    g i :
    IsPath (orderCx (namedAttachingCover q ρ u)).src
      (orderCx (namedAttachingCover q ρ u)).tgt (namedAttachingMarkingPath q ρ u hrho g i)
      (namedAttachingReference q ρ u hrho g) (namedAttachingMarkingEnd q ρ u hrho g i) ∧
    mapPath (namedAttachingProjection q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      gSig q (i.1.val, i.2) :=
  Classical.choose_spec (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

/-- The image of the path lifted in the attaching cover is the actual universal-cover lift. -/
theorem namedAttachingMarkingPath_image
    g i :
    mapPath (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      uLiftPath (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i))
        (deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u)) := by
  have hp := isPath_mapPath (namedAttachingIntoUniversal q ρ u)
    (namedAttachingMarkingPath_spec q ρ u hrho g i).1
  have he := eq_uLiftPath_of_isPath _ _ _ hp
  have hproj : mapPath
      (univProj _ _)
      (mapPath (namedAttachingIntoUniversal q ρ u)
        (namedAttachingMarkingPath q ρ u hrho g i)) =
      mapPath (namedSurfaceIntoQuotient q ρ u) (gSig q (i.1.val, i.2)) := by
    calc
      _ = mapPath
          ((univProj _ _).comp
            (namedAttachingIntoUniversal q ρ u))
          (namedAttachingMarkingPath q ρ u hrho g i) := mapPath_comp _ _ _
      _ = mapPath ((namedSurfaceIntoQuotient q ρ u).comp (namedAttachingProjection q ρ u))
          (namedAttachingMarkingPath q ρ u hrho g i) :=
        congrArg (mapPath · (namedAttachingMarkingPath q ρ u hrho g i))
          (namedAttachingIntoUniversal_projects q ρ u)
      _ = mapPath (namedSurfaceIntoQuotient q ρ u)
          (mapPath (namedAttachingProjection q ρ u)
            (namedAttachingMarkingPath q ρ u hrho g i)) := (mapPath_comp _ _ _).symm
      _ = _ := congrArg _
        (namedAttachingMarkingPath_spec q ρ u hrho g i).2
  have hsurf : mapPath (namedSurfaceIntoQuotient q ρ u) (gSig q (i.1.val, i.2)) =
      mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q i) :=
    by rfl
  rwd [hproj, hsurf] at he
  exact he

def namedAttachingMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun x => pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2))

theorem namedAttachingMarkingChains_image
    c :
    chain1 (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingChains q ρ u hrho c) =
      quotientSurfaceMarkingChains q ρ u hrho c := by
  lin_ind c x n =>
      rwd [namedAttachingMarkingChains, quotientSurfaceMarkingChains,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg _
      change Finsupp.mapDomain (namedAttachingIntoUniversal q ρ u).onE
        (pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2)) = _
      rwd [← pathChain_map]
      exact congrArg pathChain (namedAttachingMarkingPath_image q ρ u hrho x.1 x.2)

def namedAttachingNerveBoundary :=
  ordNerveChain1.comp (namedAttachingMarkingChains q ρ u hrho)

theorem namedAttachingNerveBoundary_mem_inc
    c :
    namedAttachingNerveBoundary q ρ u hrho c ∈ Inc (namedAttachingCover q ρ u) :=
  ordNerveChain1_mem_inc _

theorem namedAttachingNerveBoundary_image
    c :
    universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho c) =
      cmap Subtype.val (namedAttachingNerveBoundary q ρ u hrho c) := by
  rwd [← namedAttachingMarkingChains_image q ρ u hrho c]
  change universalNerveChain1 (chain1
      (uOrderHom.comp (orderCxMap Subtype.val (by tauto)))
      (namedAttachingMarkingChains q ρ u hrho c)) =
    cmap Subtype.val (ordNerveChain1 (namedAttachingMarkingChains q ρ u hrho c))
  simp [chain1_comp_apply, universalNerveChain1_uOrderHom, ordNerveChain1_chain1]

/-- The actual B2 coordinate equation supplies an actual attaching-cover two-chain
with the original marked boundary, and an old three-chain correcting its image. -/
theorem quotientCorrectedRelative_attaching_filling
    β
    (hβ : ∀ z,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    ∃ c,
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
  simp [quotientCorrectedRelativeChain_boundary q ρ u hrho β hβ, namedAttachingNerveBoundary_image]
