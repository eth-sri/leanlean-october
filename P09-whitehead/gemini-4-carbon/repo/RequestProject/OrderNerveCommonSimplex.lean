module

public import RequestProject.GenusQuotientRelativeSupport
public import RequestProject.CylinderPi1Surjective
public import RequestProject.OrderNerveOneDecoding
public import Mathlib.Topology.Homotopy.Contractible
public import RequestProject.CombPi1
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import RequestProject.GenusCollapseIteration
public import Mathlib.Topology.Homotopy.Equiv
public import RequestProject.GenusLoops
public import Mathlib.Topology.Path
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Homeomorph.Lemmas
public import RequestProject.PresPosetReading
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
noncomputable section
section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem universalNerveChain1_uOrderHom (c : OrdEdge (UOrder P a) →₀ ℤ) :
    universalNerveChain1 (chain1 uOrderHom c) = ordNerveChain1 c := by
  change ordNerveChain1
    (Finsupp.mapDomain uOrderHomInv.onE (Finsupp.mapDomain uOrderHom.onE c)) = _
  erw [← Finsupp.mapDomain_comp]
  have h : (uOrderHomInv (P := P) (a := a)).onE ∘ uOrderHom.onE = id := by
    funext e
    exact homInv_onE_comp uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ e
  erw [h, Finsupp.mapDomain_id]

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- The attaching-cover projection reconstructs its actual endpoint in the quotient. -/
theorem qAttachingCoverEnd_spec (a : Qpos A X att) (p : QLiftedAttaching a) :
    qOldIncl (att := att) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := by
  exact congrArg Subtype.val
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
  qAttachingCoverEnd_isPosetCover (namedAtt ρ q u (gBase q))
    (namedBasePos_isConnected ρ q u)

def namedAttachingProjection :
    Hom (orderCx (namedAttachingCover q ρ u))
      (orderCx (NeSpx (cmpRel (GenusVertex q)))) :=
  orderCxMap (qAttachingCoverEnd (namedQuotientBase ρ q u))
    (namedAttachingEnd_isPosetCover q ρ u).mono


def namedAttachingIntoUniversal :
    Hom (orderCx (namedAttachingCover q ρ u))
      (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)) :=
  uOrderHom.comp (orderCxMap Subtype.val (fun _ _ h => h))

def namedSurfaceIntoQuotient :
    Hom (orderCx (NeSpx (cmpRel (GenusVertex q)))) (orderCx (namedQuotientPos ρ q u)) :=
  (oldIntoNamedQuotient q ρ u).comp (surfCx (cmpRel (GenusVertex q)))


def namedAttachingReference
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :
    namedAttachingCover q ρ u :=
  ⟨deckV (finiteSpineToQuotient ρ q u hrho g) (quotientCylinderVertex q ρ u), by
    change InQOld (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u))) ∧
      InQBaseStar (endV (deckV (finiteSpineToQuotient ρ q u hrho g)
        (quotientCylinderVertex q ρ u)))
    simp only [endV_deckV, quotientCylinderVertex_end]
    exact ⟨trivial, rfl⟩⟩


theorem exists_namedAttachingMarkingPath
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    ∃ p : List ((orderCx (namedAttachingCover q ρ u)).E × Bool),
      ∃ b : namedAttachingCover q ρ u,
        IsPath (orderCx (namedAttachingCover q ρ u)).src
          (orderCx (namedAttachingCover q ρ u)).tgt p
          (namedAttachingReference q ρ u hrho g) b ∧
        mapPath (namedAttachingProjection q ρ u) p = gSig q (i.1.val, i.2) := by
  apply exists_liftPathAt (isCovering_orderCxMap (namedAttachingEnd_isPosetCover q ρ u))
    (gSig q (i.1.val, i.2)) (namedAttachingReference q ρ u hrho g) (gBase q)
  erw [(show (namedAttachingProjection q ρ u).onV (namedAttachingReference q ρ u hrho g) =
      gBase q by
    apply (qPositiveOldOrderIso (att := namedAtt ρ q u)).symm.injective
    ext
    change qOldIncl
      (posQCube (qAttachingCoverEnd (namedQuotientBase ρ q u)
        (namedAttachingReference q ρ u hrho g))) =
      qOldIncl (posQCube (gBase q))
    erw [qAttachingCoverEnd_spec]
    change endV (deckV _ (quotientCylinderVertex q ρ u)) = _
    erw [endV_deckV, quotientCylinderVertex_end]
    rfl)]
  exact isPath_gSig q (i.1.val, i.2)

def namedAttachingMarkingPath
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    List ((orderCx (namedAttachingCover q ρ u)).E × Bool) :=
  Classical.choose (exists_namedAttachingMarkingPath q ρ u hrho g i)

def namedAttachingMarkingEnd
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    namedAttachingCover q ρ u :=
  Classical.choose (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

theorem namedAttachingMarkingPath_spec
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
    IsPath (orderCx (namedAttachingCover q ρ u)).src
      (orderCx (namedAttachingCover q ρ u)).tgt (namedAttachingMarkingPath q ρ u hrho g i)
      (namedAttachingReference q ρ u hrho g) (namedAttachingMarkingEnd q ρ u hrho g i) ∧
    mapPath (namedAttachingProjection q ρ u) (namedAttachingMarkingPath q ρ u hrho g i) =
      gSig q (i.1.val, i.2) :=
  Classical.choose_spec (Classical.choose_spec (exists_namedAttachingMarkingPath q ρ u hrho g i))

/-- The image of the path lifted in the attaching cover is the actual universal-cover lift. -/
theorem namedAttachingMarkingPath_image
    (g : PresGroup (substPresF ρ (finiteSpineWordBlock q u))) (i : Fin q × Bool) :
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
          ((univProj (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).comp
            (namedAttachingIntoUniversal q ρ u))
          (namedAttachingMarkingPath q ρ u hrho g i) := mapPath_comp _ _ _
      _ = mapPath ((namedSurfaceIntoQuotient q ρ u).comp (namedAttachingProjection q ρ u))
          (namedAttachingMarkingPath q ρ u hrho g i) :=
        congrArg (fun f => mapPath f (namedAttachingMarkingPath q ρ u hrho g i))
          (by
            apply Hom.ext'
            · funext p
              exact (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) p).symm
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
                  (qAttachingCoverEnd_spec (namedQuotientBase ρ q u) t.1.2.2).symm))
      _ = mapPath (namedSurfaceIntoQuotient q ρ u)
          (mapPath (namedAttachingProjection q ρ u)
            (namedAttachingMarkingPath q ρ u hrho g i)) := (mapPath_comp _ _ _).symm
      _ = _ := congrArg (mapPath (namedSurfaceIntoQuotient q ρ u))
        (namedAttachingMarkingPath_spec q ρ u hrho g i).2
  have hsurf  :=
    (mapPath_comp (oldIntoNamedQuotient q ρ u) (surfCx _) (gSig q (i.1.val, i.2))).symm
  erw [hproj, hsurf] at he
  exact he

def namedAttachingMarkingChains :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun x => pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2))

theorem namedAttachingMarkingChains_image
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u) (namedAttachingMarkingChains q ρ u hrho c) =
      quotientSurfaceMarkingChains q ρ u hrho c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      erw [namedAttachingMarkingChains, quotientSurfaceMarkingChains,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul]
      apply congrArg (fun z => n • z)
      change Finsupp.mapDomain (namedAttachingIntoUniversal q ρ u).onE
        (pathChain (namedAttachingMarkingPath q ρ u hrho x.1 x.2)) = _
      erw [← pathChain_map]
      exact congrArg pathChain (namedAttachingMarkingPath_image q ρ u hrho x.1 x.2)

def namedAttachingNerveBoundary :
    ((PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      Ch (namedAttachingCover q ρ u) :=
  ordNerveChain1.comp (namedAttachingMarkingChains q ρ u hrho)


theorem namedAttachingNerveBoundary_image
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    universalNerveChain1 (quotientSurfaceMarkingChains q ρ u hrho c) =
      cmap Subtype.val (namedAttachingNerveBoundary q ρ u hrho c) := by
  erw [← namedAttachingMarkingChains_image q ρ u hrho c]
  change universalNerveChain1 (chain1
      (uOrderHom.comp (orderCxMap Subtype.val (fun _ _ h => h)))
      (namedAttachingMarkingChains q ρ u hrho c)) =
    cmap Subtype.val (ordNerveChain1 (namedAttachingMarkingChains q ρ u hrho c))
  erw [chain1_comp_apply, universalNerveChain1_uOrderHom, ordNerveChain1_chain1]

/-- The actual B2 coordinate equation supplies an actual attaching-cover two-chain
with the original marked boundary, and an old three-chain correcting its image. -/
theorem quotientCorrectedRelative_attaching_filling
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    ∃ c : Ch (namedAttachingCover q ρ u),
      c ∈ Inc _ ∧ lengthProjection 3 c = c ∧
      Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) ∧
      ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
        lengthProjection 4 y = y ∧
        quotientCorrectedRelativeNerveChain q ρ u hrho β =
          cmap Subtype.val c + Nerve.bdry y := by
  apply qUniversal_old_cellular_relative_chain_from_attaching
    (namedAtt ρ q u (gBase q)) (namedBasePos_isConnected ρ q u) (gBase q)
    (quotientCorrectedRelativeChain q ρ u hrho β)
    (quotientCorrectedRelativeChain_face_support q ρ u hrho β)
    (namedAttachingNerveBoundary q ρ u hrho
      ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))))
    (ordNerveChain1_mem_inc _)
  erw [quotientCorrectedRelativeChain_boundary q ρ u hrho β hβ,
    namedAttachingNerveBoundary_image]

end FiniteChains.Davis.Genus
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Vertices comparable with a chosen vertex; their induced nerve is its closed star. -/
def orderNerveVertexStar (P : Type) [PartialOrder P] (v : P) : Set P :=
  {a | a ≤ v ∨ v ≤ a}

/-- Identity vertex maps induce identity maps of the actual realization. -/
theorem orderNerveRealizationMap_id (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) : orderNerveRealizationMap id monotone_id x = x := by
  change SSet.toTop.map (𝟙 (nerve P)) x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Every order isomorphism induces a homeomorphism of the actual realizations. -/
def orderNerveRealizationOrderIso {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) : orderNerveRealization P ≃ₜ orderNerveRealization Q where
  toFun := orderNerveRealizationMap e e.monotone
  invFun := orderNerveRealizationMap e.symm e.symm.monotone
  left_inv x := by
    rw [orderNerveRealizationMap_comp]
    have he : (e.symm ∘ e : P → P) = id := by
      funext p
      exact e.symm_apply_apply p
    simp only [he, orderNerveRealizationMap_id]
  right_inv x := by
    rw [orderNerveRealizationMap_comp]
    have he : (e ∘ e.symm : Q → Q) = id := by
      funext q
      exact e.apply_symm_apply q
    simp only [he, orderNerveRealizationMap_id]
  continuous_toFun := (orderNerveRealizationMap e e.monotone).hom.continuous
  continuous_invFun := (orderNerveRealizationMap e.symm e.symm.monotone).hom.continuous

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A poset covering reflects order among vertices comparable with one fixed vertex. -/
theorem le_of_le_vertexStar (hf : IsPosetCover f) {a b v : P}
    (ha : a ∈ orderNerveVertexStar P v) (hb : b ∈ orderNerveVertexStar P v)
    (h : f a ≤ f b) : a ≤ b := by grind [hf.le_of_le_below, le_antisymm, hf.up_inj, hf.down_inj, hf.le_of_le_above, orderNerveVertexStar]

/-- The covering projection restricts to the comparable-vertex star. -/
def vertexStarMap (hf : IsPosetCover f) (v : P) :
    orderNerveVertexStar P v → orderNerveVertexStar Q (f v) :=
  fun a => ⟨f a.val, a.property.elim (fun h => Or.inl (hf.mono h))
    (fun h => Or.inr (hf.mono h))⟩

/-- Restricted star projections are bijective, by unique upper and lower interval lifts. -/
theorem vertexStarMap_bijective (hf : IsPosetCover f) (v : P) :
    Function.Bijective (hf.vertexStarMap v) := by
  constructor
  · intro a b h
    have he  := congrArg Subtype.val h
    ext
    exact le_antisymm (hf.le_of_le_vertexStar a.property b.property he.le)
      (hf.le_of_le_vertexStar b.property a.property he.symm.le)
  · intro q
    rcases q.property with hq | hq
    · obtain ⟨a, ⟨hav, hfa⟩, _⟩ := hf.down v q.val hq
      exact ⟨⟨a, Or.inl hav⟩, Subtype.ext hfa⟩
    · obtain ⟨a, ⟨hva, hfa⟩, _⟩ := hf.up v q.val hq
      exact ⟨⟨a, Or.inr hva⟩, Subtype.ext hfa⟩

/-- The actual comparable-vertex stars of a poset cover are order isomorphic. -/
def vertexStarOrderIso (hf : IsPosetCover f) (v : P) :
    orderNerveVertexStar P v ≃o orderNerveVertexStar Q (f v) where
  toEquiv := Equiv.ofBijective (hf.vertexStarMap v) (hf.vertexStarMap_bijective v)
  map_rel_iff' := by
    intro a b
    exact ⟨fun h => hf.le_of_le_vertexStar a.property b.property h, fun h => hf.mono h⟩

/-- The closed vertex stars have genuinely homeomorphic actual realizations. -/
def vertexStarRealizationHomeomorph (hf : IsPosetCover f) (v : P) :
    orderNerveRealization (orderNerveVertexStar P v) ≃ₜ
      orderNerveRealization (orderNerveVertexStar Q (f v)) :=
  orderNerveRealizationOrderIso (hf.vertexStarOrderIso v)

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- The actual open vertex star, defined by positivity of its global coordinate. -/
def orderNerveRealizationOpenStar (P : Type) [PartialOrder P] (v : P) :
    Set (orderNerveRealization P) := {x | 0 < orderNerveRealizationCoordinates P x v}

/-- Coordinate positivity defines an open subset of the actual realization. -/
theorem orderNerveRealizationOpenStar_isOpen (P : Type) [PartialOrder P] (v : P) :
    IsOpen (orderNerveRealizationOpenStar P v) := by
  exact isOpen_Ioi.preimage ((continuous_apply v).comp
    (orderNerveRealizationCoordinates P).continuous)

/-- On simplex interiors, open-star membership is exactly vertex membership. -/
theorem orderNerveRealizationSimplex_mem_openStar_iff {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (v : P) :
    orderNerveRealizationSimplex P s z ∈ orderNerveRealizationOpenStar P v ↔
      v ∈ Set.range s.obj := by
  have he := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun p => if p = v then 1 else 0) s)
  change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) v =
    orderNerveAffineSimplex (fun p => if p = v then 1 else 0) s z at he
  change 0 < orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) v ↔ _
  rw [he]
  exact orderNerveAffineSimplex_indicator_pos_iff s z hz v

/-- Actual open vertex stars cover the whole realization. -/
theorem orderNerveRealizationOpenStar_cover (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) : ∃ v, x ∈ orderNerveRealizationOpenStar P v := by
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  refine ⟨s.val.obj 0, ?_⟩
  rw [← he]
  exact (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz _).mpr ⟨0, rfl⟩

/-- Every point of an open star lies in the genuine comparable-vertex CW carrier. -/
theorem orderNerveRealizationOpenStar_subset_subcomplex {P : Type} [PartialOrder P]
    (v : P) : orderNerveRealizationOpenStar P v ⊆
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
        Set (orderNerveRealization P)) := by
  intro x hx
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  rw [← he] at hx ⊢
  obtain ⟨i, hi⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v).mp hx
  apply orderNerveRealizationSimplex_supported (orderNerveVertexStar P v) s.val _ ⟨z, rfl⟩
  intro j
  rcases le_total j i with h | h
  · exact Or.inl (hi ▸ leOfHom (s.val.map (homOfLE h)))
  · exact Or.inr (hi ▸ leOfHom (s.val.map (homOfLE h)))

/-- Open stars over distinct lifts of one vertex are disjoint. -/
theorem IsPosetCover.realizationOpenStar_disjoint {P Q : Type}
    [PartialOrder P] [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)
    {a b : P} (hab : a ≠ b) (he : f a = f b) :
    Disjoint (orderNerveRealizationOpenStar P a) (orderNerveRealizationOpenStar P b) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  rw [← hx] at hxa hxb
  obtain ⟨i, hi⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz a).mp hxa
  obtain ⟨j, hj⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz b).mp hxb
  have hij : f (s.val.obj i) = f (s.val.obj j) := by rw [hi, hj, he]
  rcases le_total i j with h | h
  · have hs := hf.up_inj (le_refl (s.val.obj i))
      (leOfHom (s.val.map (homOfLE h))) hij
    exact hab (hi.symm.trans (hs.trans hj))
  · have hs := hf.up_inj (le_refl (s.val.obj j))
      (leOfHom (s.val.map (homOfLE h))) hij.symm
    exact hab (hi.symm.trans (hs.symm.trans hj))

/-- The preimage of an open star is exactly the union of stars at its lifted vertices. -/
theorem orderNerveRealizationMap_mem_openStar_iff {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (x : orderNerveRealization P) (q : Q) :
    orderNerveRealizationMap f hf x ∈ orderNerveRealizationOpenStar Q q ↔
      ∃ p : P, f p = q ∧ x ∈ orderNerveRealizationOpenStar P p := by
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  rw [← hx]
  have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s.val)
  change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s.val z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s.val) z at hn
  rw [hn, orderNerveRealizationSimplex_mem_openStar_iff _ z hz]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨s.val.obj i, hi, ?_⟩
    exact (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz _).mpr ⟨i, rfl⟩
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨i, hi⟩ := (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz p).mp hxp
    exact ⟨i, (congrArg f hi).trans hp⟩

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical

/-- Compact parameter families are continuous on a realization exactly when they
are continuous on each of its simplices. -/
theorem orderNerveRealization_continuous_prod_iff (P : Type) [PartialOrder P]
    {T X : Type*} [TopologicalSpace T] [LocallyCompactSpace T] [TopologicalSpace X]
    (f : T × orderNerveRealization P → X) :
    Continuous f ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      Continuous (fun p : T × SimplexCategory.toTop.obj n =>
        f (p.1, orderNerveRealizationSimplex P s p.2)) := by
  constructor
  · intro h n s
    exact h.comp (continuous_fst.prodMk
      ((orderNerveRealizationSimplex P s).hom.continuous.comp continuous_snd))
  · intro h
    have ht : ∀ x, Continuous (fun t : T => f (t, x)) := by
      intro x
      obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
      exact (h n s).comp (continuous_id.prodMk continuous_const)
    let g : orderNerveRealization P → C(T, X) := fun x => ⟨_, ht x⟩
    have hg : Continuous g := by
      apply (orderNerveRealization_continuous_iff P g).mpr
      intro n s
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (h n s).comp continuous_swap
    exact (ContinuousMap.continuous_uncurry_of_continuous ⟨g, hg⟩).comp continuous_swap

/-- Adjoining a vertex comparable with every vertex of a simplex gives a larger
simplex, together with a simplex operator containing the original one. -/
theorem orderNerveSimplex_extend_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (v : P)
    (hv : ∀ i, s.obj i ≤ v ∨ v ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (j : Fin (m.len + 1)),
      (nerve P).map a.op u = s ∧ u.obj j = v := by
  let A  := insert v (Set.range s.obj)
  have hA : IsChain (· ≤ ·) A := by
    intro x hx y hy _
    rcases hx with rfl | ⟨i, rfl⟩
    · grind
    · rcases hy with rfl | ⟨j, rfl⟩
      · exact hv i
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (s.map (homOfLE h)))
        · exact Or.inr (leOfHom (s.map (homOfLE h)))
  letI : Fintype A := (Set.finite_range s.obj |>.insert v).fintype
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  let av : A := ⟨v, Set.mem_insert v _⟩
  letI : Nonempty A := ⟨av⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e  := (Fintype.orderIsoFinOfCardEq A hk).symm
  let u  :=
    (show Monotone (fun i : Fin (k + 1) => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor
  let a  := SimplexCategory.mkHom
    ⟨fun i => e ⟨s.obj i, Set.mem_insert_of_mem _ ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (s.map (homOfLE h)))⟩
  refine ⟨⦋k⦌, u, a, e av, ?_, ?_⟩
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply
        ⟨s.obj i, Set.mem_insert_of_mem _ ⟨i, rfl⟩⟩))
  · exact congrArg Subtype.val (e.symm_apply_apply av)

/-- Straight-line interpolation inside a topological simplex. -/
def topologicalSimplexBlend {n : SimplexCategory}
    (t : I) (z w : SimplexCategory.toTop.obj n) : SimplexCategory.toTop.obj n :=
  ULift.up ((TopologicalSingular.simplexCoordinates n.len).symm
    ⟨(1 - (t : ℝ)) • (TopologicalSingular.simplexCoordinates n.len z.down).val +
      (t : ℝ) • (TopologicalSingular.simplexCoordinates n.len w.down).val,
      convex_stdSimplex ℝ _ (TopologicalSingular.simplexCoordinates n.len z.down).property
        (TopologicalSingular.simplexCoordinates n.len w.down).property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩)

theorem topologicalSimplexBlend_continuous {n : SimplexCategory} :
    Continuous (fun p : I × (SimplexCategory.toTop.obj n × SimplexCategory.toTop.obj n) =>
      topologicalSimplexBlend p.1 p.2.1 p.2.2) := by
  unfold topologicalSimplexBlend
  fun_prop

theorem orderNerveAffineSimplex_blend {P : Type} [PartialOrder P] (v : P → ℝ)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : I) (z w : SimplexCategory.toTop.obj n) :
    orderNerveAffineSimplex v s (topologicalSimplexBlend t z w) =
      (1 - (t : ℝ)) * orderNerveAffineSimplex v s z +
        (t : ℝ) * orderNerveAffineSimplex v s w := by
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk, topologicalSimplexBlend,
    TopologicalSingular.simplexCoordinates_symm_weights_apply,
    TopologicalSingular.simplexCoordinates_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

/-- The affine interpolation formula in global coordinates. -/
theorem orderNerveRealizationCoordinates_blend {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : I) (z w : SimplexCategory.toTop.obj n) (p : P) :
    orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s (topologicalSimplexBlend t z w)) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s z) p +
      (t : ℝ) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s w) p := by
  have h z := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s)
  change ∀ z, orderNerveAffineRealization (fun q => if q = p then 1 else 0)
    (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z at h
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s _) =
    (1 - t) * orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) +
    (t : ℝ) * orderNerveAffineRealization _ (orderNerveRealizationSimplex P s w)
  rw [h, h, h, orderNerveAffineSimplex_blend]

/-- A vertex comparable with the whole poset can be joined affinely to every
realization point, with a uniquely prescribed global coordinate vector. -/
theorem orderNerveRealization_cone_exists {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) :
    ∃ y : orderNerveRealization P, ∀ p,
      orderNerveRealizationCoordinates P y p =
        (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
        (t : ℝ) * (if v = p then 1 else 0) := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, j, hs, hj⟩ := orderNerveSimplex_extend_vertex s v (fun i => hv (s.obj i))
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex u j
  rw [hj] at hw
  have hz := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a u)
  change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a z) =
    orderNerveRealizationSimplex P ((nerve P).map a.op u) z at hz
  rw [hs] at hz
  refine ⟨orderNerveRealizationSimplex P u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) w), fun p => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, hz, hw,
    orderNerveRealizationCoordinates_vertex]

/-- The affine cone towards a universally comparable vertex. -/
def orderNerveRealizationCone {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) :
    orderNerveRealization P := (orderNerveRealization_cone_exists v hv t x).choose

theorem orderNerveRealizationCone_coordinates {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationCone v hv t x) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
      (t : ℝ) * (if v = p then 1 else 0) :=
  (orderNerveRealization_cone_exists v hv t x).choose_spec p

/-- The affine cone is jointly continuous in the weak CW topology, without any
local finiteness hypothesis on the poset. -/
theorem orderNerveRealizationCone_continuous {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) :
    Continuous (fun tx : I × orderNerveRealization P =>
      orderNerveRealizationCone v hv tx.1 tx.2) := by
  apply (orderNerveRealization_continuous_prod_iff P _).mpr
  intro n s
  obtain ⟨m, u, a, j, hs, hj⟩ := orderNerveSimplex_extend_vertex s v (fun i => hv (s.obj i))
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex u j
  rw [hj] at hw
  have hz z := congrArg (fun k => k z)
    (orderNerveRealizationSimplex_operator P a u)
  have he : (fun tx : I × SimplexCategory.toTop.obj n =>
      orderNerveRealizationCone v hv tx.1 (orderNerveRealizationSimplex P s tx.2)) =
      (fun tx => orderNerveRealizationSimplex P u
        (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2) w)) := by
    funext tx
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_blend, hw,
      orderNerveRealizationCoordinates_vertex]
    have hz' := hz tx.2
    change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a tx.2) =
      orderNerveRealizationSimplex P ((nerve P).map a.op u) tx.2 at hz'
    rw [hs] at hz'
    rw [hz']
  rw [he]
  exact (orderNerveRealizationSimplex P u).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp
      (continuous_fst.prodMk (((SimplexCategory.toTop.map a).hom.continuous.comp
        continuous_snd).prodMk continuous_const)))

@[simp] theorem orderNerveRealizationCone_zero {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 0 x = x := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  simp [orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRealizationCone_one {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 1 x = orderNerveRealizationVertex v := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  simp [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_vertex]

/-- A poset with a universally comparable vertex has contractible realization. -/
theorem orderNerveRealization_contractible_of_comparable {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) : ContractibleSpace (orderNerveRealization P) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨orderNerveRealizationVertex v, ⟨?_⟩⟩
  exact
    { toFun := fun tx => orderNerveRealizationCone v hv tx.1 tx.2
      continuous_toFun := orderNerveRealizationCone_continuous v hv
      map_zero_left := fun x => orderNerveRealizationCone_zero v hv x
      map_one_left := fun x => orderNerveRealizationCone_one v hv x }

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

theorem orderNerveRealizationCoordinates_simplex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
      orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z :=
  congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s)

theorem orderNerveRealizationCoordinates_nonneg {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) (p : P) :
    0 ≤ orderNerveRealizationCoordinates P x p := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  rw [orderNerveRealizationCoordinates_simplex]
  change 0 ≤ ∑ i, z.down.weights i * (if s.obj i = p then 1 else 0)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (z.down.weights_nonneg i) (by split_ifs <;> norm_num)

theorem orderNerveRealizationCoordinates_sum {P : Type} [PartialOrder P] [Fintype P]
    (x : orderNerveRealization P) : ∑ p, orderNerveRealizationCoordinates P x p = 1 := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  simp only [orderNerveRealizationCoordinates_simplex, orderNerveAffineSimplex,
    ContinuousMap.coe_mk]
  rw [Finset.sum_comm]
  simp

theorem orderNerveRealizationCoordinates_support_chain {P : Type} [PartialOrder P]
    (x : orderNerveRealization P) :
    IsChain (· ≤ ·) {p | 0 < orderNerveRealizationCoordinates P x p} := by
  obtain ⟨n, s, z, hz, rfl⟩ := orderNerveRealization_interior_cover P x
  intro p hp q hq _
  rw [Set.mem_setOf_eq, orderNerveRealizationCoordinates_simplex] at hp hq
  obtain ⟨i, rfl⟩ := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz p).mp hp
  obtain ⟨j, rfl⟩ := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz q).mp hq
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

/-- Every probability vector whose positive support is a chain represents
an actual point of the geometric realization, with precisely those coordinates. -/
theorem orderNerveRealizationCoordinates_exists {P : Type} [PartialOrder P] [Fintype P]
    (c : P → ℝ) (hc : ∀ p, 0 ≤ c p) (hsum : ∑ p, c p = 1)
    (hchain : IsChain (· ≤ ·) {p | 0 < c p}) :
    ∃ x : orderNerveRealization P, ∀ p, orderNerveRealizationCoordinates P x p = c p := by
  let A := {p : P // 0 < c p}
  have hzero  :=
    fun p hp => le_antisymm (le_of_not_gt hp) (hc p)
  have hA : ∑ p : A, c p.val = 1 := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun p => 0 < c p) c
    have hz : (∑ p : {p : P // ¬ 0 < c p}, c p.val) = 0 :=
      Finset.sum_eq_zero (fun p _ => hzero p.val p.property)
    rw [hz, add_zero, hsum] at h
    exact h
  have hne : Nonempty A := by
    by_contra hn
    haveI := not_nonempty_iff.mp hn
    simp at hA
  letI := hne
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hchain.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e  := (Fintype.orderIsoFinOfCardEq A hn).symm
  let s : (nerve P).obj (Opposite.op ⦋n⦌) :=
    (show Monotone (fun i : Fin (n + 1) => (e.symm i).val) from
      fun _ _ hij => e.symm.monotone hij).functor
  have hs : Function.Injective s.obj := Subtype.val_injective.comp e.symm.injective
  let zold : stdSimplex ℝ (Fin (n + 1)) := ⟨fun i => c (s.obj i),
    ⟨fun i => hc (s.obj i), by
      change (∑ i : Fin (n + 1), c (e.symm i).val) = 1
      exact (e.symm.toEquiv.sum_comp (fun a : A => c a.val)).trans hA⟩⟩
  let z : SimplexCategory.toTop.obj ⦋n⦌ :=
    ULift.up ((TopologicalSingular.simplexCoordinates n).symm zold)
  refine ⟨orderNerveRealizationSimplex P s z, ?_⟩
  intro p
  by_cases hp : 0 < c p
  · let i := e ⟨p, hp⟩
    have hi : s.obj i = p := congrArg Subtype.val (e.symm_apply_apply ⟨p, hp⟩)
    calc
      orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
          orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) (s.obj i) :=
        congrArg (orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z)) hi.symm
      _ = z.down.weights i := (orderNerveRealizationCoordinates_simplex s z (s.obj i)).trans
        (orderNerveAffineSimplex_indicator s hs i z)
      _ = c p := by
        simpa only [z, TopologicalSingular.simplexCoordinates_symm_weights_apply] using congrArg c hi
  · have hn : ∀ i, s.obj i ≠ p := by
      intro i hi
      exact hp (hi ▸ (e.symm i).property)
    rw [orderNerveRealizationCoordinates_simplex]
    simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk, hn, ite_false, mul_zero,
      Finset.sum_const_zero, hzero p hp]

end FiniteChains.Comb

section
open scoped Classical unitInterval
open Set Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment

def squareCorner00 : SquareBoundary := squareSideMap (0, false) 0
def squareCorner01 : SquareBoundary := squareSideMap (0, false) 1
def squareCorner11 : SquareBoundary := squareSideMap (0, true) 1
def squareCorner10 : SquareBoundary := squareSideMap (0, true) 0

def squareTraversalLeft : Path squareCorner00 squareCorner01 where
  toContinuousMap := squareSideMap (0, false)
  source' := rfl
  target' := rfl

def squareTraversalTop : Path squareCorner01 squareCorner11 where
  toContinuousMap := squareSideMap (1, true)
  source' := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  target' := by apply Subtype.ext; funext i; fin_cases i <;> rfl

def squareTraversalRight : Path squareCorner11 squareCorner10 :=
  ({ toContinuousMap := squareSideMap (0, true)
     source' := rfl
     target' := rfl } : Path squareCorner10 squareCorner11).symm

def squareTraversalBottom : Path squareCorner10 squareCorner00 :=
  ({ toContinuousMap := squareSideMap (1, false)
     source' := by apply Subtype.ext; funext i; fin_cases i <;> rfl
     target' := by apply Subtype.ext; funext i; fin_cases i <;> rfl } :
      Path squareCorner00 squareCorner10).symm

/-- The balanced concatenation allocates one quarter of the interval to
each side, in positive once-around order. -/
def squareBoundaryTraversal : Path squareCorner00 squareCorner00 :=
  (squareTraversalLeft.trans squareTraversalTop).trans
    (squareTraversalRight.trans squareTraversalBottom)

theorem squareBoundaryTraversal_surjective : Function.Surjective squareBoundaryTraversal := by
  intro z
  obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
  change squareSideMap s t ∈ Set.range squareBoundaryTraversal
  simp only [squareBoundaryTraversal, Path.trans_range]
  rcases s with ⟨i, b⟩
  fin_cases i <;> cases b
  · exact Or.inl (Or.inl ⟨t, rfl⟩)
  · exact Or.inr (Or.inl ⟨unitInterval.symm t, by
      simp [squareTraversalRight]⟩)
  · exact Or.inr (Or.inr ⟨unitInterval.symm t, by
      simp [squareTraversalBottom]⟩)
  · exact Or.inl (Or.inr ⟨t, rfl⟩)

/-- There is no hidden multiple traversal: only zero and one coincide. -/
theorem squareBoundaryTraversal_fiber {s t : I}
    (h : squareBoundaryTraversal s = squareBoundaryTraversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have coords u :
      (((squareBoundaryTraversal u).val 0 : ℝ), ((squareBoundaryTraversal u).val 1 : ℝ)) =
        if (u : ℝ) ≤ 1 / 2 then
          if 2 * (u : ℝ) ≤ 1 / 2 then (0, 4 * (u : ℝ)) else (4 * (u : ℝ) - 1, 1)
        else if 2 * (u : ℝ) - 1 ≤ 1 / 2 then (1, 3 - 4 * (u : ℝ))
        else (4 - 4 * (u : ℝ), 0) := by
    simp only [squareBoundaryTraversal, Path.trans_apply]
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · rw [dif_pos hu, if_pos hu]
      by_cases hv : 2 * (u : ℝ) ≤ 1 / 2
      · rw [dif_pos hv, if_pos hv]
        simp [squareTraversalLeft, squareSideMap, Whitehead.squareEdge, boolEndpoint]
        ring
      · rw [dif_neg hv, if_neg hv]
        simp [squareTraversalTop, squareSideMap, Whitehead.squareEdge, boolEndpoint]
        ring
    · rw [dif_neg hu, if_neg hu]
      by_cases hv : 2 * (u : ℝ) - 1 ≤ 1 / 2
      · rw [dif_pos hv, if_pos hv]
        simp [squareTraversalRight, squareSideMap, Whitehead.squareEdge, boolEndpoint,
          Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq]
        ring
      · rw [dif_neg hv, if_neg hv]
        simp [squareTraversalBottom, squareSideMap, Whitehead.squareEdge, boolEndpoint,
          Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq]
        ring
  have he := (coords s).symm.trans
    ((congrArg (fun z : SquareBoundary => ((z.val 0 : ℝ), (z.val 1 : ℝ))) h).trans (coords t))
  have hs₀ := s.property.1
  have hs₁ := s.property.2
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> rcases he with ⟨h₀, h₁⟩ <;>
    first
    | exact Or.inl (Subtype.ext (by linarith))
    | exact Or.inr (Or.inl ⟨Subtype.ext (show (s : ℝ) = 0 by linarith),
        Subtype.ext (show (t : ℝ) = 1 by linarith)⟩)
    | exact Or.inr (Or.inr ⟨Subtype.ext (show (s : ℝ) = 1 by linarith),
        Subtype.ext (show (t : ℝ) = 0 by linarith)⟩)

theorem squareBoundaryTraversal_isQuotientMap : IsQuotientMap squareBoundaryTraversal :=
  squareBoundaryTraversal.continuous.isClosedMap.isQuotientMap
    squareBoundaryTraversal.continuous squareBoundaryTraversal_surjective

variable {X : Type} [TopologicalSpace X]

def squareLoopDesc {x : X} (p : Path x x) : C(SquareBoundary, X) where
  toFun z := p (Function.surjInv squareBoundaryTraversal_surjective z)
  continuous_toFun := by
    apply squareBoundaryTraversal_isQuotientMap.continuous_iff.mpr
    have he : (fun z => p (Function.surjInv squareBoundaryTraversal_surjective z)) ∘
        squareBoundaryTraversal = p := by
      funext t
      change p (Function.surjInv squareBoundaryTraversal_surjective (squareBoundaryTraversal t)) = p t
      have h := Function.surjInv_eq squareBoundaryTraversal_surjective (squareBoundaryTraversal t)
      rcases squareBoundaryTraversal_fiber h with h | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · simp_all
      · simp_all
      · simp_all
    rw [he]
    exact p.continuous

@[simp] theorem squareLoopDesc_traversal {x : X} (p : Path x x) (t : I) :
    squareLoopDesc p (squareBoundaryTraversal t) = p t := by
  have h := Function.surjInv_eq squareBoundaryTraversal_surjective (squareBoundaryTraversal t)
  rcases squareBoundaryTraversal_fiber h with h | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact congrArg p h
  · change p _ = p t
    rw [h₀, h₁, p.source, p.target]
  · change p _ = p t
    rw [h₀, h₁, p.source, p.target]

theorem squareLoopDesc_map (f : C(SquareBoundary, X)) :
    squareLoopDesc (squareBoundaryTraversal.map f.continuous) = f := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective z
  exact squareLoopDesc_traversal _ t

/-- A homotopy of based traversal loops gives a homotopy of the actual
attaching maps; equality of group words is never used as a substitute. -/
def squareLoopDescHomotopy {x : X} {p q : Path x x} (H : p.Homotopy q) :
    (squareLoopDesc p).Homotopy (squareLoopDesc q) := by
  let F : C(I, C(I, X)) := (H.toHomotopy.toContinuousMap.comp
    ⟨Prod.swap, continuous_swap⟩).curry
  let D : C(SquareBoundary, C(I, X)) := {
    toFun z := F (Function.surjInv squareBoundaryTraversal_surjective z)
    continuous_toFun := by
      apply squareBoundaryTraversal_isQuotientMap.continuous_iff.mpr
      have he : (fun z => F (Function.surjInv squareBoundaryTraversal_surjective z)) ∘
          squareBoundaryTraversal = F := by
        funext s
        apply ContinuousMap.ext
        intro τ
        have hs := Function.surjInv_eq squareBoundaryTraversal_surjective (squareBoundaryTraversal s)
        rcases squareBoundaryTraversal_fiber hs with hs | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
        · exact congrArg (fun z => H (τ, z)) hs
        · change H (τ, _) = H (τ, s)
          rw [h₀, h₁, H.source, H.target]
        · change H (τ, _) = H (τ, s)
          rw [h₀, h₁, H.source, H.target]
      rw [he]
      exact F.continuous }
  exact {
    toContinuousMap := D.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun z => H.apply_zero _
    map_one_left := fun z => H.apply_one _ }

theorem squareLoopDesc_homotopic {x : X} {p q : Path x x} (H : p.Homotopic q) :
    (squareLoopDesc p).Homotopic (squareLoopDesc q) :=
  Nonempty.map squareLoopDescHomotopy H

end FiniteChains.RelativeAttachment
end

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.RelativeAttachment

variable {X : Type} [TopologicalSpace X]

theorem path_trans_injective {a b c : X} (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : I, p s = q t → p s = b) : Function.Injective (p.trans q) := by
  intro s t h
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · grind
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at h
    have hb := hmeet _ _ h
    have hv := congrArg (fun z : I => z) (hp (hb.trans p.target.symm))
    have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.symm.trans hb).trans q.source.symm))
    apply Subtype.ext
    dsimp at hv hw
    linarith
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_pos ht] at h
    have hb := hmeet _ _ h.symm
    have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
    have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.trans hb).trans q.source.symm))
    apply Subtype.ext
    dsimp at hv hw
    linarith
  · grind

/-- Two arcs meeting only at their endpoints form a loop with exactly the
expected endpoint identification. -/
theorem path_trans_loop_fiber {a b : X} (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : I, p s = q t → p s = a ∨ p s = b)
    {s t : I} (h : (p.trans q) s = (p.trans q) t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · grind
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at h
    rcases hmeet _ _ h with ha | hb
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (ha.trans p.source.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.symm.trans ha).trans q.target.symm))
      exact Or.inr (Or.inl ⟨Subtype.ext (by change (s : ℝ) = 0; dsimp at hv; linarith),
        Subtype.ext (by change (t : ℝ) = 1; dsimp at hw; linarith)⟩)
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.symm.trans hb).trans q.source.symm))
      exact Or.inl (Subtype.ext (by dsimp at hv hw; linarith))
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_pos ht] at h
    rcases hmeet _ _ h.symm with ha | hb
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (ha.trans p.source.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.trans ha).trans q.target.symm))
      exact Or.inr (Or.inr ⟨Subtype.ext (by change (s : ℝ) = 1; dsimp at hw; linarith),
        Subtype.ext (by change (t : ℝ) = 0; dsimp at hv; linarith)⟩)
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.trans hb).trans q.source.symm))
      exact Or.inl (Subtype.ext (by dsimp at hv hw; linarith))
  · grind


def simpleLoopSquareHomeomorph [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    SquareBoundary ≃ₜ X := by
  letI : CompactSpace SquareBoundary := ⟨by
    simpa only [Set.range_eq_univ.mpr squareBoundaryTraversal_surjective] using
      (isCompact_range squareBoundaryTraversal.continuous)⟩
  exact Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (squareLoopDesc p) (by
      constructor
      · intro x y h
        obtain ⟨s, rfl⟩ := squareBoundaryTraversal_surjective x
        obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective y
        rw [squareLoopDesc_traversal, squareLoopDesc_traversal] at h
        rcases hfiber s t h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact squareBoundaryTraversal.source.trans squareBoundaryTraversal.target.symm
        · exact squareBoundaryTraversal.target.trans squareBoundaryTraversal.source.symm
      · intro x
        obtain ⟨t, rfl⟩ := hsur x
        exact ⟨squareBoundaryTraversal t, squareLoopDesc_traversal p t⟩))
    (squareLoopDesc p).continuous

def simpleLoopBoundaryHomeomorph [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    UnitBoundary (Fin 2 → ℝ) ≃ₜ X :=
  unitBoundarySquareHomeomorph.trans (simpleLoopSquareHomeomorph p hsur hfiber)

@[simp] theorem simpleLoopSquareHomeomorph_traversal [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) (t : I) :
    simpleLoopSquareHomeomorph p hsur hfiber (squareBoundaryTraversal t) = p t :=
  squareLoopDesc_traversal p t

end FiniteChains.RelativeAttachment
end

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.Comb
open CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineEdgeSimplex {a b : P} (h : a ≤ b) :
    (nerve P).obj (Opposite.op ⦋1⦌) := ComposableArrows.mk₁ (homOfLE h)

def affineEdgeEndpoint {a b : P} (h : a ≤ b) (i : Fin 2) :
    SimplexCategory.toTop.obj ⦋1⦌ :=
  Classical.choose (orderNerveRealizationVertex_mem_simplex (affineEdgeSimplex h) i)

theorem affineEdgeEndpoint_spec {a b : P} (h : a ≤ b) (i : Fin 2) :
    orderNerveRealizationSimplex P (affineEdgeSimplex h) (affineEdgeEndpoint h i) =
      orderNerveRealizationVertex ((affineEdgeSimplex h).obj i) :=
  Classical.choose_spec (orderNerveRealizationVertex_mem_simplex (affineEdgeSimplex h) i)

def orderNerveAffineEdgePath {a b : P} (h : a ≤ b) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) where
  toFun t := orderNerveRealizationSimplex P (affineEdgeSimplex h)
    (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))
  continuous_toFun := (orderNerveRealizationSimplex P (affineEdgeSimplex h)).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp (continuous_id.prodMk
      (continuous_const.prodMk continuous_const)))
  source' := by
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
    simp
    rfl
  target' := by
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
    simp
    rfl

theorem orderNerveAffineEdgePath_coordinates {a b : P} (h : a ≤ b) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveAffineEdgePath h t) p =
      (1 - (t : ℝ)) * (if a = p then 1 else 0) + (t : ℝ) * (if b = p then 1 else 0) := by
  change orderNerveRealizationCoordinates P
    (orderNerveRealizationSimplex P (affineEdgeSimplex h)
      (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))) p = _
  rw [orderNerveRealizationCoordinates_blend, affineEdgeEndpoint_spec, affineEdgeEndpoint_spec]
  simp only [orderNerveRealizationCoordinates_vertex]
  rfl

def orderNerveComparablePath {a b : P} (h : a ≤ b ∨ b ≤ a) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) :=
  if hab : a ≤ b then orderNerveAffineEdgePath hab
  else (orderNerveAffineEdgePath (h.resolve_left hab)).symm

theorem orderNerveComparablePath_coordinates {a b : P} (h : a ≤ b ∨ b ≤ a) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveComparablePath h t) p =
      (1 - (t : ℝ)) * (if a = p then 1 else 0) + (t : ℝ) * (if b = p then 1 else 0) := by
  by_cases hab : a ≤ b
  · simpa only [orderNerveComparablePath, dif_pos hab] using orderNerveAffineEdgePath_coordinates hab t p
  · simp only [orderNerveComparablePath, dif_neg hab, Path.symm_apply, Function.comp_apply,
      orderNerveAffineEdgePath_coordinates, unitInterval.coe_symm_eq]
    ring

theorem orderNerveAffineRealization_vertex (v : P → ℝ) (p : P) :
    orderNerveAffineRealization v (orderNerveRealizationVertex p) = v p := by
  have h := congrArg (fun k => k default)
    (orderNerveAffineRealization_simplex v (n := ⦋0⦌) (ComposableArrows.mk₀ p))
  change orderNerveAffineRealization v (orderNerveRealizationVertex p) =
    orderNerveAffineSimplex.{0} v (n := ⦋0⦌) (ComposableArrows.mk₀ p) default at h
  rw [h]
  haveI : Unique (Fin (⦋0⦌.len + 1)) := by
    simpa using (inferInstance : Unique (Fin 1))
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk, ComposableArrows.mk₀,
    Fintype.sum_unique, Functor.const_obj_obj]
  have hone := (default : SimplexCategory.toTop.{0}.obj ⦋0⦌).down.total_of_fintype
  simp only [Fintype.sum_unique] at hone
  exact (congrArg (fun a : ℝ => a * v p) hone).trans (one_mul _)

theorem orderNerveAffineEdgePath_affine (v : P → ℝ) {a b : P}
    (h : a ≤ b) (t : I) :
    orderNerveAffineRealization v (orderNerveAffineEdgePath h t) =
      (1 - (t : ℝ)) * v a + (t : ℝ) * v b := by
  have hs (z : SimplexCategory.toTop.obj ⦋1⦌) := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex v (affineEdgeSimplex h))
  change ∀ z, orderNerveAffineRealization v
    (orderNerveRealizationSimplex P (affineEdgeSimplex h) z) =
      orderNerveAffineSimplex v (affineEdgeSimplex h) z at hs
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P (affineEdgeSimplex h)
    (topologicalSimplexBlend t (affineEdgeEndpoint h 0) (affineEdgeEndpoint h 1))) = _
  rw [hs, orderNerveAffineSimplex_blend, ← hs, ← hs,
    affineEdgeEndpoint_spec, affineEdgeEndpoint_spec,
    orderNerveAffineRealization_vertex, orderNerveAffineRealization_vertex]
  rfl

theorem orderNerveComparablePath_affine (v : P → ℝ) {a b : P}
    (h : a ≤ b ∨ b ≤ a) (t : I) :
    orderNerveAffineRealization v (orderNerveComparablePath h t) =
      (1 - (t : ℝ)) * v a + (t : ℝ) * v b := by
  by_cases hab : a ≤ b
  · simpa only [orderNerveComparablePath, dif_pos hab] using
      orderNerveAffineEdgePath_affine v hab t
  · simp only [orderNerveComparablePath, dif_neg hab, Path.symm_apply, Function.comp_apply]
    rw [orderNerveAffineEdgePath_affine v (h.resolve_left hab), unitInterval.coe_symm_eq]
    ring

/-- Collapsing vertices is allowed: the affine path formula is natural for
every monotone map, including the actual letter-reading map. -/
theorem orderNerveComparablePath_natural {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) {a b : P} (h : a ≤ b ∨ b ≤ a)
    (h' : f a ≤ f b ∨ f b ≤ f a) (t : I) :
    orderNerveRealizationMap f hf (orderNerveComparablePath h t) =
      orderNerveComparablePath h' t := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  change orderNerveAffineRealization (fun z => if z = q then 1 else 0)
    (orderNerveRealizationMap f hf (orderNerveComparablePath h t)) = _
  rw [orderNerveAffineRealization_natural, orderNerveComparablePath_affine,
    orderNerveComparablePath_coordinates]
  rfl

theorem orderNerveComparablePath_injective {a b : P} (h : a ≤ b ∨ b ≤ a) (hne : a ≠ b) :
    Function.Injective (orderNerveComparablePath h) := by
  intro s t hst
  have hcoord := congrArg (fun x => orderNerveRealizationCoordinates P x b) hst
  simp only [orderNerveComparablePath_coordinates, if_neg hne, ite_true,
    mul_zero, mul_one, zero_add] at hcoord
  exact Subtype.ext hcoord

theorem orderNerveComparablePath_of_support [Fintype P] {a b : P}
    (h : a ≤ b ∨ b ≤ a) (hne : a ≠ b) (x : orderNerveRealization P)
    (hx : ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0) :
    ∃ t : I, orderNerveComparablePath h t = x := by
  let c := orderNerveRealizationCoordinates P x
  have hsum : c a + c b = 1 := by
    calc
      c a + c b = ∑ p ∈ ({a, b} : Finset P), c p := by simp [hne]
      _ = ∑ p : P, c p := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro p _ hp
        simp at hp
        exact hx p hp.1 hp.2
      _ = 1 := orderNerveRealizationCoordinates_sum x
  have ha := orderNerveRealizationCoordinates_nonneg x a
  have hb := orderNerveRealizationCoordinates_nonneg x b
  let t : I := ⟨c b, hb, by dsimp [c] at hsum ⊢; linarith⟩
  refine ⟨t, ?_⟩
  apply orderNerveRealizationCoordinates_injective P
  funext p
  rw [orderNerveComparablePath_coordinates]
  by_cases hpa : p = a
  · grind
  · grind

end FiniteChains.Comb
end

section
open scoped Classical unitInterval
open Set
namespace FiniteChains.RelativeAttachment

variable {X : Type} [TopologicalSpace X]

/-- `n+1` arcs, with no artificial stationary part. -/
def arcConcat : (n : ℕ) → (v : Fin (n + 2) → X) →
    (∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) → Path (v 0) (v (Fin.last (n + 1)))
  | 0, _, F => F 0
  | n + 1, v, F =>
      (arcConcat n (v ∘ Fin.castSucc) (fun i => F i.castSucc)).trans (F (Fin.last (n + 1)))

theorem arcConcat_homotopic_concat (n : ℕ) (v : Fin (n + 2) → X)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) :
    (arcConcat n v F).Homotopic (Path.concat v F) := by
  induction n with
  | zero =>
    rw [Path.concat_succ, Path.concat_zero]
    exact (Path.Homotopic.refl_trans (F 0)).symm
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (v ∘ Fin.castSucc) (fun i => F i.castSucc)).hcomp
      (Path.Homotopic.refl (F (Fin.last (n + 1))))

theorem arcConcat_range (n : ℕ) (v : Fin (n + 2) → X)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) (x : X) :
    x ∈ Set.range (arcConcat n v F) ↔ ∃ i, x ∈ Set.range (F i) := by
  induction n with
  | zero =>
    constructor
    · intro hx
      exact ⟨0, hx⟩
    · rintro ⟨i, hi⟩
      have hi0 : i = 0 := Fin.ext (by omega)
      subst i
      exact hi
  | succ n ih =>
    change x ∈ Set.range
      ((arcConcat n (v ∘ Fin.castSucc) (fun i => F i.castSucc)).trans (F (Fin.last (n + 1)))) ↔ _
    rw [Path.trans_range, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi⟩ | hlast)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), hlast⟩
    · rintro ⟨i, hi⟩
      refine Fin.lastCases (fun hi => Or.inr hi)
        (fun j hj => Or.inl ⟨j, hj⟩) i hi

theorem arcConcat_injective (n : ℕ) (v : Fin (n + 2) → X)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ))
    (hF : ∀ i, Function.Injective (F i))
    (hmeet : ∀ i j : Fin (n + 1), i < j → ∀ s t : I,
      F i s = F j t → s = 1 ∧ t = 0) : Function.Injective (arcConcat n v F) := by
  induction n with
  | zero => exact hF 0
  | succ n ih =>
    apply path_trans_injective
    · exact ih (v ∘ Fin.castSucc) (fun i => F i.castSucc)
        (fun i => hF i.castSucc)
        (fun i j hij s t h => hmeet i.castSucc j.castSucc hij s t h)
    · exact hF (Fin.last (n + 1))
    · intro s t h
      obtain ⟨i, u, hu⟩ := (arcConcat_range n (v ∘ Fin.castSucc)
        (fun i => F i.castSucc) _).mp ⟨s, rfl⟩
      have ht  := (hmeet i.castSucc (Fin.last (n + 1))
        (by exact Fin.castSucc_lt_last i) u t (hu.trans h)).2
      rw [ht, (F (Fin.last (n + 1))).source] at h
      exact h

end FiniteChains.RelativeAttachment
end

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.Comb
open RelativeAttachment

structure FinitePosetCycle (P : Type) [PartialOrder P] (n : ℕ) where
  positive : 0 < n
  vertex : Fin (n + 2) ≃ P
  consecutive : ∀ i : Fin (n + 1),
    vertex i.castSucc ≤ vertex i.succ ∨ vertex i.succ ≤ vertex i.castSucc
  closing : vertex (Fin.last (n + 1)) ≤ vertex 0 ∨ vertex 0 ≤ vertex (Fin.last (n + 1))
  edges : ∀ a b : P, a ≠ b → (a ≤ b ∨ b ≤ a) →
    (∃ i : Fin (n + 1), (a = vertex i.castSucc ∧ b = vertex i.succ) ∨
      (b = vertex i.castSucc ∧ a = vertex i.succ)) ∨
    (a = vertex (Fin.last (n + 1)) ∧ b = vertex 0) ∨
      (b = vertex (Fin.last (n + 1)) ∧ a = vertex 0)
  height : P → ℕ
  height_strict : StrictMono height
  height_le : ∀ p, height p ≤ 1

namespace FinitePosetCycle

variable {P : Type} [PartialOrder P] {n : ℕ} (C : FinitePosetCycle P n)

def edge (i : Fin (n + 1)) := orderNerveComparablePath (C.consecutive i)
def lastEdge := orderNerveComparablePath C.closing

theorem edge_coordinates (i : Fin (n + 1)) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (C.edge i t) p =
      (1 - (t : ℝ)) * (if C.vertex i.castSucc = p then 1 else 0) +
        (t : ℝ) * (if C.vertex i.succ = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem lastEdge_coordinates (t : I) (p : P) :
    orderNerveRealizationCoordinates P (C.lastEdge t) p =
      (1 - (t : ℝ)) * (if C.vertex (Fin.last (n + 1)) = p then 1 else 0) +
        (t : ℝ) * (if C.vertex 0 = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem vne {i j : Fin (n + 2)} (h : i.val ≠ j.val) : C.vertex i ≠ C.vertex j :=
  fun he => h (congrArg Fin.val (C.vertex.injective he))

theorem edge_injective (i : Fin (n + 1)) : Function.Injective (C.edge i) :=
  orderNerveComparablePath_injective _ (C.vne (by simp))

theorem lastEdge_injective : Function.Injective C.lastEdge :=
  orderNerveComparablePath_injective _ (C.vne (by simp))

theorem edge_meet (i j : Fin (n + 1)) (hij : i < j) (s t : I)
    (h : C.edge i s = C.edge j t) : s = 1 ∧ t = 0 := by
  have hij' : i.val < j.val := hij
  have hi0 := congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex i.castSucc)) h
  have hj1 := congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex j.succ)) h
  have hi : C.vertex i.succ ≠ C.vertex i.castSucc := C.vne (by simp)
  have hji : C.vertex j.castSucc ≠ C.vertex i.castSucc := C.vne (by simpa using ne_of_gt hij')
  have hji' : C.vertex j.succ ≠ C.vertex i.castSucc := C.vne (by dsimp; omega)
  have hij₁ : C.vertex i.castSucc ≠ C.vertex j.succ := C.vne (by dsimp; omega)
  have hij₂ : C.vertex i.succ ≠ C.vertex j.succ := C.vne (by dsimp; omega)
  have hj : C.vertex j.castSucc ≠ C.vertex j.succ := C.vne (by simp)
  simp only [edge_coordinates, ite_true, if_neg hi, if_neg hji, if_neg hji',
    mul_one, mul_zero, add_zero] at hi0
  simp only [edge_coordinates, ite_true, if_neg hij₁, if_neg hij₂, if_neg hj,
    mul_one, mul_zero, zero_add, add_zero] at hj1
  exact ⟨Subtype.ext (show (s : ℝ) = 1 by linarith),
    Subtype.ext (show (t : ℝ) = 0 by linarith)⟩

def «prefix» : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex (Fin.last (n + 1)))) :=
  arcConcat n (orderNerveRealizationVertex ∘ C.vertex) C.edge

theorem prefix_injective : Function.Injective C.prefix :=
  arcConcat_injective n _ _ C.edge_injective C.edge_meet

theorem prefix_meet_last (s t : I) (h : C.prefix s = C.lastEdge t) :
    C.prefix s = orderNerveRealizationVertex (C.vertex 0) ∨
      C.prefix s = orderNerveRealizationVertex (C.vertex (Fin.last (n + 1))) := by
  obtain ⟨i, u, hu⟩ := (arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex)
    C.edge _).mp ⟨s, rfl⟩
  have he := hu.trans h
  by_cases hi : i.val = 0
  · have hc := (C.edge_coordinates i u (C.vertex (Fin.last (n + 1)))).symm.trans
      ((congrArg (fun z => orderNerveRealizationCoordinates P z
        (C.vertex (Fin.last (n + 1)))) he).trans
          (C.lastEdge_coordinates t (C.vertex (Fin.last (n + 1)))))
    have h₀ : C.vertex i.castSucc ≠ C.vertex (Fin.last (n + 1)) := C.vne (by dsimp; omega)
    have h₁ : C.vertex i.succ ≠ C.vertex (Fin.last (n + 1)) := C.vne (by
      have hn := C.positive
      dsimp
      omega)
    have hz : C.vertex 0 ≠ C.vertex (Fin.last (n + 1)) := C.vne (by simp)
    simp only [if_neg h₀, if_neg h₁, if_neg hz,
      ite_true, mul_zero, mul_one, add_zero] at hc
    have ht : t = 1 := Subtype.ext (show (t : ℝ) = 1 by linarith)
    exact Or.inl (h.trans (by rw [ht]; exact C.lastEdge.target))
  · have hc := (C.edge_coordinates i u (C.vertex 0)).symm.trans
      ((congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex 0)) he).trans
        (C.lastEdge_coordinates t (C.vertex 0)))
    have h₀ : C.vertex i.castSucc ≠ C.vertex 0 := C.vne (by simpa using hi)
    have h₁ : C.vertex i.succ ≠ C.vertex 0 := C.vne (by simp)
    have hz : C.vertex (Fin.last (n + 1)) ≠ C.vertex 0 := C.vne (by simp)
    simp only [if_neg h₀, if_neg h₁, if_neg hz,
      ite_true, mul_zero, mul_one, zero_add, add_zero] at hc
    have ht : t = 0 := Subtype.ext (show (t : ℝ) = 0 by linarith)
    exact Or.inr (h.trans (by rw [ht]; exact C.lastEdge.source))

def traversal : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex 0)) := C.prefix.trans C.lastEdge

theorem traversal_fiber (s t : I) (h : C.traversal s = C.traversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
  path_trans_loop_fiber C.prefix C.lastEdge C.prefix_injective C.lastEdge_injective
    C.prefix_meet_last h

include C in
theorem height_ne {a b : P} (hne : a ≠ b) (h : a ≤ b ∨ b ≤ a) :
    C.height a ≠ C.height b := by
  rcases h with h | h
  · exact ne_of_lt (C.height_strict (lt_of_le_of_ne h hne))
  · exact (ne_of_lt (C.height_strict (lt_of_le_of_ne h hne.symm))).symm

include C in
theorem support_pair [Fintype P] (x : orderNerveRealization P) :
    ∃ a b : P, a ≠ b ∧ (a ≤ b ∨ b ≤ a) ∧
      ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0 := by
  let c := orderNerveRealizationCoordinates P x
  have hpositive : ∃ a, 0 < c a := by
    by_contra hn
    push_neg at hn
    have hs : ∑ a, c a ≤ 0 := Finset.sum_nonpos (fun a _ => hn a)
    have he  := orderNerveRealizationCoordinates_sum x
    linarith
  obtain ⟨a, ha⟩ := hpositive
  have hc := orderNerveRealizationCoordinates_support_chain x
  by_cases hb : ∃ b, b ≠ a ∧ 0 < c b
  · obtain ⟨b, hba, hb⟩ := hb
    have hab  := hc ha hb hba.symm
    refine ⟨a, b, hba.symm, hab, ?_⟩
    intro p hpa hpb
    apply le_antisymm _ (orderNerveRealizationCoordinates_nonneg x p)
    by_contra hp
    have hp'  := lt_of_not_ge hp
    have h₁ := C.height_ne hba.symm hab
    have h₂ := C.height_ne hpa (hc hp' ha hpa)
    have h₃ := C.height_ne hpb (hc hp' hb hpb)
    have ha₁ := C.height_le a
    have hb₁ := C.height_le b
    have hp₁ := C.height_le p
    omega
  · have hz : ∀ p, p ≠ a → c p = 0 := by
      intro p hpa
      apply le_antisymm _ (orderNerveRealizationCoordinates_nonneg x p)
      exact le_of_not_gt (fun hp => hb ⟨p, hpa, hp⟩)
    let k := C.vertex.symm a
    by_cases hk : k = Fin.last (n + 1)
    · have he  :=
        (congrArg C.vertex hk).symm.trans (C.vertex.apply_symm_apply a)
      refine ⟨a, C.vertex 0, ?_, ?_, fun p hpa _ => hz p hpa⟩
      · rw [← he]
        exact C.vne (by simp)
      · rw [← he]
        exact C.closing
    · obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hk
      have he  :=
        (congrArg C.vertex hi).trans (C.vertex.apply_symm_apply a)
      refine ⟨a, C.vertex i.succ, ?_, ?_, fun p hpa _ => hz p hpa⟩
      · rw [← he]
        exact C.vne (by simp)
      · rw [← he]
        exact C.consecutive i

theorem traversal_surjective : Function.Surjective C.traversal := by
  letI := Fintype.ofEquiv (Fin (n + 2)) C.vertex
  intro x
  obtain ⟨a, b, hne, hab, hs⟩ := C.support_pair x
  rcases C.edges a b hne hab with ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i)
      (C.vne (by simp)) x hs
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr
      ⟨i, t, ht⟩)
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i)
      (C.vne (by simp)) x (fun p h₀ h₁ => hs p h₁ h₀)
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr
      ⟨i, t, ht⟩)
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support C.closing
      (C.vne (by simp)) x hs
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inr ⟨t, ht⟩
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support C.closing
      (C.vne (by simp)) x (fun p h₀ h₁ => hs p h₁ h₀)
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inr ⟨t, ht⟩

def boundaryHomeomorph : orderNerveRealization P ≃ₜ UnitBoundary (Fin 2 → ℝ) :=
  (simpleLoopBoundaryHomeomorph C.traversal C.traversal_surjective C.traversal_fiber).symm

end FinitePosetCycle
end FiniteChains.Comb
end

namespace FiniteChains.Nerve
universe u
variable {P Q : Type u} [Preorder P]


theorem reflectsBoundsIn_of_retraction {U B : P → Prop}
    (hBU : ∀ p, B p → U p) (ρ : {p : P // U p} → {p : P // U p})
    (hmono : Monotone ρ) (hbase : ∀ p, B (ρ p).1)
    (hfix : ∀ p : {p : P // U p}, B p.1 → ρ p = p) (n : ℕ) :
    ReflectsBoundsIn U B n := by
  classical
  let r  := fun p => if h : U p then (ρ ⟨p, h⟩).1 else p
  have hr p : r p.1 = (ρ p).1 := by simp [r, p.2]
  have hrfix p (hp : B p) : r p = p := by
    have h := hfix ⟨p, hBU p hp⟩ hp
    simp only [r, dif_pos (hBU p hp)]
    exact congrArg Subtype.val h
  intro c hc _ hbound
  obtain ⟨y, hy, hdy⟩ := hbound
  have hryn : cmap r y ∈ IncOn B := by
    obtain ⟨y', hy', rfl⟩ := exists_preimage_of_mem_incOn U hy
    rw [cmap_comp]
    have he : (r ∘ Subtype.val) =
        Subtype.val ∘ ρ := funext hr
    rw [he]
    exact cmap_mem_incOn_of_maps
      (f := Subtype.val ∘ ρ) (fun _ _ h => hmono h) hbase hy'
  refine ⟨cmap r y, hryn, ?_⟩
  rw [← cmap_bdry, hdy]
  simpa only [cmap_id] using (show cmap r c = cmap id c by
    refine AddSubgroup.closure_induction (p := fun z _ => cmap r z = cmap id z)
      ?_ ?_ ?_ ?_ hc
    · rintro z ⟨l, hl, rfl⟩
      rw [cmap_of, cmap_of]
      congr 1
      exact List.map_congr_left (fun p hp => hrfix p (hl.2 p hp))
    · simp
    · simp_all
    · simp)

/-- Pushing a cycle up to the retract changes it by a finite prism boundary. -/
theorem acyclicRelIn_of_upper_retraction {U B : P → Prop} (hne : ∃ p : P, U p)
    (ρ : {p : P // U p} → {p : P // U p}) (hmono : Monotone ρ)
    (hle : ∀ p, p ≤ ρ p) (hbase : ∀ p, B (ρ p).1) : AcyclicRelIn U B := by
  intro c hc hcyc
  obtain ⟨c', hc', rfl⟩ := exists_preimage_of_mem_incOn U hc
  have hcyc' : bdry c' = 0 := by
    apply cmap_val_injective U hne
    rw [cmap_bdry, hcyc, map_zero]
  have hp := bdry_prism_add_prism_bdry id ρ c'
  rw [hcyc', map_zero, add_zero, cmap_id] at hp
  have hpi  :=
    prism_mem_inc monotone_id hmono hle hc'
  refine ⟨cmap Subtype.val (cmap ρ c'), ?_, -cmap Subtype.val (prism id ρ c'),
    AddSubgroup.neg_mem _ (cmap_val_mem_incOn U hpi), ?_, ?_⟩
  · rw [cmap_comp]
    exact cmap_mem_incOn_of_maps
      (f := Subtype.val ∘ ρ) (fun _ _ h => hmono h) hbase hc'
  · rw [← cmap_bdry, ← cmap_bdry, hcyc', map_zero, map_zero]
  · rw [map_neg, ← cmap_bdry, hp, map_sub]
    abel

end FiniteChains.Nerve

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]


/-- The retraction is lifted in each sheet, so the full free-face fiber can be
deleted simultaneously even for an infinite or disconnected covering. -/
theorem cover_freeFace_homology {f : P → Q} (hf : IsPosetCover f)
    {C : Q → Prop} {s t : Q} (ht : C t) (hst : s ≤ t) (hne : t ≠ s)
    (hunique : ∀ x, C x → s ≤ x → x ≠ s → x = t) :
    Nerve.AcyclicRelIn (fun p => C (f p)) (fun p => C (f p) ∧ f p ≠ s) ∧
      ∀ n, Nerve.ReflectsBoundsIn (fun p => C (f p)) (fun p => C (f p) ∧ f p ≠ s) n := by
  obtain ⟨r, hr, hir, hav, hfix⟩ := (show ∃ r : {x : Q // C x} → {x : Q // C x}, Monotone r ∧
      (∀ x, x ≤ r x) ∧ (∀ x, (r x).1 ≠ s) ∧ (∀ x, x.1 ≠ s → r x = x) by
    classical
    let r : {x : Q // C x} → {x : Q // C x} :=
      fun x => if x.1 = s then ⟨t, ht⟩ else x
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · intro x y hxy
      by_cases hx : x.1 = s
      · by_cases hy : y.1 = s
        · simp [r, hx, hy]
        · have hyt  := hunique y.1 y.2 (hx ▸ hxy) hy
          change (r x).1 ≤ (r y).1
          simp only [r, if_pos hx, if_neg hy]
          exact hyt.ge
      · by_cases hy : y.1 = s
        · have hxs : x.1 ≤ s := hy ▸ hxy
          change (r x).1 ≤ (r y).1
          simpa [r, hx, hy] using hxs.trans hst
        · simpa [r, hx, hy] using hxy
    · intro x
      by_cases hx : x.1 = s
      · change x.1 ≤ (r x).1
        simpa [r, hx] using hst
      · simp [r, hx]
    · grind
    · grind)
  let hfc := IsPosetCover.restriction f {x | C x} hf
  let ρ := hfc.upTransform r hir
  have hρ := hfc.upTransform_monotone r hr hir
  have hρge := hfc.le_upTransform r hir
  have hbase : ∀ p, C (f (ρ p).1) ∧ f (ρ p).1 ≠ s := by
    intro p
    refine ⟨(ρ p).2, ?_⟩
    have hp := congrArg Subtype.val (hfc.upTransform_spec r hir p).2
    change f (ρ p).1 = (r ⟨f p.1, p.2⟩).1 at hp
    rw [hp]
    exact hav _
  have hρfix : ∀ p, (C (f p.1) ∧ f p.1 ≠ s) → ρ p = p := by
    intro p hp
    apply hfc.upTransform_fixed r hir p
    exact hfix _ hp.2
  have hnonempty : ∃ p, C (f p) := by
    obtain ⟨p, hp⟩ := hf.surj t
    exact ⟨p, hp.symm ▸ ht⟩
  exact ⟨Nerve.acyclicRelIn_of_upper_retraction hnonempty ρ hρ hρge hbase,
    fun n => Nerve.reflectsBoundsIn_of_retraction (fun _ h => h.1) ρ hρ hbase hρfix n⟩

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- For every recorded pair, including cut-face pairs, deleting all lifts of
its free face preserves homology. No retraction or filling premise is assumed. -/
theorem genus_recorded_free_face_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, truncatedFaceIndex s) :: right)) :
    AcyclicRelIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q left (f p) ∧ f p ≠ s) ∧
      ∀ n, ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
        (fun p => genusCollapseStage q left (f p) ∧ f p ≠ s) n := by
  let pair  := (qCubeToCoordinate t.1, truncatedFaceIndex s)
  have hpair : pair ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hs  := genus_removedFace_dimension q s
    (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
  have ht  := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (truncatedFaceIndex s) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex s) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hcert.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (pair :: right) hsplit
      (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  have hne : (Sum.inl t) ≠ s := by
    intro he
    have hd := congrArg truncatedCellDimension he
    omega
  apply cover_freeFace_homology hf htC (truncatedCell_le_of_inc s t hi) hne
  intro x hx hsx hxs
  have hdim : truncatedCellDimension x = 3 := by
    have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hsx hxs.symm)
    have hmax := genusTruncatedCell_dimension_le_three q x
    omega
  cases x with
  | inr σ =>
      have hmax := genus_cutCell_dimension_le_two q σ
      omega
  | inl d =>
      have hd  := hdim
      have hinc := truncatedCell_inc_of_le s d hsx hs hd
        (genus_simplex_mem_faces q d.1.isSimplex)
      have hm := Finset.mem_inter.mpr ⟨hinc, genusCollapseStage_active_top q left d hx hd⟩
      rw [hcert.2.1] at hm
      have he  := Finset.mem_singleton.mp hm
      exact congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext he)))

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (a : P)


/-- Augmentation commutes with the actual degree-three cellular boundary. -/
theorem hurewicz_uOrdBoundary3 (c : UOrdTet P a →₀ ℤ) :
    hurewicz (orderCx P) a (uOrdBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (fun t : UOrdTet P a => t.1.2) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
      rw [uOrdBoundary3, Finsupp.linearCombination_single, map_smul,
        (show hurewicz (orderCx P) a (uOrdTetBoundary t) = ordTetBoundary t.1.2 by
          have hs (c d) :
              Finsupp.mapDomain (univProj (orderCx P) a).onF (c - d) =
                Finsupp.mapDomain (univProj (orderCx P) a).onF c -
                  Finsupp.mapDomain (univProj (orderCx P) a).onF d :=
            (Finsupp.lmapDomain ℤ ℤ (univProj (orderCx P) a).onF).map_sub c d
          change Finsupp.mapDomain (univProj (orderCx P) a).onF (uOrdTetBoundary t) = _
          simp only [uOrdTetBoundary, hs, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
          rfl), Finsupp.mapDomain_single, ordBoundary3,
        Finsupp.linearCombination_single]

end FiniteChains.Comb
end

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

/-- The actual unique lift of a strict edge from a specified actual source vertex. -/
def strictEdgeLiftFrom (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1) :
    StrictOrdEdge P := by
  let h : f v ≤ e.1.2 := hv.symm ▸ e.2.le
  let q := Classical.choose (hf.up v e.1.2 h)
  have hq : v ≤ q ∧ f q = e.1.2 := (Classical.choose_spec (hf.up v e.1.2 h)).1
  exact ⟨(v, q), lt_of_le_of_ne hq.1 (by
    intro he
    exact e.2.ne (hv.symm.trans ((congrArg f he).trans hq.2)))⟩

theorem strictEdgeLiftFrom_projection (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1) :
    (strictOrderCxMap f hf.strictMono).onE (hf.strictEdgeLiftFrom e v hv) = e := by
  apply Subtype.ext
  apply Prod.ext hv
  exact (Classical.choose_spec (hf.up v e.1.2 (hv.symm ▸ e.2.le))).1.2

theorem strictEdgeLiftFrom_unique (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.1)
    (r : StrictOrdEdge P) (hr : (strictOrderCxMap f hf.strictMono).onE r = e)
    (hs : r.1.1 = v) : r = hf.strictEdgeLiftFrom e v hv := by
  apply Subtype.ext
  apply Prod.ext hs
  have hp := congrArg (fun s : StrictOrdEdge Q => s.1.2)
    (hr.trans (hf.strictEdgeLiftFrom_projection e v hv).symm)
  exact hf.up_inj (hs ▸ r.2.le) (hf.strictEdgeLiftFrom e v hv).2.le hp

/-- The actual unique lift of a strict edge to a specified actual target vertex. -/
def strictEdgeLiftTo (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2) :
    StrictOrdEdge P := by
  let h : e.1.1 ≤ f v := hv.symm ▸ e.2.le
  let q := Classical.choose (hf.down v e.1.1 h)
  have hq : q ≤ v ∧ f q = e.1.1 := (Classical.choose_spec (hf.down v e.1.1 h)).1
  exact ⟨(q, v), lt_of_le_of_ne hq.1 (by
    intro he
    exact e.2.ne (hq.2.symm.trans ((congrArg f he).trans hv)))⟩

theorem strictEdgeLiftTo_projection (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2) :
    (strictOrderCxMap f hf.strictMono).onE (hf.strictEdgeLiftTo e v hv) = e := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Classical.choose_spec (hf.down v e.1.1 (hv.symm ▸ e.2.le))).1.2
  · exact hv

theorem strictEdgeLiftTo_unique (e : StrictOrdEdge Q) (v : P) (hv : f v = e.1.2)
    (r : StrictOrdEdge P) (hr : (strictOrderCxMap f hf.strictMono).onE r = e)
    (ht : r.1.2 = v) : r = hf.strictEdgeLiftTo e v hv := by
  apply Subtype.ext
  apply Prod.ext
  · have hp := congrArg (fun s : StrictOrdEdge Q => s.1.1)
      (hr.trans (hf.strictEdgeLiftTo_projection e v hv).symm)
    exact hf.down_inj (ht ▸ r.2.le) (hf.strictEdgeLiftTo e v hv).2.le hp
  · exact ht

end FiniteChains.Comb.IsPosetCover

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Exactly the two actual lifted incidences enter each actual rose edge-end vertex. -/
theorem roseCover_incoming_edge_cases (q : P) (i : α) (b : Bool) (hq : f q = Rose.edg i b)
    (e : StrictOrdEdge P) (ht : e.1.2 = q) :
    e = hf.strictEdgeLiftTo (roseBaseEdge i b) q hq ∨
      e = hf.strictEdgeLiftTo (roseMidEdge i b) q hq := by
  obtain ⟨k, s, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hp  :=
      (congrArg (fun r : StrictOrdEdge (Rose α) => r.1.2) he).symm.trans
        ((congrArg f ht).trans hq)
    obtain ⟨hk, hs⟩ := Rose.edg.inj hp
    subst k
    subst s
    exact Or.inl (hf.strictEdgeLiftTo_unique (roseBaseEdge i b) q hq e he ht)
  · have hp  :=
      (congrArg (fun r : StrictOrdEdge (Rose α) => r.1.2) he).symm.trans
        ((congrArg f ht).trans hq)
    obtain ⟨hk, hs⟩ := Rose.edg.inj hp
    subst k
    subst s
    exact Or.inr (hf.strictEdgeLiftTo_unique (roseMidEdge i b) q hq e he ht)

/-- Exactly the two actual lifted midpoint incidences leave an actual midpoint vertex. -/
theorem roseCover_mid_outgoing_edge_cases (v : P) (i : α) (hv : f v = Rose.mid i)
    (e : StrictOrdEdge P) (hs : e.1.1 = v) :
    e = hf.strictEdgeLiftFrom (roseMidEdge i false) v hv ∨
      e = hf.strictEdgeLiftFrom (roseMidEdge i true) v hv := by
  obtain ⟨k, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hp  :=
      (congrArg (fun r : StrictOrdEdge (Rose α) => r.1.1) he).symm.trans
        ((congrArg f hs).trans hv)
    cases hp
  · have hp  :=
      (congrArg (fun r : StrictOrdEdge (Rose α) => r.1.1) he).symm.trans
        ((congrArg f hs).trans hv)
    have hk := Rose.mid.inj hp
    subst k
    have hl := hf.strictEdgeLiftFrom_unique (roseMidEdge i b) v hv e he hs
    cases b
    · exact Or.inl hl
    · exact Or.inr hl

include hf in
/-- No actual strict edge enters a lifted rose midpoint. -/
theorem roseCover_mid_no_incoming (v : P) (i : α) (hv : f v = Rose.mid i)
    (e : StrictOrdEdge P) : e.1.2 ≠ v := by
  intro ht
  obtain ⟨k, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he <;>
    have hp := (congrArg (fun r : StrictOrdEdge (Rose α) => r.1.2) he).symm.trans
      ((congrArg f ht).trans hv) <;> cases hp

include hf in
/-- No actual strict edge leaves a lifted rose edge-end. -/
theorem roseCover_end_no_outgoing (q : P) (i : α) (b : Bool)
    (hq : f q = Rose.edg i b) (e : StrictOrdEdge P) : e.1.1 ≠ q := by
  intro hs
  obtain ⟨k, s, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he <;>
    have hp := (congrArg (fun r : StrictOrdEdge (Rose α) => r.1.1) he).symm.trans
      ((congrArg f hs).trans hq) <;> cases hp

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- The midpoint boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_mid (v : P) (i : α) (hv : f v = Rose.mid i)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c v =
      -c (hf.strictEdgeLiftFrom (roseMidEdge i false) v hv) -
        c (hf.strictEdgeLiftFrom (roseMidEdge i true) v hv) := by
  let l := hf.strictEdgeLiftFrom (roseMidEdge i false) v hv
  let r := hf.strictEdgeLiftFrom (roseMidEdge i true) v hv
  have hl : l.1.1 = v := rfl
  have hr : r.1.1 = v := rfl
  have hne : l ≠ r := by
    intro h
    have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
    rw [hf.strictEdgeLiftFrom_projection, hf.strictEdgeLiftFrom_projection] at hp
    have hb := congrArg (fun e : StrictOrdEdge (Rose α) => e.1.2) hp
    cases hb
  change FiniteChains.Comb.bdry1 (strictOrderCx P) c v = -c l - c r
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    rw [bdry1_single]
    have ht := roseCover_mid_no_incoming f hf v i hv e
    by_cases he : e = l
    · subst e
      simp [strictOrderCx, ht, hl, hne.symm]
    · by_cases her : e = r
      · subst e
        simp [strictOrderCx, ht, hr, hne]
      · have hs : e.1.1 ≠ v := by
          intro h
          exact (roseCover_mid_outgoing_edge_cases f hf v i hv e h).elim he her
        simp [strictOrderCx, ht, hs, he, her]

/-- The edge-end boundary equation for the actual finite chain complex of a rose cover. -/
theorem roseCover_boundary_end (q : P) (i : α) (b : Bool) (hq : f q = Rose.edg i b)
    (c : StrictOrdEdge P →₀ ℤ) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) c q =
      c (hf.strictEdgeLiftTo (roseBaseEdge i b) q hq) +
        c (hf.strictEdgeLiftTo (roseMidEdge i b) q hq) := by
  let l := hf.strictEdgeLiftTo (roseBaseEdge i b) q hq
  let r := hf.strictEdgeLiftTo (roseMidEdge i b) q hq
  have hl : l.1.2 = q := rfl
  have hr : r.1.2 = q := rfl
  have hne : l ≠ r := by
    intro h
    have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) h
    rw [hf.strictEdgeLiftTo_projection, hf.strictEdgeLiftTo_projection] at hp
    have hb := congrArg (fun e : StrictOrdEdge (Rose α) => e.1.1) hp
    cases hb
  change FiniteChains.Comb.bdry1 (strictOrderCx P) c q = c l + c r
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    rw [bdry1_single]
    have hs := roseCover_end_no_outgoing f hf q i b hq e
    by_cases he : e = l
    · subst e
      simp [strictOrderCx, hs, hl, hne.symm]
    · by_cases her : e = r
      · subst e
        simp [strictOrderCx, hs, hr, hne]
      · have ht : e.1.2 ≠ q := by
          intro h
          exact (roseCover_incoming_edge_cases f hf q i b hq e h).elim he her
        simp [strictOrderCx, ht, hs, he, her]

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual incidence edges over the positive selected half of each rose generator. -/
def roseCoverGeneratorEdges : Set (StrictOrdEdge P) :=
  {e | ∃ i, (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true}

/-- Restrict the actual finite chain to its selected generator incidences. -/
def roseCoverGeneratorCoordinates :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (roseCoverGeneratorEdges f hf →₀ ℤ) :=
  Finsupp.lsubtypeDomain (roseCoverGeneratorEdges f hf)

@[simp] theorem roseCoverGeneratorCoordinates_apply (c : StrictOrdEdge P →₀ ℤ)
    (e : roseCoverGeneratorEdges f hf) : roseCoverGeneratorCoordinates f hf c e = c e.val := rfl

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Actual lifted midpoint vertices, with their actual generator label. -/
def roseCoverMidpoints := {p : P × α // f p.1 = Rose.mid p.2}

/-- The actual positive selected incidence leaving a lifted midpoint. -/
def roseCoverMidpointEdge (p : roseCoverMidpoints f) :
    roseCoverGeneratorEdges f hf :=
  ⟨hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property,
    p.val.2, hf.strictEdgeLiftFrom_projection _ _ _⟩



/-- A proved equivalence between actual midpoint vertices and selected actual incidence edges. -/
def roseCoverMidpointEdgeEquiv :
    roseCoverMidpoints f ≃ roseCoverGeneratorEdges f hf :=
  Equiv.ofBijective (roseCoverMidpointEdge f hf)
    ⟨(by
      intro p q h
      have he := congrArg Subtype.val h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun e : StrictOrdEdge P => e.val.1) he
      · have hp := congrArg ((strictOrderCxMap f hf.strictMono).onE) he
        change (strictOrderCxMap f hf.strictMono).onE
          (hf.strictEdgeLiftFrom (roseMidEdge p.val.2 true) p.val.1 p.property) =
          (strictOrderCxMap f hf.strictMono).onE
            (hf.strictEdgeLiftFrom (roseMidEdge q.val.2 true) q.val.1 q.property) at hp
        rw [hf.strictEdgeLiftFrom_projection, hf.strictEdgeLiftFrom_projection] at hp
        exact Rose.mid.inj (congrArg (fun e : StrictOrdEdge (Rose α) => e.val.1) hp)), (by
      rintro ⟨e, i, he⟩
      have hv  :=
        congrArg (fun r : StrictOrdEdge (Rose α) => r.val.1) he
      refine ⟨⟨(e.val.1, i), hv⟩, ?_⟩
      apply Subtype.ext
      exact (hf.strictEdgeLiftFrom_unique (roseMidEdge i true) e.val.1 hv e he rfl).symm)⟩

end FiniteChains.PresModel
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {A D P K Z : Type u}
variable [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]
variable [TopologicalSpace K] [TopologicalSpace Z]

def attachmentBaseMap (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) : C(Space a i, Space (e ∘ a) i) :=
  desc a i ((⟨old (e ∘ a) i, old_continuous (e ∘ a) i⟩ : C(K, Space (e ∘ a) i)).comp e)
    ⟨cell (e ∘ a) i, cell_continuous (e ∘ a) i⟩
    (fun b => (cell_boundary (e ∘ a) i hi b).symm)

omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_old (a : A → P) (i : A → D)
    (hi : Function.Injective i) (e : C(P, K)) (p : P) :
    attachmentBaseMap a i hi e (old a i p) = old (e ∘ a) i (e p) := rfl

omit [TopologicalSpace A] in
@[simp] theorem attachmentBaseMap_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (e : C(P, K)) (d : D) :
    attachmentBaseMap a i hi e (cell a i d) = cell (e ∘ a) i d := by
  unfold attachmentBaseMap
  rw [desc_cell]
  rfl

omit [TopologicalSpace A] in
theorem attachmentBaseMap_comp {Q : Type u} [TopologicalSpace Q]
    (a : A → P) (i : A → D) (hi : Function.Injective i)
    (e : C(P, K)) (g : C(K, Q)) :
    (attachmentBaseMap (e ∘ a) i hi g).comp (attachmentBaseMap a i hi e) =
      attachmentBaseMap a i hi (g.comp e) := by
  apply hom_ext a i
  · intro p
    rfl
  · intro d
    simp
    exact (attachmentBaseMap_cell a i hi (g.comp e) d).symm

/-- A jointly continuous pasting on the attachment. The target is curried
in the compact time coordinate, so the base need not be locally compact. -/
def attachmentHomotopyPasting (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) : C(I × Space a i, Z) :=
  (desc a i ((H.comp ⟨Prod.swap, continuous_swap⟩).curry)
    ((G.comp ⟨Prod.swap, continuous_swap⟩).curry)
    (fun b => ContinuousMap.ext (fun t => h t b))).uncurry.comp
      ⟨Prod.swap, continuous_swap⟩

omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_old (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (p : P) :
    attachmentHomotopyPasting a i H G h (t, old a i p) = H (t, p) := rfl

omit [TopologicalSpace A] in
@[simp] theorem attachmentHomotopyPasting_cell (a : A → P) (i : A → D)
    (H : C(I × P, Z)) (G : C(I × D, Z))
    (h : ∀ t b, H (t, a b) = G (t, i b)) (t : I) (d : D) :
    attachmentHomotopyPasting a i H G h (t, cell a i d) = G (t, d) := by simp_all [attachmentHomotopyPasting, ContinuousMap.comp_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry, Prod.swap]

end FiniteChains.RelativeAttachment
end

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

theorem finOne_norm (x : Fin 1 → ℝ) : ‖x‖ = |x 0| := by
  have hx  := funext fun i => congrArg x (Subsingleton.elim i 0)
  calc
    ‖x‖ = ‖fun _ => x 0‖ := congrArg norm hx
    _ = |x 0| := by rw [pi_norm_const, Real.norm_eq_abs]

def graphBoundaryNeg : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => -1, by simp [pi_norm_const]⟩

def graphBoundaryPos : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => 1, by simp [pi_norm_const]⟩

theorem graphBoundary_cases (a : UnitBoundary (Fin 1 → ℝ)) :
    a = graphBoundaryNeg ∨ a = graphBoundaryPos := by
  have ha  := (finOne_norm a.val).symm.trans a.property
  by_cases h : 0 ≤ a.val 0
  · right
    apply Subtype.ext
    funext i
    rw [show i = 0 from Subsingleton.elim _ _]
    simpa [graphBoundaryNeg, graphBoundaryPos,abs_of_nonneg h] using ha
  · left
    have hn : a.val 0 = -1 := by
      rw [abs_of_neg (lt_of_not_ge h)] at ha
      linarith
    apply Subtype.ext
    funext i
    rw [show i = 0 from Subsingleton.elim _ _]
    exact hn

def graphDiskHomeomorph : I ≃ₜ ClosedUnitBall (Fin 1 → ℝ) where
  toFun s := ⟨fun _ => 2 * (s : ℝ) - 1, by
    rw [pi_norm_const, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [s.property.1], by linarith [s.property.2]⟩⟩
  invFun d := ⟨(d.val 0 + 1) / 2, by
    have hd : |d.val 0| ≤ 1 := by simpa only [finOne_norm] using d.property
    obtain ⟨hl, hu⟩ := abs_le.mp hd
    constructor <;> linarith⟩
  left_inv s := by simp
  right_inv d := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2

@[simp] theorem graphDiskHomeomorph_zero :
    graphDiskHomeomorph 0 = unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryNeg := by
  apply Subtype.ext
  funext i
  norm_num [graphDiskHomeomorph, graphBoundaryNeg, unitBoundaryInclusion]

@[simp] theorem graphDiskHomeomorph_one :
    graphDiskHomeomorph 1 = unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryPos := by
  apply Subtype.ext
  funext i
  norm_num [graphDiskHomeomorph, graphBoundaryPos, unitBoundaryInclusion]

@[simp] theorem graphDiskHomeomorph_symm_neg :
    graphDiskHomeomorph.symm (unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryNeg) = 0 := by
  rw [← graphDiskHomeomorph_zero, graphDiskHomeomorph.symm_apply_apply]

@[simp] theorem graphDiskHomeomorph_symm_pos :
    graphDiskHomeomorph.symm (unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryPos) = 1 := by
  rw [← graphDiskHomeomorph_one, graphDiskHomeomorph.symm_apply_apply]

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphSrc (j : J) : V := r ⟨j, graphBoundaryNeg⟩
def graphTgt (j : J) : V := r ⟨j, graphBoundaryPos⟩

def graphCx : Comb.Complex2 where
  V := V
  E := J
  F := Empty
  src := graphSrc r
  tgt := graphTgt r
  base := Empty.elim
  att := Empty.elim
  att_isLoop f := Empty.elim f

def graphEdgePath (j : J) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphSrc r j))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphTgt r j)) where
  toFun s := cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ⟨j, graphDiskHomeomorph s⟩
  continuous_toFun := (cell_continuous r _).comp
    (continuous_sigmaMk.comp graphDiskHomeomorph.continuous)
  source' := by
    rw [graphDiskHomeomorph_zero]
    exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
      ⟨j, graphBoundaryNeg⟩
  target' := by
    rw [graphDiskHomeomorph_one]
    exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
      ⟨j, graphBoundaryPos⟩

def graphGermPath (g : J × Bool) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      (Comb.germSrc (graphSrc r) (graphTgt r) g))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
        (Comb.germTgt (graphSrc r) (graphTgt r) g)) := by
  rcases g with ⟨j, b⟩
  cases b
  · exact (graphEdgePath r j).symm
  · exact graphEdgePath r j

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

theorem generatesDegreeIn_trans {U B C : P → Prop} {n : ℕ}
    (hBU : ∀ p, B p → U p) (hUB : GeneratesDegreeIn U B (n + 1))
    (hBC : GeneratesDegreeIn B C (n + 1)) : GeneratesDegreeIn U C (n + 1) := by
  intro z hz hd hcyc
  obtain ⟨c, hc, y, hy, hdc, he⟩ := hUB z hz hd hcyc
  let c' := lengthProjection (n + 1) c
  let y' := lengthProjection (n + 2) y
  have hc' : c' ∈ IncOn B := lengthProjection_mem_incOn _ hc
  have hdc' : bdry c' = 0 := by
    rw [← lengthProjection_bdry, hdc, map_zero]
  have he' : z = c' + bdry y' := by
    rw [← hd, he, map_add, lengthProjection_bdry]
  obtain ⟨d, hdC, w, hw, hdd, hec⟩ :=
    hBC c' hc' (lengthProjection_idempotent _ _) hdc'
  refine ⟨d, hdC, y' + w, AddSubgroup.add_mem _ (lengthProjection_mem_incOn _ hy)
    (incOn_mono hBU hw), hdd, ?_⟩
  rw [he', hec, map_add]
  abel

end FiniteChains.Nerve

namespace FiniteChains.Nerve
universe u
variable {P : Type u} [PartialOrder P]
  {C T : P → Prop} (hTC : ∀ p, T p → C p)
  (hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p)
  {n : ℕ}
  (hlink₁ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) n)
  (hlink₂ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) (n + 1))

include hTC hmax hlink₁ hlink₂ in
theorem maximalFamily_finite (S : Finset P) (hS : ∀ v ∈ S, T v) :
    GeneratesDegreeIn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S)
      (fun p => C p ∧ ¬ T p) (n + 1) ∧
    ReflectsBoundsIn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S)
      (fun p => C p ∧ ¬ T p) (n + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · intro c hc _ hd
        have hb : c ∈ IncOn (fun p => C p ∧ ¬ T p) := by simpa using hc
        exact ⟨c, hb, 0, AddSubgroup.zero_mem _, hd, by simp⟩
      · intro c _ _ hb
        simpa using hb
  | @insert v S hvS ih =>
      have hvT  := hS v (Finset.mem_insert_self _ _)
      have hvC  := hTC v hvT
      have hS'  := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have hprev := ih hS'
      let Prev := fun p => (C p ∧ ¬ T p) ∨ p ∈ S
      let U := fun p => (C p ∧ ¬ T p) ∨ p ∈ insert v S
      let D := fun p => C p ∧ p ≤ v
      have hUC p (hp : U p) : C p := by
        rcases hp with hp | hp
        · simp_all
        · grind
      have hprev_of_ne p (hp : U p) (hne : p ≠ v) : Prev p := by
        rcases hp with hp | hp
        · grind
        · grind
      have hbelow p (hpC : C p) (hpv : p < v) : ¬ T p := by
        intro hpT
        exact hpv.ne (hmax p hpT v hvC hpv.le).symm
      have hinter (p : P) : (Prev p ∧ D p) ↔ C p ∧ p < v := by
        constructor
        · rintro ⟨hp, hpC, hpv⟩
          refine ⟨hpC, lt_of_le_of_ne hpv ?_⟩
          intro he
          subst p
          exact hp.elim (fun h => h.2 hvT) hvS
        · grind
      have hunion (p : P) : U p ↔ Prev p ∨ D p := by
        constructor
        · grind
        · grind
      have hmix : ∀ p r : P, p ≤ r → U p → U r →
          (Prev p ∧ Prev r) ∨ (D p ∧ D r) := by
        intro p r hpr hp hr
        by_cases he : r = v
        · grind
        · grind
      have hcone : AcyclicIn D := by
        let b : {p : P // D p} := ⟨v, hvC, le_refl _⟩
        apply acyclicIn_of_subtype D ⟨v, hvC, le_refl _⟩
        intro c hc hd
        exact exists_bdry_eq_of_cycle id b monotone_id (fun _ => le_refl _)
          (fun p => p.2.2) hc hd
      constructor
      · exact generatesDegreeIn_union_of_unmixed hunion hmix hprev.1
          (generatesDegreeIn_of_acyclicRelIn (acyclicRelIn_of_acyclicIn hcone))
          (fillsDegreeIn_congr (fun p => (hinter p).symm) (hlink₁ v hvT))
      · exact reflectsBoundsIn_trans (fun _ hp => Or.inl hp)
          (reflectsBoundsIn_union_of_unmixed hmix
            (fillsDegreeIn_congr (fun p => (hinter p).symm) (hlink₂ v hvT))) hprev.2

theorem exists_finite_maximal_support (c : Ch P) (hc : c ∈ IncOn C) :
    ∃ S : Finset P, (∀ v ∈ S, T v) ∧ c ∈ IncOn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S) := by
  classical
  let S := (c.support.biUnion (fun l => l.toFinset)).filter T
  refine ⟨S, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  rw [mem_incOn_iff]
  intro l hl
  obtain ⟨hchain, hsupp⟩ := (mem_incOn_iff c).mp hc l hl
  refine ⟨hchain, ?_⟩
  intro p hp
  by_cases hpT : T p
  · exact Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨l, hl, List.mem_toFinset.mpr hp⟩, hpT⟩)
  · simp_all

include hTC hmax hlink₁ hlink₂ in
/-- Both homology comparisons hold for the whole maximal family. The family,
ambient complex, and cover are not required to be finite. -/
theorem maximalFamily_homology :
    GeneratesDegreeIn C (fun p => C p ∧ ¬ T p) (n + 1) ∧
      ReflectsBoundsIn C (fun p => C p ∧ ¬ T p) (n + 1) := by
  constructor
  · intro c hc hd hcyc
    obtain ⟨S, hS, hcS⟩ := exists_finite_maximal_support c hc
    obtain ⟨d, hdB, y, hy, hdd, he⟩ :=
      (maximalFamily_finite hTC hmax hlink₁ hlink₂ S hS).1 c hcS hd hcyc
    refine ⟨d, hdB, y, incOn_mono ?_ hy, hdd, he⟩
    intro p hp
    exact hp.elim (fun h => h.1) (fun h => hTC p (hS p h))
  · intro c hc hd hbound
    obtain ⟨y, hy, hdy⟩ := hbound
    obtain ⟨S, hS, hyS⟩ := exists_finite_maximal_support y hy
    exact (maximalFamily_finite hTC hmax hlink₁ hlink₂ S hS).2 c hc hd ⟨y, hyS, hdy⟩

end FiniteChains.Nerve

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- Actual cellular normalization and an actual monotone endomorphism commute
with the genuine two-to-one boundary. -/
theorem bdry2_normalizedStrictChain2 (g : P → P) (hg : Monotone g)
    (c : StrictOrdTri P →₀ ℤ) :
    bdry2 (strictOrderCx P) (normalizedStrictChain2 g hg c) =
      normalizedStrictChain1 g hg (bdry2 (strictOrderCx P) c) := by
  change bdry2 (strictOrderCx P)
    (normalizeOrdChain2 (chain2 (orderCxMap g hg) (chain2 (strictOrderIncl P) c))) =
    normalizeOrdChain1 (chain1 (orderCxMap g hg)
      (chain1 (strictOrderIncl P) (bdry2 (strictOrderCx P) c)))
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, bdry2_chain2]

end FiniteChains.Comb
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

def cylinderCoverRoseSet : Set P := {p | ∃ x : Rose α, f p = cylIn (aHom w) x}

theorem cylinderCoverCollapse_mem_rose (p : P) :
    cylinderCoverCollapse w hf p ∈ cylinderCoverRoseSet w f :=
  ⟨cylRetr (aHom w) (f p), cylinderCoverCollapse_projection w hf p⟩

/-- Every surviving genuine edge of a collapsed finite chain lies in the actual rose preimage. -/
theorem cylinderCoverCollapsedChain_support_rose (c : StrictOrdEdge P →₀ ℤ) :
    ∀ e ∈ (normalizedStrictChain1 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c).support,
      e.1.1 ∈ cylinderCoverRoseSet w f ∧ e.1.2 ∈ cylinderCoverRoseSet w f := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    intro e he
    rw [map_add] at he
    rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
    · simp_all
    · simp_all
  | single t n =>
    intro e he
    rw [normalizedStrictChain1_single] at he
    by_cases h : cylinderCoverCollapse w hf t.1.1 = cylinderCoverCollapse w hf t.1.2
    · simp [normalizeOrdEdge, h] at he
    · simp only [normalizeOrdEdge, dif_neg h] at he
      let r : StrictOrdEdge P := ⟨(cylinderCoverCollapse w hf t.1.1,
        cylinderCoverCollapse w hf t.1.2),
        lt_of_le_of_ne (cylinderCoverCollapse_monotone w hf t.2.le) h⟩
      have hr : e = r := by
        by_contra hn
        have hz : (n • Finsupp.single r (1 : ℤ)) e = 0 := by simp [Ne.symm hn]
        exact (Finsupp.mem_support_iff.mp he) hz
      subst e
      exact ⟨cylinderCoverCollapse_mem_rose w f hf t.1.1,
        cylinderCoverCollapse_mem_rose w f hf t.1.2⟩

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

def cylinderRoseSet : Set (CylBase w) := {p | ∃ x : Rose α, p = cylIn (aHom w) x}

def cylinderRoseInclusion (x : Rose α) : cylinderRoseSet w :=
  ⟨cylIn (aHom w) x, x, rfl⟩



/-- The actual inner end of the cylinder is order isomorphic to the actual rose. -/
def cylinderRoseOrderIso : Rose α ≃o cylinderRoseSet w where
  toEquiv := Equiv.ofBijective (cylinderRoseInclusion w)
    ⟨(by
      intro x y h
      exact Sum.inl.inj (congrArg Subtype.val h)), (by
      rintro ⟨p, x, hx⟩
      exact ⟨x, Subtype.ext hx.symm⟩)⟩
  map_rel_iff' := by intro x y; rfl

variable {P : Type u} [PartialOrder P] (f : P → CylBase w)

/-- The actual projection from the actual rose preimage to the actual rose. -/
def cylinderCoverRoseEnd (p : cylinderCoverRoseSet w f) : Rose α :=
  (cylinderRoseOrderIso w).symm ⟨f p.val, p.property⟩

theorem cylinderCoverRoseEnd_isPosetCover (hf : IsPosetCover f) :
    IsPosetCover (cylinderCoverRoseEnd w f) :=
  (hf.restriction f (cylinderRoseSet w)).postcompose_orderIso (cylinderRoseOrderIso w).symm

omit [PartialOrder P] in
theorem cylinderCoverRoseEnd_projection (p : cylinderCoverRoseSet w f) :
    cylIn (aHom w) (cylinderCoverRoseEnd w f p) = f p.val := congrArg Subtype.val ((cylinderRoseOrderIso w).apply_symm_apply ⟨f p.val, p.property⟩)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w)

/-- The actual rose-preimage fibre is exactly the corresponding presentation-cover fibre. -/
def presCoverRoseFibreEquiv (x : Rose α) :
    {p : cylinderCoverRoseSet w (coneAdjCoverBaseEnd f) //
      cylinderCoverRoseEnd w (coneAdjCoverBaseEnd f) p = x} ≃
    {p : P // f p = iRose w x} where
  toFun p := ⟨p.val.val.val, by
    have h := cylinderCoverRoseEnd_projection w (coneAdjCoverBaseEnd f) p.val
    rw [p.property] at h
    exact (coneAdjCoverBaseEnd_spec f p.val.val).symm.trans (congrArg ConeAdj.inc h.symm)⟩
  invFun p := by
    let b : {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
      ⟨p.val, cylIn (aHom w) x, p.property.symm⟩
    have hb : coneAdjCoverBaseEnd f b = cylIn (aHom w) x :=
      Sum.inl.inj ((coneAdjCoverBaseEnd_spec f b).trans p.property)
    let q : cylinderCoverRoseSet w (coneAdjCoverBaseEnd f) := ⟨b, x, hb⟩
    refine ⟨q, ?_⟩
    exact cylIn_injective (aHom w)
      ((cylinderCoverRoseEnd_projection w (coneAdjCoverBaseEnd f) q).trans hb)
  left_inv p := rfl
  right_inv p := rfl

end FiniteChains.PresModel

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
theorem strictOrderCxMap_onF_injective (k : P → Q) (hm : StrictMono k)
    (hi : Function.Injective k) : Function.Injective (strictOrderCxMap k hm).onF := by
  intro t s he
  apply Subtype.ext
  apply Prod.ext
  · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.1) he)
  · apply Prod.ext
    · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.2.1) he)
    · exact hi (congrArg (fun r : StrictOrdTri Q => r.1.2.2) he)
end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (w : J → List (α × Bool)) (f : P → PresPos w) (hf : IsPosetCover f)
  (hpos : ∀ j, 0 < (w j).length)

/-- The distinguished coordinate triangle is the unique triangle over its actual
first incidence with its actual apex. -/
theorem presCoverRelatorTriangle_unique (p : PresCoverRelator w f) (t : StrictOrdTri P)
    (ht : (strictOrderCxMap f hf.strictMono).onF t = presRelatorFirstTriangle w hpos p.1.2)
    (hv : t.1.2.2 = p.1.1) : t = presCoverRelatorTriangle w f hf hpos p := by
  let r := presCoverRelatorTriangle w f hf hpos p
  have he  :=
    ht.trans (presCoverRelatorTriangle_projection w f hf hpos p).symm
  have hfa := congrArg (fun s : StrictOrdTri (PresPos w) => s.1.1) he
  have hfb := congrArg (fun s : StrictOrdTri (PresPos w) => s.1.2.1) he
  have ha  := hf.down_inj (a := p.1.1)
    (hv ▸ (t.2.1.le.trans t.2.2.le)) (r.2.1.le.trans r.2.2.le) hfa
  have hb  := hf.down_inj (a := p.1.1) (hv ▸ t.2.2.le) r.2.2.le hfb
  exact Subtype.ext (Prod.ext ha (Prod.ext hb hv))

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

include hpos

/-- The actual path-class cover projection of the nonempty-word presentation model. -/
theorem presUniversalEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := PresPos w) (a := ptBase w)) := by
  apply uOrderEnd_isPosetCover
  apply presPos_isConnected w
  grind

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Reading coordinates on an actual universal rose-cover midpoint fibre. -/
def presUniversalRoseMidpointFibreEquiv (i : α) :
    {p : cylinderCoverRoseSet w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))) //
      cylinderCoverRoseEnd w (coneAdjCoverBaseEnd uOrderEnd) p = Rose.mid i} ≃ PresGroup ρ :=
  (presCoverRoseFibreEquiv w uOrderEnd (Rose.mid i)).trans
    (presUniversalFibreGroupEquiv ρ w hw hpos (iRose w (Rose.mid i)))

/-- Actual universal lifted midpoints are indexed by their reading and generator label. -/
def presUniversalMidpointGroupEquiv :
    roseCoverMidpoints (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w)))) ≃ PresGroup ρ × α where
  toFun p := (presUniversalRoseMidpointFibreEquiv ρ w hw hpos p.val.2
    ⟨p.val.1, p.property⟩, p.val.2)
  invFun q :=
    let p := (presUniversalRoseMidpointFibreEquiv ρ w hw hpos q.2).symm q.1
    ⟨(p.val, q.2), p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · rfl
  right_inv q := by grind

/-- Selected actual universal rose edges have the same genuine group-generator coordinates. -/
def presUniversalGeneratorGroupEquiv :
    roseCoverGeneratorEdges (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))
      (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) ≃
      PresGroup ρ × α :=
  (roseCoverMidpointEdgeEquiv _
    (cylinderCoverRoseEnd_isPosetCover w _
      (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))).symm.trans
    (presUniversalMidpointGroupEquiv ρ w hw hpos)

/-- Finite selected-edge coefficients in actual group-generator coordinates. -/
def presUniversalGeneratorGroupChainEquiv :
    (roseCoverGeneratorEdges (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))
      (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) →₀ ℤ) ≃ₗ[ℤ]
      (PresGroup ρ × α →₀ ℤ) :=
  Finsupp.domLCongr (R := ℤ) (M := ℤ) (presUniversalGeneratorGroupEquiv ρ w hw hpos)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual lifted relators are indexed by their apex reading and actual relator label. -/
def presUniversalRelatorGroupEquiv :
    PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) ≃ PresGroup ρ × J where
  toFun p := ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1, p.val.2)
  invFun q :=
    let p := (presUniversalFibreGroupEquiv ρ w hw hpos (apexOf w q.2)).symm q.1
    ⟨(p.val, q.2), p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((presUniversalFibreGroupEquiv ρ w hw hpos (apexOf w p.val.2)).symm_apply_apply
          ⟨p.val.1, p.property⟩)
    · rfl
  right_inv q := by
    apply Prod.ext
    · exact (presUniversalFibreGroupEquiv ρ w hw hpos (apexOf w q.2)).apply_symm_apply q.1
    · rfl

/-- Finite actual relator coefficients expressed in actual presentation-group coordinates. -/
def presUniversalRelatorGroupChainEquiv :
    (PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) ≃ₗ[ℤ]
      (PresGroup ρ × J →₀ ℤ) :=
  Finsupp.domLCongr (R := ℤ) (M := ℤ) (presUniversalRelatorGroupEquiv ρ w hw hpos)

end FiniteChains.PresModel

namespace Path
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X] {a b z : X}

/-- Time runs vertically. At time zero the square is `p`; at time one it
is constant at `z`. Its left side is `q`, and its right side is `p.symm.trans q`. -/
def tailContraction (p : Path a b) (q : Path a z) : C(I × I, X) where
  toFun ts := (p.symm.trans q).extend
    ((1 - (ts.2 : ℝ) + (1 + (ts.2 : ℝ)) * (ts.1 : ℝ)) / 2)
  continuous_toFun := (p.symm.trans q).continuous_extend.comp (by fun_prop)

@[simp] theorem tailContraction_zero (p : Path a b) (q : Path a z) (s : I) :
    tailContraction p q (0, s) = p s := by
  change (p.symm.trans q).extend ((1 - s + (1 + s) * 0) / 2) = p s
  grind

@[simp] theorem tailContraction_one (p : Path a b) (q : Path a z) (s : I) :
    tailContraction p q (1, s) = z := by simp_all [tailContraction]

@[simp] theorem tailContraction_left (p : Path a b) (q : Path a z) (t : I) :
    tailContraction p q (t, 0) = q t := by
  change (p.symm.trans q).extend ((1 - 0 + (1 + 0) * t) / 2) = q t
  rw [Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  grind

@[simp] theorem tailContraction_right (p : Path a b) (q : Path a z) (t : I) :
    tailContraction p q (t, 1) = (p.symm.trans q) t := by
  change (p.symm.trans q).extend ((1 - 1 + (1 + 1) * t) / 2) = _
  grind

end Path

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (root : V)


variable (Q : ∀ a : V, Path ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) a) ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root))
  (hQ : ∀ j : J,
    Q (graphSrc r j) = (graphEdgePath r j).trans (Q (graphTgt r j)) ∨
    Q (graphTgt r j) = (graphEdgePath r j).symm.trans (Q (graphSrc r j)))

include hQ in
theorem graphEdgeContraction_exists (j : J) : ∃ H : C(I × I, (DiskAttachment r)),
    (∀ s, H (0, s) = graphEdgePath r j s) ∧
    (∀ s, H (1, s) = (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root) ∧
    (∀ t, H (t, 0) = Q (graphSrc r j) t) ∧
    (∀ t, H (t, 1) = Q (graphTgt r j) t) := by
  rcases hQ j with hj | hj
  · let H := (Path.tailContraction (graphEdgePath r j).symm (Q (graphTgt r j))).comp
      ⟨fun ts : I × I => (ts.1, unitInterval.symm ts.2),
        continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd)⟩
    refine ⟨H, ?_, ?_, ?_, ?_⟩
    · intro s
      change Path.tailContraction _ _ (0, unitInterval.symm s) = _
      simp
    · intro s
      exact Path.tailContraction_one _ _ _
    · intro t
      change Path.tailContraction _ _ (t, unitInterval.symm 0) = _
      rw [unitInterval.symm_zero, Path.tailContraction_right, Path.symm_symm, ← hj]
    · intro t
      change Path.tailContraction _ _ (t, unitInterval.symm 1) = _
      rw [unitInterval.symm_one, Path.tailContraction_left]
  · refine ⟨Path.tailContraction (graphEdgePath r j) (Q (graphSrc r j)),
      Path.tailContraction_zero _ _, Path.tailContraction_one _ _,
      Path.tailContraction_left _ _, ?_⟩
    intro t
    rw [Path.tailContraction_right, ← hj]

def graphEdgeContraction (j : J) : C(I × I, (DiskAttachment r)) :=
  Classical.choose (graphEdgeContraction_exists r root Q hQ j)

theorem graphEdgeContraction_spec (j : J) :
    (∀ s, graphEdgeContraction r root Q hQ j (0, s) = graphEdgePath r j s) ∧
    (∀ s, graphEdgeContraction r root Q hQ j (1, s) = (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root) ∧
    (∀ t, graphEdgeContraction r root Q hQ j (t, 0) = Q (graphSrc r j) t) ∧
    (∀ t, graphEdgeContraction r root Q hQ j (t, 1) = Q (graphTgt r j) t) :=
  Classical.choose_spec (graphEdgeContraction_exists r root Q hQ j)

variable [DiscreteTopology V]

def graphVertexContraction : C(I × V, (DiskAttachment r)) :=
  (⟨fun a => (Q a).toContinuousMap, continuous_of_discreteTopology⟩ : C(V, C(I, (DiskAttachment r)))).uncurry.comp
    ⟨Prod.swap, continuous_swap⟩

def graphDiskContraction (j : J) : C(I × ClosedUnitBall (Fin 1 → ℝ), (DiskAttachment r)) :=
  (graphEdgeContraction r root Q hQ j).comp
    ⟨fun td => (td.1, graphDiskHomeomorph.symm td.2),
      continuous_fst.prodMk (graphDiskHomeomorph.symm.continuous.comp continuous_snd)⟩

def graphDiskFamilyContraction : C(I × DiskFamily J (Fin 1 → ℝ), (DiskAttachment r)) :=
  let F : C(DiskFamily J (Fin 1 → ℝ), C(I, (DiskAttachment r))) := {
    toFun := fun d => ((graphDiskContraction r root Q hQ d.1).comp
      ⟨Prod.swap, continuous_swap⟩).curry d.2
    continuous_toFun := continuous_sigma (fun j =>
      ((graphDiskContraction r root Q hQ j).comp ⟨Prod.swap, continuous_swap⟩).curry.continuous) }
  F.uncurry.comp ⟨Prod.swap, continuous_swap⟩

theorem graphContraction_compatible (t : I) (a : BoundaryFamily J (Fin 1 → ℝ)) :
    graphVertexContraction r root Q (t, r a) =
      graphDiskFamilyContraction r root Q hQ (t, boundaryFamilyInclusion J _ a) := by
  rcases a with ⟨j, a⟩
  rcases graphBoundary_cases a with rfl | rfl
  · change Q (graphSrc r j) t =
      graphEdgeContraction r root Q hQ j
        (t, graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryNeg))
    rw [graphDiskHomeomorph_symm_neg]
    exact ((graphEdgeContraction_spec r root Q hQ j).2.2.1 t).symm
  · change Q (graphTgt r j) t =
      graphEdgeContraction r root Q hQ j
        (t, graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryPos))
    rw [graphDiskHomeomorph_symm_pos]
    exact ((graphEdgeContraction_spec r root Q hQ j).2.2.2 t).symm

/-- Compatible vertex paths and edge recursions contract the actual quotient
topology of the graph. Neither the vertex set nor the edge set is finite. -/
def graphContraction : ContinuousMap.Homotopy (ContinuousMap.id (DiskAttachment r))
    (ContinuousMap.const (DiskAttachment r) ((old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) root)) where
  toContinuousMap := attachmentHomotopyPasting r (boundaryFamilyInclusion J _)
    (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
    (graphContraction_compatible r root Q hQ)
  map_zero_left z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J _) z
    cases w with
    | inl a => exact (Q a).source
    | inr d =>
        change attachmentHomotopyPasting r (boundaryFamilyInclusion J (Fin 1 → ℝ))
          (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
          (graphContraction_compatible r root Q hQ)
          (0, cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) d) = _
        rw [attachmentHomotopyPasting_cell]
        change graphEdgeContraction r root Q hQ d.1 (0, graphDiskHomeomorph.symm d.2) = _
        rw [(graphEdgeContraction_spec r root Q hQ d.1).1]
        change cell r (boundaryFamilyInclusion J (Fin 1 → ℝ))
          ⟨d.1, graphDiskHomeomorph (graphDiskHomeomorph.symm d.2)⟩ = _
        exact congrArg (fun x : ClosedUnitBall (Fin 1 → ℝ) =>
          cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ⟨d.1, x⟩)
          (graphDiskHomeomorph.apply_symm_apply d.2)
  map_one_left z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J _) z
    cases w with
    | inl a => exact (Q a).target
    | inr d =>
        change attachmentHomotopyPasting r (boundaryFamilyInclusion J (Fin 1 → ℝ))
          (graphVertexContraction r root Q) (graphDiskFamilyContraction r root Q hQ)
          (graphContraction_compatible r root Q hQ)
          (1, cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) d) = _
        rw [attachmentHomotopyPasting_cell]
        exact (graphEdgeContraction_spec r root Q hQ d.1).2.1 _

@[simp] theorem graphContraction_old (t : I) (a : V) :
    graphContraction r root Q hQ (t, (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))) a) = Q a t := rfl

end FiniteChains.ClassicalGraphModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (T : Comb.SpanningTree (graphCx r))

def treeAttaching : BoundaryFamily {j : J // T.isTree j} (Fin 1 → ℝ) → V :=
  fun a => r ⟨a.1.val, a.2⟩

abbrev TreeSpace := DiskAttachment (treeAttaching r T)

def treeVertex (a : V) : TreeSpace r T :=
  old (treeAttaching r T) (boundaryFamilyInclusion {j : J // T.isTree j} _) a

def treeUpPath (a : V) (ha : a ≠ T.root) :
    Path (treeVertex r T a) (treeVertex r T (T.parent a ha)) :=
  (graphGermPath (treeAttaching r T)
    (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2)).cast
      (congrArg (treeVertex r T) (T.up_src a ha).symm) rfl

/-- Follow the finitely many chosen parent edges to the root. -/
def treeRootPath (a : V) : Path (treeVertex r T a) (treeVertex r T T.root) :=
  if ha : a = T.root then
    (Path.refl (treeVertex r T T.root)).cast (congrArg (treeVertex r T) ha) rfl
  else (treeUpPath r T a ha).trans (treeRootPath (T.parent a ha))
  termination_by T.ht a
  decreasing_by
    have h := T.ht_parent ha
    omega


theorem treeRootPath_of_ne {a : V} (ha : a ≠ T.root) :
    treeRootPath r T a = (treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha)) := by
  rw [treeRootPath]
  simp only [dif_neg ha]

/-- Every retained edge is a chosen parent edge, so the actual vertex paths
have precisely the compatibility used by the cellwise contraction. -/
theorem treeRootPath_edge (j : {j : J // T.isTree j}) :
    treeRootPath r T (graphSrc (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).trans
        (treeRootPath r T (graphTgt (treeAttaching r T) j)) ∨
    treeRootPath r T (graphTgt (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).symm.trans
        (treeRootPath r T (graphSrc (treeAttaching r T) j)) := by
  obtain ⟨a, ha, he⟩ := (T.isTree_iff j.val).mp j.property
  cases hb : (T.up a ha).2 with
  | false =>
      have hg : T.up a ha = (j.val, false) := Prod.ext he hb
      have ha' : a = graphTgt (treeAttaching r T) j := by
        simpa [hg, Comb.germSrc_false, graphTgt, graphCx, treeAttaching] using (T.up_src a ha).symm
      have hp : T.parent a ha = graphSrc (treeAttaching r T) j := by
        simp only [Comb.SpanningTree.parent, hg, Comb.germTgt_false]
        rfl
      right
      apply Path.ext
      funext t
      have h := congrArg (fun p => p t) (treeRootPath_of_ne r T ha)
      have hu : ∀ s, treeUpPath r T a ha s = (graphEdgePath (treeAttaching r T) j).symm s := by
        intro s
        have hpair :
            (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) = (j, false) := by
          apply Prod.ext
          · simp_all
          · exact hb
        exact congrArg
          (fun g : {j : J // T.isTree j} × Bool => graphGermPath (treeAttaching r T) g s)
          hpair
      calc
        treeRootPath r T (graphTgt (treeAttaching r T) j) t = treeRootPath r T a t :=
          congrArg (fun v => treeRootPath r T v t) ha'.symm
        _ = ((treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha))) t := h
        _ = _ := by
          simp only [Path.trans_apply]
          split_ifs
          · exact hu _
          · exact congrArg (fun v => treeRootPath r T v _) hp
  | true =>
      have hg : T.up a ha = (j.val, true) := Prod.ext he hb
      have ha' : a = graphSrc (treeAttaching r T) j := by
        simpa [hg, Comb.germSrc_true, graphSrc, graphCx, treeAttaching] using (T.up_src a ha).symm
      have hp : T.parent a ha = graphTgt (treeAttaching r T) j := by
        simp only [Comb.SpanningTree.parent, hg, Comb.germTgt_true]
        rfl
      left
      apply Path.ext
      funext t
      have h := congrArg (fun p => p t) (treeRootPath_of_ne r T ha)
      have hu : ∀ s, treeUpPath r T a ha s = graphEdgePath (treeAttaching r T) j s := by
        intro s
        change graphGermPath (treeAttaching r T)
          (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) s = _
        have hpair :
            (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) = (j, true) := by
          apply Prod.ext
          · simp_all
          · exact hb
        exact congrArg
          (fun g : {j : J // T.isTree j} × Bool => graphGermPath (treeAttaching r T) g s)
          hpair
      calc
        treeRootPath r T (graphSrc (treeAttaching r T) j) t = treeRootPath r T a t :=
          congrArg (fun v => treeRootPath r T v t) ha'.symm
        _ = ((treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha))) t := h
        _ = _ := by
          simp only [Path.trans_apply]
          split_ifs
          · exact hu _
          · exact congrArg (fun v => treeRootPath r T v _) hp

variable [DiscreteTopology V]

/-- The actual spanning-tree disk attachment is contracted to its literal
old root vertex. The entire tree may have arbitrarily many edges. -/
def treeContraction : ContinuousMap.Homotopy (ContinuousMap.id (TreeSpace r T))
    (ContinuousMap.const (TreeSpace r T) (treeVertex r T T.root)) :=
  graphContraction (treeAttaching r T) T.root (treeRootPath r T) (treeRootPath_edge r T)

@[simp] theorem treeContraction_vertex (t : I) (a : V) :
    treeContraction r T (t, treeVertex r T a) = treeRootPath r T a t := rfl


/-- The same specified collapse, with the universe-polymorphic singleton. -/
def treeHomotopyEquivPUnit : ContinuousMap.HomotopyEquiv (TreeSpace r T) PUnit where
  toFun := ContinuousMap.const _ PUnit.unit
  invFun := ContinuousMap.const _ (treeVertex r T T.root)
  left_inv := ⟨(treeContraction r T).symm⟩
  right_inv := by
    have he : (ContinuousMap.const PUnit PUnit.unit : C(PUnit, PUnit)) = ContinuousMap.id PUnit := by
      ext x
    change ContinuousMap.Homotopic (ContinuousMap.const PUnit PUnit.unit) (ContinuousMap.id PUnit)
    rw [he]

end FiniteChains.ClassicalGraphModel
end

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u v
variable {D : Type u} [TopologicalSpace D] (S : Set D)

abbrev FullCylinderBoundary :=
  {z : I × D // z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}

variable {Z : Type v} [TopologicalSpace Z]

def fullCylinderPastingFun (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (z : FullCylinderBoundary S) : Z :=
  if h₀ : z.val.1 = 0 then f₀ z.val.2
  else if h₁ : z.val.1 = 1 then f₁ z.val.2
  else H (z.val.1, ⟨z.val.2, (z.property.resolve_left h₀).resolve_left h₁⟩)

theorem fullCylinderPastingFun_zero (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (z : FullCylinderBoundary S) (hz : z.val.1 = 0) :
    fullCylinderPastingFun S f₀ f₁ H z = f₀ z.val.2 := by
  simp only [fullCylinderPastingFun, dif_pos hz]

theorem fullCylinderPastingFun_one (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (z : FullCylinderBoundary S) (hz : z.val.1 = 1) :
    fullCylinderPastingFun S f₀ f₁ H z = f₁ z.val.2 := by simp_all [hz, fullCylinderPastingFun, dif_neg, dif_pos, one_ne_zero, FullCylinderBoundary]

theorem fullCylinderPastingFun_side (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (h₀ : ∀ x, H (0, x) = f₀ x.val) (h₁ : ∀ x, H (1, x) = f₁ x.val)
    (z : FullCylinderBoundary S) (hz : z.val.2 ∈ S) :
    fullCylinderPastingFun S f₀ f₁ H z = H (z.val.1, ⟨z.val.2, hz⟩) := by
  by_cases ht₀ : z.val.1 = 0
  · rw [fullCylinderPastingFun_zero S f₀ f₁ H z ht₀, ht₀, h₀]
  by_cases ht₁ : z.val.1 = 1
  · rw [fullCylinderPastingFun_one S f₀ f₁ H z ht₁, ht₁, h₁]
  simp only [fullCylinderPastingFun, dif_neg ht₀, dif_neg ht₁]

/-- Pasting on the full cylinder boundary, with exact formulas on each of
the three closed pieces. -/
def fullCylinderPasting (hS : IsClosed S) (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (h₀ : ∀ x, H (0, x) = f₀ x.val) (h₁ : ∀ x, H (1, x) = f₁ x.val) :
    C(FullCylinderBoundary S, Z) where
  toFun := fullCylinderPastingFun S f₀ f₁ H
  continuous_toFun := by
    let B₀ : Set (FullCylinderBoundary S) := {z | z.val.1 = 0}
    let B₁ : Set (FullCylinderBoundary S) := {z | z.val.1 = 1}
    let C : Set (FullCylinderBoundary S) := {z | z.val.2 ∈ S}
    have hb₀ : IsClosed B₀ := isClosed_eq (by fun_prop) continuous_const
    have hb₁ : IsClosed B₁ := isClosed_eq (by fun_prop) continuous_const
    have hc : IsClosed C := hS.preimage (continuous_snd.comp continuous_subtype_val)
    have hcover : (B₀ ∪ B₁) ∪ C = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      rcases z.property with h | h | h
      · grind
      · grind
      · grind
    have hf₀ : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) B₀ := by
      apply ((f₀.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      exact fun z hz => fullCylinderPastingFun_zero S f₀ f₁ H z hz
    have hf₁ : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) B₁ := by
      apply ((f₁.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      exact fun z hz => fullCylinderPastingFun_one S f₀ f₁ H z hz
    have hh : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) C := by
      rw [continuousOn_iff_continuous_restrict]
      let k : C(C, I × S) := {
        toFun := fun z => (z.val.val.1, ⟨z.val.val.2, z.property⟩)
        continuous_toFun := by fun_prop }
      have he : C.domRestrict (fullCylinderPastingFun S f₀ f₁ H) = H ∘ k := by
        funext z
        exact fullCylinderPastingFun_side S f₀ f₁ H h₀ h₁ z.val z.property
      rw [he]
      exact H.continuous.comp k.continuous
    rw [← continuousOn_univ, ← hcover]
    exact (hf₀.union_of_isClosed hf₁ hb₀ hb₁).union_of_isClosed hh (hb₀.union hb₁) hc

@[simp] theorem fullCylinderPasting_zero (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (d : D) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(0, d), Or.inl rfl⟩ = f₀ d :=
  fullCylinderPastingFun_zero S f₀ f₁ H _ rfl

@[simp] theorem fullCylinderPasting_one (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (d : D) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(1, d), Or.inr (Or.inl rfl)⟩ = f₁ d :=
  fullCylinderPastingFun_one S f₀ f₁ H _ rfl

@[simp] theorem fullCylinderPasting_side (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (t : I) (x : S) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁
      ⟨(t, x.val), Or.inr (Or.inr x.property)⟩ = H (t, x) :=
  fullCylinderPastingFun_side S f₀ f₁ H h₀ h₁ _ x.property

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D Z : Type u} [TopologicalSpace D] [TopologicalSpace Z]

theorem homotopyRel_of_boundaryContraction (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary S → I × D))
    {f₀ f₁ : C(D, Z)} (F : f₀.Homotopy f₁)
    (J : C(I × (I × S), Z))
    (hJ₀ : ∀ t a, J (0, (t, a)) = F (t, a.val))
    (hJ₁ : ∀ t a, J (1, (t, a)) = f₀ a.val)
    (hJl : ∀ s a, J (s, (0, a)) = f₀ a.val)
    (hJr : ∀ s a, J (s, (1, a)) = f₁ a.val) :
    f₀.HomotopicRel f₁ S := by
  let P₀ : C(D, C(I, Z)) := {
    toFun := fun d => ContinuousMap.const I (f₀ d)
    continuous_toFun := ContinuousMap.continuous_const'.comp f₀.continuous }
  let P₁ : C(D, C(I, Z)) := {
    toFun := fun d => ContinuousMap.const I (f₁ d)
    continuous_toFun := ContinuousMap.continuous_const'.comp f₁.continuous }
  let PS  :=
    (J.comp ⟨fun z => (z.2, z.1), continuous_swap⟩).curry
  have hP₀ : ∀ a, PS (0, a) = P₀ a.val := by
    intro a
    apply ContinuousMap.ext
    exact fun s => hJl s a
  have hP₁ : ∀ a, PS (1, a) = P₁ a.val := by
    intro a
    apply ContinuousMap.ext
    exact fun s => hJr s a
  let PB  :=
    fullCylinderPasting S hS P₀ P₁ PS hP₀ hP₁
  let HB  :=
    PB.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  have hBleft s d :
      HB (s, ⟨(0, d), Or.inl rfl⟩) = f₀ d := by
    exact congrArg (fun f : C(I, Z) => f s)
      (fullCylinderPasting_zero S hS P₀ P₁ PS hP₀ hP₁ d)
  have hBright s d :
      HB (s, ⟨(1, d), Or.inr (Or.inl rfl)⟩) = f₁ d := by
    exact congrArg (fun f : C(I, Z) => f s)
      (fullCylinderPasting_one S hS P₀ P₁ PS hP₀ hP₁ d)
  have hBside (s t) (a : S) :
      HB (s, ⟨(t, a.val), Or.inr (Or.inr a.property)⟩) = J (s, (t, a)) := by
    exact congrArg (fun f : C(I, Z) => f s)
      (fullCylinderPasting_side S hS P₀ P₁ PS hP₀ hP₁ t a)
  have hB₀ : ∀ b : FullCylinderBoundary S, HB (0, b) = F b.val := by
    intro b
    rcases b.property with hb | hb | hb
    · have he : b = ⟨(0, b.val.2), Or.inl rfl⟩ := by
        apply Subtype.ext
        exact Prod.ext hb rfl
      rw [he, hBleft]
      exact (F.apply_zero _).symm
    · have he : b = ⟨(1, b.val.2), Or.inr (Or.inl rfl)⟩ := by
        apply Subtype.ext
        exact Prod.ext hb rfl
      rw [he, hBright]
      exact (F.apply_one _).symm
    · exact (hBside 0 b.val.1 ⟨b.val.2, hb⟩).trans (hJ₀ _ _)
  obtain ⟨G, _, hGB⟩ := hext Z F.toContinuousMap HB hB₀
  refine ⟨{
    toFun := fun td => G (1, td)
    continuous_toFun := G.continuous.comp (continuous_const.prodMk continuous_id)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · simp_all
  · simp_all
  · simp_all

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

def backtrackTime (t : I) : I :=
  ⟨min (2 * (t : ℝ)) (2 - 2 * (t : ℝ)), by
    have hl := t.2.1
    have hu := t.2.2
    constructor
    · apply le_min <;> linarith
    · rcases le_total (t : ℝ) (1 / 2) with h | h
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)⟩

theorem backtrackTime_continuous : Continuous backtrackTime := by
  unfold backtrackTime
  fun_prop

theorem backtrackTime_zero : backtrackTime 0 = 0 := by
  apply Subtype.ext
  norm_num [backtrackTime]

theorem backtrackTime_one : backtrackTime 1 = 0 := by
  apply Subtype.ext
  norm_num [backtrackTime]

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

/-- The composite of the two actual collar maps is homotopic to the
identity. All map equations below are discharged by `desc` in the final
construction of the attaching-homotopy equivalence. -/
theorem attachingBacktrack_homotopic_id (S : Set D) (hS : IsClosed S)
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁)
    (C : C(Space a₁ Subtype.val, Space a₀ Subtype.val))
    (B : C(Space a₀ Subtype.val, Space a₁ Subtype.val))
    (hCold : ∀ p, C (old a₁ Subtype.val p) = old a₀ Subtype.val p)
    (hBold : ∀ p, B (old a₀ Subtype.val p) = old a₁ Subtype.val p)
    (L₀ : C(I × D, Space a₀ Subtype.val))
    (L₁ : C(I × D, Space a₁ Subtype.val))
    (hL₀zero : ∀ d, L₀ (0, d) = cell a₀ Subtype.val d)
    (hL₁zero : ∀ d, L₁ (0, d) = cell a₁ Subtype.val d)
    (hL₀side : ∀ t a, L₀ (t, a.val) = old a₀ Subtype.val (H (t, a)))
    (hL₁side : ∀ t a, L₁ (t, a.val) = old a₁ Subtype.val (H.symm (t, a)))
    (hCcell : ∀ d, C (cell a₁ Subtype.val d) = L₀ (1, d))
    (hBcell : ∀ d, B (cell a₀ Subtype.val d) = L₁ (1, d)) :
    (C.comp B).Homotopic (ContinuousMap.id (Space a₀ Subtype.val)) := by
  let f₀ : C(D, Space a₀ Subtype.val) := ⟨cell a₀ Subtype.val, cell_continuous _ _⟩
  let fm  :=
    C.comp ⟨cell a₁ Subtype.val, cell_continuous _ _⟩
  let f₁ := (C.comp B).comp f₀
  let F₀ : f₀.Homotopy fm := {
    toContinuousMap := L₀
    map_zero_left := hL₀zero
    map_one_left := fun d => (hCcell d).symm }
  let F₁ : fm.Homotopy f₁ := {
    toContinuousMap := C.comp L₁
    map_zero_left := fun d => congrArg C (hL₁zero d)
    map_one_left := fun d => congrArg C (hBcell d).symm }
  let F  := F₀.trans F₁
  have hFside t a :
      F (t, a.val) = old a₀ Subtype.val (H (backtrackTime t, a)) := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change L₀ (_, a.val) = _
      rw [hL₀side]
      congr 2
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact (min_eq_left (by linarith)).symm
    · change C (L₁ (_, a.val)) = _
      rw [hL₁side, hCold]
      change old a₀ Subtype.val (H (unitInterval.symm _, a)) = _
      congr 2
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      change 1 - (2 * t - 1) = min (2 * (t : ℝ)) (2 - 2 * t)
      rw [min_eq_right (by linarith)]
      ring
  have htime : Continuous (fun sta : I × (I × S) =>
      unitInterval.symm sta.1 * backtrackTime sta.2.1) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp
      (unitInterval.continuous_symm.comp continuous_fst)).mul
        (continuous_subtype_val.comp
          (backtrackTime_continuous.comp (continuous_fst.comp continuous_snd)))
  let J : C(I × (I × S), Space a₀ Subtype.val) := {
    toFun := fun sta => old a₀ Subtype.val
      (H (unitInterval.symm sta.1 * backtrackTime sta.2.1, sta.2.2))
    continuous_toFun := (old_continuous _ _).comp (H.continuous.comp
      (htime.prodMk (continuous_snd.comp continuous_snd))) }
  have hJ₀ (t : I) (a : S) : J (0, (t, a)) = F (t, a.val) := by
    change old a₀ Subtype.val (H (unitInterval.symm 0 * backtrackTime t, a)) = _
    simpa using (hFside t a).symm
  have hJ₁ (t : I) (a : S) : J (1, (t, a)) = f₀ a.val := by
    change old a₀ Subtype.val (H (unitInterval.symm 1 * backtrackTime t, a)) =
      cell a₀ Subtype.val a.val
    simp only [unitInterval.symm_one, zero_mul, H.apply_zero]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  have hJl (s : I) (a : S) : J (s, (0, a)) = f₀ a.val := by
    change old a₀ Subtype.val (H (unitInterval.symm s * backtrackTime 0, a)) =
      cell a₀ Subtype.val a.val
    rw [backtrackTime_zero, mul_zero, H.apply_zero]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  have hJr (s : I) (a : S) : J (s, (1, a)) = f₁ a.val := by
    change old a₀ Subtype.val (H (unitInterval.symm s * backtrackTime 1, a)) =
      C (B (cell a₀ Subtype.val a.val))
    rw [backtrackTime_one, mul_zero, H.apply_zero,
      cell_boundary a₀ Subtype.val Subtype.val_injective, hBold, hCold]
  obtain ⟨G⟩ := homotopyRel_of_boundaryContraction S hS hfull F J hJ₀ hJ₁ hJl hJr
  let HOld : C(I × P, Space a₀ Subtype.val) :=
    ⟨fun tp => old a₀ Subtype.val tp.2, (old_continuous _ _).comp continuous_snd⟩
  have hg : ∀ t a, HOld (t, a₀ a) = G (t, a.val) := by
    intro t a
    change old a₀ Subtype.val (a₀ a) = G (t, a.val)
    rw [G.eq_fst t a.property]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  let T := attachmentHomotopyPasting a₀ Subtype.val HOld G.toContinuousMap hg
  have Htotal : ContinuousMap.Homotopy (ContinuousMap.id (Space a₀ Subtype.val))
      (C.comp B) := {
    toContinuousMap := T
    map_zero_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a₀ Subtype.val z
      cases w with
      | inl p => rfl
      | inr d => exact (attachmentHomotopyPasting_cell a₀ Subtype.val
          HOld G.toContinuousMap hg 0 d).trans (G.apply_zero d)
    map_one_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a₀ Subtype.val z
      cases w with
      | inl p => exact ((congrArg C (hBold p)).trans (hCold p)).symm
      | inr d => exact (attachmentHomotopyPasting_cell a₀ Subtype.val
          HOld G.toContinuousMap hg 1 d).trans (G.apply_one d) }
  exact ⟨Htotal.symm⟩

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

theorem exists_attachingDiskExtension (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    ∃ L : C(I × D, Space a₀ Subtype.val),
      (∀ d, L (0, d) = cell a₀ Subtype.val d) ∧
      ∀ t a, L (t, a.val) = old a₀ Subtype.val (H (t, a)) := by
  apply hext (Space a₀ Subtype.val)
    ⟨cell a₀ Subtype.val, cell_continuous _ _⟩
    ((⟨old a₀ Subtype.val, old_continuous _ _⟩ : C(P, Space a₀ Subtype.val)).comp
      H.toContinuousMap)
  intro a
  change old a₀ Subtype.val (H (0, a)) = cell a₀ Subtype.val a.val
  rw [H.apply_zero]
  exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm

def attachingDiskExtension (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) : C(I × D, Space a₀ Subtype.val) :=
  Classical.choose (exists_attachingDiskExtension S hext a₀ a₁ H)

theorem attachingDiskExtension_zero (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (d : D) :
    attachingDiskExtension S hext a₀ a₁ H (0, d) = cell a₀ Subtype.val d :=
  (Classical.choose_spec (exists_attachingDiskExtension S hext a₀ a₁ H)).1 d

theorem attachingDiskExtension_side (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (t : I) (a : S) :
    attachingDiskExtension S hext a₀ a₁ H (t, a.val) = old a₀ Subtype.val (H (t, a)) :=
  (Classical.choose_spec (exists_attachingDiskExtension S hext a₀ a₁ H)).2 t a

def attachingBackwardMap (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    C(Space a₁ Subtype.val, Space a₀ Subtype.val) :=
  desc a₁ Subtype.val ⟨old a₀ Subtype.val, old_continuous _ _⟩
    ((attachingDiskExtension S hext a₀ a₁ H).comp
      ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old a₀ Subtype.val (a₁ a) = attachingDiskExtension S hext a₀ a₁ H (1, a.val)
      rw [attachingDiskExtension_side, H.apply_one])

@[simp] theorem attachingBackwardMap_old (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (p : P) :
    attachingBackwardMap S hext a₀ a₁ H (old a₁ Subtype.val p) = old a₀ Subtype.val p := rfl

@[simp] theorem attachingBackwardMap_cell (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (d : D) :
    attachingBackwardMap S hext a₀ a₁ H (cell a₁ Subtype.val d) =
      attachingDiskExtension S hext a₀ a₁ H (1, d) := by
  unfold attachingBackwardMap
  rw [desc_cell]
  rfl

def attachingHomotopyEquiv (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    ContinuousMap.HomotopyEquiv (Space a₀ Subtype.val) (Space a₁ Subtype.val) where
  toFun := attachingBackwardMap S hext a₁ a₀ H.symm
  invFun := attachingBackwardMap S hext a₀ a₁ H
  left_inv := attachingBacktrack_homotopic_id S hS hfull a₀ a₁ H _ _
    (attachingBackwardMap_old S hext a₀ a₁ H)
    (attachingBackwardMap_old S hext a₁ a₀ H.symm)
    (attachingDiskExtension S hext a₀ a₁ H)
    (attachingDiskExtension S hext a₁ a₀ H.symm)
    (attachingDiskExtension_zero S hext a₀ a₁ H)
    (attachingDiskExtension_zero S hext a₁ a₀ H.symm)
    (attachingDiskExtension_side S hext a₀ a₁ H)
    (attachingDiskExtension_side S hext a₁ a₀ H.symm)
    (attachingBackwardMap_cell S hext a₀ a₁ H)
    (attachingBackwardMap_cell S hext a₁ a₀ H.symm)
  right_inv := by
    apply attachingBacktrack_homotopic_id S hS hfull a₁ a₀ H.symm _ _
      (attachingBackwardMap_old S hext a₁ a₀ H.symm)
      (attachingBackwardMap_old S hext a₀ a₁ H)
      (attachingDiskExtension S hext a₁ a₀ H.symm)
      (attachingDiskExtension S hext a₀ a₁ H)
      (attachingDiskExtension_zero S hext a₁ a₀ H.symm)
      (attachingDiskExtension_zero S hext a₀ a₁ H)
      (attachingDiskExtension_side S hext a₁ a₀ H.symm) _
      (attachingBackwardMap_cell S hext a₁ a₀ H.symm)
      (attachingBackwardMap_cell S hext a₀ a₁ H)
    intro t a
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      attachingDiskExtension_side S hext a₀ a₁ H t a

end FiniteChains.RelativeAttachment

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- The actual incidence from a lifted midpoint to its chosen end. -/
def roseCoverMidpointEndEdge (p : roseCoverMidpoints f) (b : Bool) :
    StrictOrdEdge P := hf.strictEdgeLiftFrom (roseMidEdge p.val.2 b) p.val.1 p.property

/-- The actual incidence from a lifted base vertex to the same lifted end. -/
def roseCoverMidpointBaseEdge (p : roseCoverMidpoints f) (b : Bool) :
    StrictOrdEdge P := hf.strictEdgeLiftTo (roseBaseEdge p.val.2 b)
      (roseCoverMidpointEndEdge f hf p b).val.2
      (congrArg (fun e : StrictOrdEdge (Rose α) => e.val.2)
        (hf.strictEdgeLiftFrom_projection (roseMidEdge p.val.2 b) p.val.1 p.property))

/-- The genuine four-incidence lift of a rose generator. -/
def roseCoverGeneratorChain (p : roseCoverMidpoints f) : StrictOrdEdge P →₀ ℤ :=
  Finsupp.single (roseCoverMidpointBaseEdge f hf p false) 1 -
    Finsupp.single (roseCoverMidpointEndEdge f hf p false) 1 +
    Finsupp.single (roseCoverMidpointEndEdge f hf p true) 1 -
    Finsupp.single (roseCoverMidpointBaseEdge f hf p true) 1

/-- The lifted generator chain has precisely the difference of its actual base endpoints as boundary. -/
theorem roseCoverGeneratorChain_boundary (p : roseCoverMidpoints f) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) (roseCoverGeneratorChain f hf p) =
      Finsupp.single (roseCoverMidpointBaseEdge f hf p true).val.1 1 -
        Finsupp.single (roseCoverMidpointBaseEdge f hf p false).val.1 1 := by
  unfold roseCoverGeneratorChain
  rw [map_sub, map_add, map_sub]
  rw [bdry1_single (X := strictOrderCx P), bdry1_single,
    bdry1_single, bdry1_single]
  simp
  change (Finsupp.single (roseCoverMidpointEndEdge f hf p false).val.2 1 -
      Finsupp.single (roseCoverMidpointBaseEdge f hf p false).val.1 1) -
    (Finsupp.single (roseCoverMidpointEndEdge f hf p false).val.2 1 -
      Finsupp.single p.val.1 1) +
    (Finsupp.single (roseCoverMidpointEndEdge f hf p true).val.2 1 -
      Finsupp.single p.val.1 1) -
    (Finsupp.single (roseCoverMidpointEndEdge f hf p true).val.2 1 -
      Finsupp.single (roseCoverMidpointBaseEdge f hf p true).val.1 1) = _
  abel

/-- The selected incidence coordinates of the genuine generator chain are a unit vector. -/
theorem roseCoverGeneratorChain_coordinates (p : roseCoverMidpoints f) :
    roseCoverGeneratorCoordinates f hf (roseCoverGeneratorChain f hf p) =
      Finsupp.single (roseCoverMidpointEdge f hf p) 1 := by
  classical
  ext e
  obtain ⟨i, hi⟩ := e.property
  have hn : ∀ b, roseCoverMidpointBaseEdge f hf p b ≠ e.val := by
    intro b he
    have hp := (hf.strictEdgeLiftTo_projection (roseBaseEdge p.val.2 b)
      (roseCoverMidpointEndEdge f hf p b).val.2 _).symm.trans
        ((congrArg ((strictOrderCxMap f hf.strictMono).onE) he).trans hi)
    have hs := congrArg (fun r : StrictOrdEdge (Rose α) => r.val.1) hp
    cases hs
  have hm : roseCoverMidpointEndEdge f hf p false ≠ e.val := by
    intro he
    have hp := (hf.strictEdgeLiftFrom_projection (roseMidEdge p.val.2 false)
      p.val.1 p.property).symm.trans
        ((congrArg ((strictOrderCxMap f hf.strictMono).onE) he).trans hi)
    have ht := congrArg (fun r : StrictOrdEdge (Rose α) => r.val.2) hp
    exact Bool.noConfusion (Rose.edg.inj ht).2
  change (roseCoverGeneratorChain f hf p) e.val =
    (Finsupp.single (roseCoverMidpointEdge f hf p) 1) e
  unfold roseCoverGeneratorChain
  simp
  rw [Finsupp.single_eq_of_ne (Ne.symm (hn false)), Finsupp.single_eq_of_ne (Ne.symm hm),
    Finsupp.single_eq_of_ne (Ne.symm (hn true))]
  simp
  have heq : (roseCoverMidpointEndEdge f hf p true = e.val) ↔
      (roseCoverMidpointEdge f hf p = e) := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  simp only [Finsupp.single_apply, heq]

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α P : Type u} [PartialOrder P] (f : P → Rose α) (hf : IsPosetCover f)

/-- Selected coordinates detect finite chains whose boundary is supported on the base fibre. -/
theorem roseCover_chain_eq_zero_of_boundary_off_base (c : StrictOrdEdge P →₀ ℤ)
    (hc : ∀ v, f v ≠ Rose.base → FiniteChains.Comb.bdry1 (strictOrderCx P) c v = 0)
    (hz : ∀ (e : StrictOrdEdge P) (i : α),
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i true → c e = 0) : c = 0 := by
  have hm : ∀ (e : StrictOrdEdge P) (i : α) b,
      (strictOrderCxMap f hf.strictMono).onE e = roseMidEdge i b → c e = 0 := by
    intro e i b he
    cases b with
    | true => grind
    | false =>
      have hv : f e.1.1 = Rose.mid i :=
        congrArg (fun r : StrictOrdEdge (Rose α) => r.1.1) he
      have hl := hf.strictEdgeLiftFrom_unique (roseMidEdge i false) e.1.1 hv e he rfl
      have hr := hz (hf.strictEdgeLiftFrom (roseMidEdge i true) e.1.1 hv) i
        (hf.strictEdgeLiftFrom_projection _ _ _)
      have hb := roseCover_boundary_mid f hf e.1.1 i hv c
      have hn : f e.1.1 ≠ Rose.base := by rw [hv]; intro h; cases h
      rw [hc e.1.1 hn, ← hl, hr] at hb
      omega
  ext e
  obtain ⟨i, b, he⟩ := rose_strict_edge_cases ((strictOrderCxMap f hf.strictMono).onE e)
  rcases he with he | he
  · have hq : f e.1.2 = Rose.edg i b :=
      congrArg (fun r : StrictOrdEdge (Rose α) => r.1.2) he
    have hl := hf.strictEdgeLiftTo_unique (roseBaseEdge i b) e.1.2 hq e he rfl
    have hr := hm (hf.strictEdgeLiftTo (roseMidEdge i b) e.1.2 hq) i b
      (hf.strictEdgeLiftTo_projection _ _ _)
    have hb := roseCover_boundary_end f hf e.1.2 i b hq c
    have hn : f e.1.2 ≠ Rose.base := by rw [hq]; intro h; cases h
    rw [hc e.1.2 hn, ← hl, hr] at hb
    simpa using hb.symm
  · grind

/-- Realize arbitrary finite selected coefficients by genuine generator chains. -/
def roseCoverRealizeGeneratorCoordinates :
    (roseCoverGeneratorEdges f hf →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e =>
    roseCoverGeneratorChain f hf ((roseCoverMidpointEdgeEquiv f hf).symm e))

/-- Realization recovers exactly the prescribed actual selected coefficients. -/
theorem roseCoverRealizeGeneratorCoordinates_coordinates
    (c : roseCoverGeneratorEdges f hf →₀ ℤ) :
    roseCoverGeneratorCoordinates f hf (roseCoverRealizeGeneratorCoordinates f hf c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [roseCoverRealizeGeneratorCoordinates, Finsupp.linearCombination_single, map_smul,
      roseCoverGeneratorChain_coordinates]
    change n • Finsupp.single ((roseCoverMidpointEdgeEquiv f hf)
      ((roseCoverMidpointEdgeEquiv f hf).symm e)) (1 : ℤ) = _
    rw [Equiv.apply_symm_apply, Finsupp.smul_single]
    simp

/-- Every realized finite generator chain has zero boundary outside the actual base fibre. -/
theorem roseCoverRealizeGeneratorCoordinates_boundary_off_base
    (c : roseCoverGeneratorEdges f hf →₀ ℤ) (v : P) (hv : f v ≠ Rose.base) :
    FiniteChains.Comb.bdry1 (strictOrderCx P) (roseCoverRealizeGeneratorCoordinates f hf c) v = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    rw [roseCoverRealizeGeneratorCoordinates, Finsupp.linearCombination_single, map_smul,
      roseCoverGeneratorChain_boundary]
    let p := (roseCoverMidpointEdgeEquiv f hf).symm e
    have hn : ∀ b, v ≠ (roseCoverMidpointBaseEdge f hf p b).val.1 := by
      intro b he
      apply hv
      have hp := hf.strictEdgeLiftTo_projection (roseBaseEdge p.val.2 b)
        (roseCoverMidpointEndEdge f hf p b).val.2
        (congrArg (fun r : StrictOrdEdge (Rose α) => r.val.2)
          (hf.strictEdgeLiftFrom_projection (roseMidEdge p.val.2 b) p.val.1 p.property))
      exact (congrArg f he).trans (congrArg (fun r : StrictOrdEdge (Rose α) => r.val.1) hp)
    simp only [Finsupp.smul_apply, Finsupp.sub_apply]
    change n • ((Finsupp.single (roseCoverMidpointBaseEdge f hf p true).val.1 1) v -
      (Finsupp.single (roseCoverMidpointBaseEdge f hf p false).val.1 (1 : ℤ)) v) = 0
    rw [Finsupp.single_eq_of_ne (hn true), Finsupp.single_eq_of_ne (hn false)]
    simp

/-- Every finite chain with boundary supported on the base fibre is reconstructed from its actual coordinates. -/
theorem roseCover_chain_reconstruct (c : StrictOrdEdge P →₀ ℤ)
    (hc : ∀ v, f v ≠ Rose.base → FiniteChains.Comb.bdry1 (strictOrderCx P) c v = 0) :
    roseCoverRealizeGeneratorCoordinates f hf (roseCoverGeneratorCoordinates f hf c) = c := by
  apply sub_eq_zero.mp
  apply roseCover_chain_eq_zero_of_boundary_off_base f hf
  · intro v hv
    rw [map_sub, Finsupp.sub_apply,
      roseCoverRealizeGeneratorCoordinates_boundary_off_base f hf _ v hv, hc v hv, sub_self]
  · intro e i he
    have h := congrArg (fun z : roseCoverGeneratorEdges f hf →₀ ℤ => z ⟨e, i, he⟩)
      (roseCoverRealizeGeneratorCoordinates_coordinates f hf (roseCoverGeneratorCoordinates f hf c))
    rw [Finsupp.sub_apply]
    exact sub_eq_zero.mpr h

/-- Genuine finite one-cycles are reconstructed from their actual selected incidence coefficients. -/
theorem roseCover_cycle_reconstruct (c : StrictOrdEdge P →₀ ℤ)
    (hc : FiniteChains.Comb.bdry1 (strictOrderCx P) c = 0) :
    roseCoverRealizeGeneratorCoordinates f hf (roseCoverGeneratorCoordinates f hf c) = c := by
  apply roseCover_chain_reconstruct f hf c
  simp_all

/-- For genuine cycles the actual selected coordinate equation is equivalent to chain vanishing. -/
theorem roseCover_cycle_eq_zero_iff_coordinates (c : StrictOrdEdge P →₀ ℤ)
    (hc : FiniteChains.Comb.bdry1 (strictOrderCx P) c = 0) :
    c = 0 ↔ roseCoverGeneratorCoordinates f hf c = 0 := by
  constructor
  · simp_all
  · intro h
    have hr := roseCover_cycle_reconstruct f hf c hc
    rw [h, map_zero] at hr
    exact hr.symm

end FiniteChains.PresModel

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- Actual collapse normalization commutes with the edge boundary. -/
theorem bdry1_normalizedStrictChain1 (g : P → P) (hg : Monotone g)
    (c : StrictOrdEdge P →₀ ℤ) :
    Comb.bdry1 (strictOrderCx P) (normalizedStrictChain1 g hg c) =
      Finsupp.mapDomain g (Comb.bdry1 (strictOrderCx P) c) := by
  erw [bdry1_normalizeOrdChain1, bdry1_chain1, bdry1_chain1]
  change Finsupp.mapDomain g (Finsupp.mapDomain id _) = _
  simp

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → CylBase w) (hf : IsPosetCover f)

/-- The actual collapsed finite edge chain, linearly pulled back to the actual rose preimage. -/
def cylinderCoverCollapsedRoseChain :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (cylinderCoverRoseSet w f) →₀ ℤ) :=
  (Finsupp.lcomapDomain (strictSubposetIncl (cylinderCoverRoseSet w f)).onE
    (strictSubposetIncl_onE_injective _)).comp
      (normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf))

/-- Including the actual rose chain recovers exactly the genuine normalized collapsed chain. -/
theorem cylinderCoverCollapsedRoseChain_inclusion (c : StrictOrdEdge P →₀ ℤ) :
    chain1 (strictSubposetIncl (cylinderCoverRoseSet w f))
      (cylinderCoverCollapsedRoseChain w f hf c) =
        normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf) c := by
  apply Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onE_injective _)
  intro e he
  have hs := cylinderCoverCollapsedChain_support_rose w f hf c e he
  exact ⟨⟨(⟨e.val.1, hs.1⟩, ⟨e.val.2, hs.2⟩), e.property⟩, Subtype.ext rfl⟩

/-- An actual collapsed one-cycle is a genuine one-cycle on the actual rose preimage. -/
theorem cylinderCoverCollapsedRoseChain_cycle (c : StrictOrdEdge P →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx P) c = 0) :
    Comb.bdry1 (strictOrderCx (cylinderCoverRoseSet w f))
      (cylinderCoverCollapsedRoseChain w f hf c) = 0 := by
  apply Finsupp.mapDomain_injective Subtype.val_injective
  change chain0 (strictSubposetIncl (cylinderCoverRoseSet w f))
    (Comb.bdry1 (strictOrderCx (cylinderCoverRoseSet w f))
      (cylinderCoverCollapsedRoseChain w f hf c)) = _
  erw [← bdry1_chain1, cylinderCoverCollapsedRoseChain_inclusion,
    bdry1_normalizedStrictChain1, hc, Finsupp.mapDomain_zero]

/-- The actual surviving generator-incidence coordinates of a collapsed cylinder chain. -/
def cylinderCoverCollapsedGeneratorCoordinates :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ]
      (roseCoverGeneratorEdges (cylinderCoverRoseEnd w f)
        (cylinderCoverRoseEnd_isPosetCover w f hf) →₀ ℤ) :=
  (roseCoverGeneratorCoordinates (cylinderCoverRoseEnd w f)
    (cylinderCoverRoseEnd_isPosetCover w f hf)).comp
      (cylinderCoverCollapsedRoseChain w f hf)

/-- For genuine one-cycles the collapsed chain vanishes exactly when its actual generator coordinates vanish. -/
theorem cylinderCoverCollapsedChain_eq_zero_iff_coordinates (c : StrictOrdEdge P →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf) c = 0 ↔
      cylinderCoverCollapsedGeneratorCoordinates w f hf c = 0 := by
  have hi := cylinderCoverCollapsedRoseChain_inclusion w f hf c
  have he : normalizedStrictChain1 (cylinderCoverCollapse w hf)
      (cylinderCoverCollapse_monotone w hf) c = 0 ↔ cylinderCoverCollapsedRoseChain w f hf c = 0 := by
    constructor
    · intro h
      apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective (cylinderCoverRoseSet w f))
      change chain1 (strictSubposetIncl (cylinderCoverRoseSet w f))
        (cylinderCoverCollapsedRoseChain w f hf c) = Finsupp.mapDomain _ 0
      erw [hi, h, Finsupp.mapDomain_zero]
    · intro h
      erw [← hi, h, map_zero]
  exact he.trans (roseCover_cycle_eq_zero_iff_coordinates (cylinderCoverRoseEnd w f)
    (cylinderCoverRoseEnd_isPosetCover w f hf) (cylinderCoverCollapsedRoseChain w f hf c)
      (cylinderCoverCollapsedRoseChain_cycle w f hf c hc))

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

def presCoverCircleInclusion (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : P :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).val

theorem presCoverCircleInclusion_strictMono (p : PresCoverRelator w f) :
    StrictMono (presCoverCircleInclusion w f hf p) :=
  fun _ _ h => (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.strictMono h

theorem presCoverCircleInclusion_injective (p : PresCoverRelator w f) :
    Function.Injective (presCoverCircleInclusion w f hf p) := by
  intro x y h
  exact (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm.injective (Subtype.ext h)

theorem presCoverCircleInclusion_lt_apex (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : presCoverCircleInclusion w f hf p x < p.1.1 :=
  ((presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2).symm x).property

/-- The genuine finite triangle fan at an actual lifted relator apex. -/
def presCoverRelatorFan (p : PresCoverRelator w f) : StrictOrdTri P →₀ ℤ :=
  strictTopConeEdgeChain (presCoverCircleInclusion w f hf p)
    (presCoverCircleInclusion_strictMono w f hf p) p.1.1
    (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverRelatorFan_boundary (p : PresCoverRelator w f) :
    Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) =
      chain1 (strictOrderCxMap (presCoverCircleInclusion w f hf p)
        (presCoverCircleInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2) :=
  strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (relatorCircleFundamentalChain_cycle w p.1.2)


/-- A genuine lifted fan has precisely the corresponding single relator coordinate. -/
theorem presCoverRelatorChain_fan (hpos : ∀ j, 0 < (w j).length)
    (p : PresCoverRelator w f) :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFan w f hf p) = Finsupp.single p 1 := by
  ext q
  erw [presCoverRelatorChain_apply]
  by_cases h : q = p
  · subst q
    erw [(show presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos p) = 1 by
      erw [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
      have he := Finsupp.mapDomain_apply_of_injective
        (strictTopConeEdgeTriangle_injective (presCoverCircleInclusion w f hf p)
          (presCoverCircleInclusion_strictMono w f hf p) p.1.1
          (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
        (relatorCircleFundamentalChain w p.1.2)
        (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩)
      exact he.trans (relatorCircleFundamentalChain_edge0 w p.1.2 _))]
    simp
  · have hv : q.1.1 ≠ p.1.1 := by
      intro he
      apply h
      apply Subtype.ext
      apply Prod.ext he
      apply Sum.inr_injective
      exact q.2.symm.trans ((congrArg f he).trans p.2)
    have hz := strictTopConeEdgeChain_eq_zero_off_top (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)
      (presCoverRelatorTriangle w f hf hpos q) hv
    erw [show presCoverRelatorFan w f hf p (presCoverRelatorTriangle w f hf hpos q) = 0 from hz]
    simp [h]

/-- A genuine integer-linear realization of finite lifted-relator chains by actual cone fans. -/
def presCoverRelatorFanChain :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (presCoverRelatorFan w f hf)

/-- Actual finite cone-fan realization is a section of actual relator coordinates. -/
theorem presCoverRelatorChain_fanChain (hpos : ∀ j, 0 < (w j).length)
    (c : PresCoverRelator w f →₀ ℤ) :
    presCoverRelatorChain w f hf hpos (presCoverRelatorFanChain w f hf c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n =>
    erw [presCoverRelatorFanChain, Finsupp.linearCombination_single, map_smul,
      presCoverRelatorChain_fan]
    simp

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

theorem presCoverRelatorFan_circle (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 (presCoverRelatorFan w f hf p) =
      relatorCircleFundamentalChain w p.1.2 := by
  ext e
  let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he : (presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE (E.symm e) = e :=
    E.apply_symm_apply e
  have hc := presCoverConeCircleChain_apply w f hf p.1.1 p.1.2 p.2
    (presCoverRelatorFan w f hf p) (E.symm e)
  erw [he] at hc
  erw [hc]
  erw [presCoverRelatorFan, strictTopConeEdgeChain_eq_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective
    (strictTopConeEdgeTriangle_injective (presCoverCircleInclusion w f hf p)
      (presCoverCircleInclusion_strictMono w f hf p) p.1.1
      (presCoverCircleInclusion_lt_apex w f hf p) (presCoverCircleInclusion_injective w f hf p))
    (relatorCircleFundamentalChain w p.1.2) e


/-- Every finite sum of genuine relator fans has its prescribed actual circle link. -/
theorem presCoverRelatorFanChain_circle (c : PresCoverRelator w f →₀ ℤ)
    (q : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf c) =
      c q • relatorCircleFundamentalChain w q.1.2 := by
  induction c using Finsupp.induction_linear with
  | zero => simp [presCoverConeCircleChain]
  | add c d hc hd =>
    have ha : presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2
        (presCoverRelatorFanChain w f hf (c + d)) =
        presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf c) +
        presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFanChain w f hf d) := by
      simp only [presCoverConeCircleChain, map_add]
    erw [ha, hc, hd, Finsupp.add_apply, add_smul]
  | single p n =>
    erw [presCoverRelatorFanChain, Finsupp.linearCombination_single]
    have hs : presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2
        (n • presCoverRelatorFan w f hf p) =
        n • presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFan w f hf p) := by
      simp only [presCoverConeCircleChain, map_smul]
    rw (config := { transparency := .default }) [hs]
    by_cases h : p = q
    · subst p
      rw (config := { transparency := .default }) [presCoverRelatorFan_circle]
      simp
    · rw (config := { transparency := .default }) [(show presCoverConeCircleChain w f hf q.1.1 q.1.2 q.2 (presCoverRelatorFan w f hf p) = 0 by
      have hv : q.1.1 ≠ p.1.1 := by
        intro he
        apply (Ne.symm h)
        apply Subtype.ext
        apply Prod.ext he
        apply Sum.inr_injective
        exact q.2.symm.trans ((congrArg f he).trans p.2)
      ext e
      let E := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf q.1.1 q.1.2 q.2)
      have he : (presCoverConeCircleHom w f hf q.1.1 q.1.2 q.2).onE (E.symm e) = e :=
        E.apply_symm_apply e
      have hc := presCoverConeCircleChain_apply w f hf q.1.1 q.1.2 q.2
        (presCoverRelatorFan w f hf p) (E.symm e)
      erw [he] at hc
      erw [hc, Finsupp.zero_apply]
      exact strictTopConeEdgeChain_eq_zero_off_top (presCoverCircleInclusion w f hf p)
        (presCoverCircleInclusion_strictMono w f hf p) p.1.1
        (presCoverCircleInclusion_lt_apex w f hf p) (relatorCircleFundamentalChain w p.1.2)
        (strictConeTriangle q.1.1 (E.symm e)) hv)]
      simp [h]

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine relator-fan realization recovers every cone link of an actual two-cycle. -/
theorem presCover_cycle_fan_circle (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2
        (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  rw [presCoverRelatorFanChain_circle, presCoverRelatorChain_circle]
  exact relatorCircle_cycle_eq_smul_fundamental w p.1.2 _
    (presCoverConeCircleChain_cycle w f hf p.1.1 p.1.2 p.2 c hc) (hpos p.1.2)

/-- Subtracting the explicit fan realization of its coordinates leaves a genuine
finite chain entirely in the cylinder preimage. -/
theorem presCover_cycle_minus_fans_cylinder_support (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∀ t ∈ (c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)).support,
      f t.1.2.2 ∈ coneAdjBaseSet (S := circSet w) := by
  intro t ht
  by_contra hn
  cases hft : f t.1.2.2 with
  | inl x => exact hn ⟨x, hft.symm⟩
  | inr j =>
    let p : PresCoverRelator w f := ⟨(t.1.2.2, j), hft⟩
    let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
      ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
    have he := congrArg
      (fun z => z ((presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE e))
      (presCover_cycle_fan_circle w f hf hpos c hc p)
    erw [presCoverConeCircleChain_apply, presCoverConeCircleChain_apply] at he
    have hz : (c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) t = 0 := by
      erw [Finsupp.sub_apply]
      exact sub_eq_zero.mpr he
    exact (Finsupp.mem_support_iff.mp ht) hz

/-- Every actual cover two-cycle is its explicit finite relator fan plus an actual
finite triangle chain in the cylinder preimage. -/
theorem exists_presCover_cycle_cone_cylinder_decomposition (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      Finsupp.mapDomain
        (fun t : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} =>
          ((strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onF t :
            StrictOrdTri P)) d =
      c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) := by
  let S  := {p | f p ∈ coneAdjBaseSet}
  let r := c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)
  have hs : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast := presCover_cycle_minus_fans_cylinder_support w f hf hpos c hc t ht
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  let d := Finsupp.comapDomain (strictSubposetIncl S).onF r
    (strictSubposetIncl_onF_injective S).injOn
  refine ⟨d, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onF_injective S) r
    (fun t ht => (strictSubposetIncl_onF_range S t).mpr (hs t ht))

/-- The actual finite cylinder remainder has boundary equal to the negative actual
attaching-circle boundary of the coordinate fans. -/
theorem exists_presCover_cycle_cylinder_boundary (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) ∧
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
        (Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d) =
          -Comb.bdry2 (strictOrderCx P)
            (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  obtain ⟨d, hd⟩ := exists_presCover_cycle_cone_cylinder_decomposition w f hf hpos c hc
  refine ⟨d, hd, ?_⟩
  exact (bdry2_chain2
    (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}) d).symm.trans (by
      change Comb.bdry2 (strictOrderCx P)
        (Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}).onF d) = _
      erw [hd, map_sub, hc, zero_sub])

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))

/-- The actual cylinder collapse kills the boundary of every genuine finite triangle chain. -/
theorem cylinderCover_collapse_boundary_zero {f : P → CylBase w}
    (hf : IsPosetCover f) (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf)
      (Comb.bdry2 (strictOrderCx P) c) = 0 := by
  erw [← bdry2_normalizedStrictChain2, cylinderCover_normalized_collapse_zero, map_zero]

variable (f : P → PresPos w) (hf : IsPosetCover f)

/-- The genuine collapse on the actual cylinder preimage in a presentation cover. -/
def presCoverCylinderCollapse :
    {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →
      {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  cylinderCoverCollapse w (coneAdjCoverBaseEnd_isPosetCover f hf)

theorem presCoverCylinderCollapse_monotone : Monotone (presCoverCylinderCollapse w f hf) :=
  cylinderCoverCollapse_monotone w (coneAdjCoverBaseEnd_isPosetCover f hf)

/-- The actual fan boundary of an actual cover two-cycle has a genuine cylinder
edge-chain lift whose actual collapsed chain is zero. -/
theorem exists_presCover_cycle_collapsed_fan_boundary
    (hpos : ∀ j, 0 < (w j).length) (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b =
        Comb.bdry2 (strictOrderCx P)
          (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) ∧
      normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
        (presCoverCylinderCollapse_monotone w f hf) b = 0 := by
  obtain ⟨d, _, hb⟩ := exists_presCover_cycle_cylinder_boundary w f hf hpos c hc
  refine ⟨-Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet}) d,
    ?_, ?_⟩
  · simp_all
  · have hz := cylinderCover_collapse_boundary_zero w
      (coneAdjCoverBaseEnd_isPosetCover f hf) d
    exact (map_neg _ _).trans ((congrArg Neg.neg hz).trans (neg_zero))

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Each actual lifted attaching circle lies in the actual cylinder preimage. -/
def presCoverCircleCylinderInclusion (p : PresCoverRelator w f)
    (x : RelatorCircle w p.1.2) : {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} :=
  ⟨presCoverCircleInclusion w f hf p x,
    ⟨Sum.inr x.val, (presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2 x).symm⟩⟩

theorem presCoverCircleCylinderInclusion_strictMono (p : PresCoverRelator w f) :
    StrictMono (presCoverCircleCylinderInclusion w f hf p) :=
  fun _ _ h => presCoverCircleInclusion_strictMono w f hf p h

/-- The actual attaching-circle boundary as a genuine chain in the cylinder preimage. -/
def presCoverCylinderRelatorBoundary (p : PresCoverRelator w f) :
    StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ :=
  chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)) (relatorCircleFundamentalChain w p.1.2)

theorem presCoverCylinderRelatorBoundary_inclusion (p : PresCoverRelator w f) :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFan w f hf p) := by
  erw [presCoverRelatorFan_boundary]
  change Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}).onE
    (Finsupp.mapDomain (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
      (presCoverCircleCylinderInclusion_strictMono w f hf p)).onE
      (relatorCircleFundamentalChain w p.1.2)) = _
  erw [← Finsupp.mapDomain_comp]
  rfl

/-- The actual attaching-boundary map on genuine finite lifted-relator chains. -/
def presCoverCylinderRelatorBoundaryChain :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :=
  Finsupp.linearCombination ℤ (presCoverCylinderRelatorBoundary w f hf)

theorem presCoverCylinderRelatorBoundaryChain_inclusion (c : PresCoverRelator w f →₀ ℤ) :
    chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFanChain w f hf c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n =>
    erw [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single,
      map_smul, presCoverCylinderRelatorBoundary_inclusion, presCoverRelatorFanChain,
      Finsupp.linearCombination_single, map_smul]

/-- Actual cover two-cycle coordinates satisfy the actual collapsed attaching-boundary equation. -/
theorem presCover_cycle_collapsed_relator_boundary_zero
    (hpos : ∀ j, 0 < (w j).length) (c : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) = 0 := by
  obtain ⟨b, hb, hz⟩ := exists_presCover_cycle_collapsed_fan_boundary w f hf hpos c hc
  have he  :=
    Finsupp.mapDomain_injective
      (strictSubposetIncl_onE_injective {p : P | f p ∈ coneAdjBaseSet})
      ((presCoverCylinderRelatorBoundaryChain_inclusion w f hf _).trans hb.symm)
  simp_all

end FiniteChains.PresModel
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)


theorem presCoverCylinderRelatorBoundaryChain_cycle (c : PresCoverRelator w f →₀ ℤ) :
    Comb.bdry1 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single p n =>
    erw [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single,
      map_smul, (show Comb.bdry1 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) = 0 by
        erw [bdry1_chain1, relatorCircleFundamentalChain_cycle, map_zero]), smul_zero]

/-- A relator vector with actual collapsed boundary zero has an actual finite cylinder filling. -/
theorem exists_presCover_relator_cylinder_filling (c : PresCoverRelator w f →₀ ℤ)
    (hc : normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        presCoverCylinderRelatorBoundaryChain w f hf c := by
  obtain ⟨d, hd⟩ := strict_oneCycle_comparable_boundary id (presCoverCylinderCollapse w f hf)
    monotone_id (presCoverCylinderCollapse_monotone w f hf)
    ((coneAdjCoverBaseEnd_isPosetCover f hf).le_upTransform
      (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w)))
    (presCoverCylinderRelatorBoundaryChain w f hf c)
    (presCoverCylinderRelatorBoundaryChain_cycle w f hf c)
  erw [hc, normalizedStrictChain1_id, zero_sub] at hd
  exact ⟨-d, by erw [map_neg, hd, neg_neg]⟩

/-- Actual cylinder triangle chains have zero genuine relator coordinates. -/
theorem presCoverRelatorChain_cylinder_zero (hpos : ∀ j, 0 < (w j).length)
    (c : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :
    presCoverRelatorChain w f hf hpos
      (chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => erw [map_add, map_add, hc, hd, add_zero]
  | single t n =>
    change presCoverRelatorChain w f hf hpos
      (Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}).onF
        (Finsupp.single t n)) = 0
    erw [Finsupp.mapDomain_single]
    ext p
    erw [presCoverRelatorChain_apply, Finsupp.zero_apply]
    have hn : (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}).onF t ≠
        presCoverRelatorTriangle w f hf hpos p := by
      intro he
      have hv := congrArg (fun r : StrictOrdTri P => f r.1.2.2) he
      have hp := t.1.2.2.property
      erw [hv, p.2] at hp
      simp [coneAdjBaseSet, ConeAdj.inc, apexOf, ConeAdj.apex] at hp
    simp [hn]

/-- Actual collapsed-boundary cycles are realized by genuine finite cover two-cycles. -/
theorem exists_presCover_cycle_of_collapsed_relator_boundary
    (hpos : ∀ j, 0 < (w j).length) (c : PresCoverRelator w f →₀ ℤ)
    (hc : normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0) :
    ∃ z : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) z = 0 ∧
      presCoverRelatorChain w f hf hpos z = c := by
  obtain ⟨d, hd⟩ := exists_presCover_relator_cylinder_filling w f hf c hc
  let I := strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}
  let L : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} → StrictOrdTri P :=
    fun t => ⟨(t.1.1.val, t.1.2.1.val, t.1.2.2.val), t.2⟩
  let u  := Finsupp.mapDomain L d
  have hb : Comb.bdry2 (strictOrderCx P) u =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFanChain w f hf c) :=
    (bdry2_chain2 I d).trans ((congrArg (chain1 I) hd).trans
      (presCoverCylinderRelatorBoundaryChain_inclusion w f hf c))
  have hu  :=
    presCoverRelatorChain_cylinder_zero w f hf hpos d
  refine ⟨presCoverRelatorFanChain w f hf c - u, ?_, ?_⟩
  · simp_all
  · erw [map_sub, presCoverRelatorChain_fanChain, hu, sub_zero]

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine collapsed attaching-boundary linear map on actual finite lifted relators. -/
def presCoverCollapsedRelatorBoundary :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :=
  (normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
    (presCoverCylinderCollapse_monotone w f hf)).comp
      (presCoverCylinderRelatorBoundaryChain w f hf)

/-- Actual genuine two-cycle coordinates take values in the proved collapsed-boundary kernel. -/
def presCoverCycleRelatorKernelMap :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) →ₗ[ℤ]
      LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) :=
  (presCoverCycleRelatorLinear w f hf hpos).codRestrict
    (LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf))
    (fun c => LinearMap.mem_ker.mpr
      (presCover_cycle_collapsed_relator_boundary_zero w f hf hpos c.val
        (LinearMap.mem_ker.mp c.property)))



/-- Genuine presentation-cover two-cycles are linearly equivalent to the kernel of
its actual collapsed attaching-boundary map, with no assumed comparison premise. -/
def presCoverCycleRelatorKernelEquiv :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) ≃ₗ[ℤ]
      LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) :=
  LinearEquiv.ofBijective (presCoverCycleRelatorKernelMap w f hf hpos)
    ⟨(by
      intro c d he
      apply presCoverCycleRelatorLinear_injective w f hf hpos
      exact congrArg Subtype.val he),
      (by
        intro c
        obtain ⟨z, hz, he⟩ := exists_presCover_cycle_of_collapsed_relator_boundary w f hf hpos c.val
          (LinearMap.mem_ker.mp c.property)
        exact ⟨⟨z, LinearMap.mem_ker.mpr hz⟩, Subtype.ext he⟩)⟩

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- Actual generator-incidence coefficients of the genuine collapsed attaching-boundary map. -/
def presCoverRelatorGeneratorBoundary :=
  (cylinderCoverCollapsedGeneratorCoordinates w (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf)).comp
      (presCoverCylinderRelatorBoundaryChain w f hf)

/-- Vanishing of the genuine collapsed relator boundary is equivalent to its actual generator equation. -/
theorem presCoverCollapsedRelatorBoundary_eq_zero_iff_generator
    (c : PresCoverRelator w f →₀ ℤ) :
    presCoverCollapsedRelatorBoundary w f hf c = 0 ↔
      presCoverRelatorGeneratorBoundary w f hf c = 0 :=
  cylinderCoverCollapsedChain_eq_zero_iff_coordinates w (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf) (presCoverCylinderRelatorBoundaryChain w f hf c)
      (presCoverCylinderRelatorBoundaryChain_cycle w f hf c)

/-- Equality of the two genuine kernels is proved from actual cycle-coordinate detection. -/
theorem presCoverCollapsedRelatorBoundary_ker_eq_generator :
    LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) =
      LinearMap.ker (presCoverRelatorGeneratorBoundary w f hf) := by
  ext c
  exact presCoverCollapsedRelatorBoundary_eq_zero_iff_generator w f hf c

/-- Genuine presentation-cover two-cycles are equivalent to the actual generator-boundary kernel. -/
def presCoverCycleRelatorGeneratorKernelEquiv (hpos : ∀ j, 0 < (w j).length) :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) ≃ₗ[ℤ]
      LinearMap.ker (presCoverRelatorGeneratorBoundary w f hf) :=
  (presCoverCycleRelatorKernelEquiv w f hf hpos).trans
    (LinearEquiv.ofEq _ _ (presCoverCollapsedRelatorBoundary_ker_eq_generator w f hf))

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb CategoryTheory
universe u

instance cPos_finite : Finite CPos := by
  let index : CPos → Fin 4
    | .cor => 0
    | .cmid => 1
    | .cedgL => 2
    | .cedgR => 3
  exact Finite.of_injective index (by
    intro a b h
    cases a <;> cases b <;> simp_all [index])

instance rose_finite {α : Type u} [Finite α] : Finite (Rose α) := by
  let decode : Option (α × Option Bool) → Rose α
    | none => .base
    | some (a, none) => .mid a
    | some (a, some b) => .edg a b
  apply Finite.of_surjective decode
  intro r
  cases r with
  | base => exact ⟨none, rfl⟩
  | mid a => exact ⟨some (a, none), rfl⟩
  | edg a b => exact ⟨some (a, some b), rfl⟩

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb CategoryTheory Simplicial
open scoped Classical

variable {α : Type}

def roseCopy (a : α) : Rose PUnit.{1} ↪o Rose α where
  toFun
    | .base => .base
    | .mid _ => .mid a
    | .edg _ b => .edg a b
  inj' := by
    intro p q h
    cases p <;> cases q <;> simp_all
  map_rel_iff' := by
    intro p q
    change Rose.le _ _ ↔ Rose.le p q
    cases p <;> cases q <;> simp [Rose.le, RelEmbedding.coe_mk]

def roseCopyRealization (a : α) : C(orderNerveRealization (Rose PUnit),
    orderNerveRealization (Rose α)) :=
  (orderNerveRealizationMap (roseCopy a) (roseCopy a).monotone).hom

def orderRoseBase (α : Type) : orderNerveRealization (Rose α) :=
  orderNerveRealizationVertex Rose.base

theorem realizedMap_vertex {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (p : P) :
    orderNerveRealizationMap f hf (orderNerveRealizationVertex p) =
      orderNerveRealizationVertex (f p) := by
  have h := congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
      orderNerveRealization Q => k default)
    (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ p))
  exact h

@[simp] theorem roseCopyRealization_base (a : α) :
    roseCopyRealization a (orderRoseBase PUnit) = orderRoseBase α :=
  realizedMap_vertex (roseCopy a) (roseCopy a).monotone Rose.base

theorem roseCopyRealization_injective (a : α) : Function.Injective (roseCopyRealization a) :=
  orderNerveRealizationMap_injective (roseCopy a) (roseCopy a).monotone (roseCopy a).injective

theorem rose_le_base (p : Rose α) (hp : p ≤ .base) : p = .base := by
  cases p with
  | base => rfl
  | mid a => exact hp.elim
  | edg a b => exact hp.elim

theorem rose_le_mid_has_copy (a : α) (p : Rose α) (hp : p ≤ .mid a) :
    ∃ q, roseCopy a q = p := by
  cases p with
  | base => exact hp.elim
  | mid b => exact ⟨.mid PUnit.unit, congrArg Rose.mid hp.symm⟩
  | edg b s => exact hp.elim

theorem rose_le_edg_has_copy (a : α) (b : Bool) (p : Rose α)
    (hp : p ≤ .edg a b) : ∃ q, roseCopy a q = p := by
  cases p with
  | base => exact ⟨.base, rfl⟩
  | mid c => exact ⟨.mid PUnit.unit, congrArg Rose.mid hp.symm⟩
  | edg c s =>
      exact ⟨.edg PUnit.unit s, congrArg (fun c => Rose.edg c s) hp.1.symm⟩

theorem roseSimplex_copy_lift {n : SimplexCategory}
    (s : (nerve (Rose α)).obj (Opposite.op n)) (a : α)
    (hs : ∀ i, ∃ p, roseCopy a p = s.obj i) :
    ∃ t : (nerve (Rose PUnit)).obj (Opposite.op n),
      (nerveMap (roseCopy a).monotone.functor).app _ t = s := by
  choose p hp using hs
  let t  :=
    (show Monotone p from fun i j hij =>
      (roseCopy a).le_iff_le.mp (by
        rw [hp i, hp j]
        exact leOfHom (s.map (homOfLE hij)))).functor
  exact ⟨t, CategoryTheory.Functor.ext hp⟩

theorem roseSimplex_cases {n : SimplexCategory}
    (s : (nerve (Rose α)).obj (Opposite.op n)) :
    (∀ i, s.obj i = .base) ∨
      ∃ (a : α) (t : (nerve (Rose PUnit)).obj (Opposite.op n)),
        (nerveMap (roseCopy a).monotone.functor).app _ t = s := by
  let last  := Fin.last n.len
  have hle (i : Fin (n.len + 1)) : s.obj i ≤ s.obj last :=
    leOfHom (s.map (homOfLE (Fin.le_last i)))
  cases he : s.obj last with
  | base => exact Or.inl (fun i => rose_le_base _ (he ▸ hle i))
  | mid a =>
      obtain ⟨t, ht⟩ := roseSimplex_copy_lift s a
        (fun i => rose_le_mid_has_copy a _ (he ▸ hle i))
      exact Or.inr ⟨a, t, ht⟩
  | edg a b =>
      obtain ⟨t, ht⟩ := roseSimplex_copy_lift s a
        (fun i => rose_le_edg_has_copy a b _ (he ▸ hle i))
      exact Or.inr ⟨a, t, ht⟩

theorem constantSimplex_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (p : P)
    (hs : ∀ i, s.obj i = p) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationSimplex P s z = orderNerveRealizationVertex p := by
  apply orderNerveRealizationCoordinates_injective P
  funext q
  rw [orderNerveRealizationCoordinates_simplex, orderNerveRealizationCoordinates_vertex]
  change (∑ i, z.down.weights i * (if s.obj i = q then 1 else 0)) = _
  simp_all

theorem orderRoseRealization_continuous_iff {X : Type*} [TopologicalSpace X]
    (f : orderNerveRealization (Rose α) → X) :
    Continuous f ↔ ∀ a, Continuous (f ∘ roseCopyRealization a) := by
  constructor
  · intro hf a
    exact hf.comp (roseCopyRealization a).continuous
  · intro hf
    apply (orderNerveRealization_continuous_iff (Rose α) f).mpr
    intro n s
    rcases roseSimplex_cases s with hs | ⟨a, t, ht⟩
    · have he : f ∘ orderNerveRealizationSimplex (Rose α) s =
          fun _ => f (orderRoseBase α) :=
        funext (fun z => congrArg f (constantSimplex_vertex s .base hs z))
      rw [he]
      exact continuous_const
    · have he : roseCopyRealization a ∘ orderNerveRealizationSimplex (Rose PUnit) t =
          orderNerveRealizationSimplex (Rose α) s := by
        funext z
        have h := congrArg (fun k => k z)
          (orderNerveRealizationSimplex_natural (roseCopy a) (roseCopy a).monotone t)
        simpa only [ht, roseCopyRealization, TopCat.comp_app, Function.comp_apply] using h
      rw [← he]
      exact (hf a).comp (orderNerveRealizationSimplex (Rose PUnit) t).hom.continuous

theorem orderRoseRealization_cases (x : orderNerveRealization (Rose α)) :
    x = orderRoseBase α ∨ ∃ a u, roseCopyRealization a u = x := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective (Rose α) x
  rcases roseSimplex_cases s with hs | ⟨a, t, ht⟩
  · exact Or.inl (constantSimplex_vertex s .base hs z)
  · right
    refine ⟨a, orderNerveRealizationSimplex (Rose PUnit) t z, ?_⟩
    have h := congrArg (fun k => k z)
      (orderNerveRealizationSimplex_natural (roseCopy a) (roseCopy a).monotone t)
    simpa only [ht, roseCopyRealization, TopCat.comp_app, Function.comp_apply] using h


theorem smallRose_eq_base (x : orderNerveRealization (Rose PUnit))
    (hx : ∀ q, q ≠ .base → orderNerveRealizationCoordinates (Rose PUnit) x q = 0) :
    x = orderRoseBase PUnit := by
  letI : Fintype (Rose PUnit) := Fintype.ofFinite _
  have hb : orderNerveRealizationCoordinates (Rose PUnit) x .base = 1 := by
    calc
      orderNerveRealizationCoordinates (Rose PUnit) x .base =
          ∑ q : Rose PUnit, orderNerveRealizationCoordinates (Rose PUnit) x q :=
        (Fintype.sum_eq_single Rose.base hx).symm
      _ = 1 := orderNerveRealizationCoordinates_sum x
  apply orderNerveRealizationCoordinates_injective (Rose PUnit)
  funext q
  rw [orderRoseBase, orderNerveRealizationCoordinates_vertex]
  by_cases hq : q = .base
  · simp_all
  · grind

theorem roseCopyRealization_intersection {a b : α} (hab : a ≠ b)
    (x y : orderNerveRealization (Rose PUnit))
    (h : roseCopyRealization a x = roseCopyRealization b y) :
    x = orderRoseBase PUnit ∧ y = orderRoseBase PUnit := by
  have oneSide {a b : α} (hab : a ≠ b) (x y)
      (h : roseCopyRealization a x = roseCopyRealization b y) :
      x = orderRoseBase PUnit := by
    apply smallRose_eq_base
    intro q hq
    have hc := congrArg (fun z => orderNerveRealizationCoordinates (Rose α) z (roseCopy a q)) h
    dsimp only [roseCopyRealization] at hc
    rw [orderNerveRealizationCoordinates_map_injective (roseCopy a)
      (roseCopy a).monotone (roseCopy a).injective] at hc
    exact hc.trans (orderNerveRealizationCoordinates_map_outside
      (roseCopy b) (roseCopy b).monotone y (roseCopy a q) (by
        rintro ⟨p, hp⟩
        cases q <;> cases p <;> simp_all [roseCopy, RelEmbedding.coe_mk]))
  grind

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open scoped Classical

def roseFourVertex : Fin 4 → Rose PUnit :=
  ![.base, .edg PUnit.unit false, .mid PUnit.unit, .edg PUnit.unit true]


theorem roseFourVertex_surjective : Function.Surjective roseFourVertex := by
  intro p
  cases p with
  | base => exact ⟨0, rfl⟩
  | mid a => cases a; exact ⟨2, rfl⟩
  | edg a b =>
      cases a
      cases b
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩

def roseFourVertexEquiv : Fin 4 ≃ Rose PUnit :=
  Equiv.ofBijective roseFourVertex ⟨(by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [roseFourVertex]), roseFourVertex_surjective⟩

@[simp] theorem roseFourVertex_zero : roseFourVertex 0 = Rose.base := rfl

end FiniteChains.PresModel

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {J : Type u} {D : J → Type u} [∀ j, TopologicalSpace (D j)]

def sigmaCylinderHomeomorph : (Σ j, I × D j) ≃ₜ I × (Σ j, D j) where
  toFun z := (z.2.1, ⟨z.1, z.2.2⟩)
  invFun z := ⟨z.2.1, (z.1, z.2.2)⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z with | mk t d => cases d; rfl
  continuous_toFun := continuous_sigma (fun _ =>
    continuous_fst.prodMk (continuous_sigmaMk.comp continuous_snd))
  continuous_invFun := by
    let swapFibres : (Σ j, D j × I) → Σ j, I × D j := fun z => ⟨z.1, (z.2.2, z.2.1)⟩
    have hs : Continuous swapFibres := continuous_sigma (fun _ =>
      continuous_sigmaMk.comp continuous_swap)
    exact hs.comp ((Homeomorph.sigmaProdDistrib (X := D) (Y := I)).continuous.comp continuous_swap)

def SigmaSubspace (S : ∀ j, Set (D j)) : Set (Σ j, D j) := {d | d.2 ∈ S d.1}

theorem sigmaSubspace_isClosed (S : ∀ j, Set (D j)) (hS : ∀ j, IsClosed (S j)) :
    IsClosed (SigmaSubspace S) :=
  isClosed_sigma_iff.mpr hS

theorem sigmaSubspace_hasHomotopyExtension (S : ∀ j, Set (D j))
    (h : ∀ j, HasHomotopyExtension (Subtype.val : S j → D j)) :
    HasHomotopyExtension (Subtype.val : SigmaSubspace S → Σ j, D j) := by
  intro Z _ f H h₀
  have hex j : ∃ G : C(I × D j, Z),
      (∀ d, G (0, d) = f ⟨j, d⟩) ∧
      ∀ t (a : S j), G (t, a.val) = H (t, ⟨⟨j, a.val⟩, a.property⟩) := by
    let k : C(S j, SigmaSubspace S) :=
      ⟨fun a => ⟨⟨j, a.val⟩, a.property⟩,
        (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _⟩
    exact h j Z (f.comp ⟨Sigma.mk j, continuous_sigmaMk⟩)
      (H.comp ⟨fun ta => (ta.1, k ta.2),
        continuous_fst.prodMk (k.continuous.comp continuous_snd)⟩)
      (fun a => h₀ (k a))
  choose G hG₀ hGA using hex
  let F : C((Σ j, D j), C(I, Z)) := {
    toFun := fun d => ((G d.1).comp ⟨Prod.swap, continuous_swap⟩).curry d.2
    continuous_toFun := continuous_sigma (fun j =>
      ((G j).comp ⟨Prod.swap, continuous_swap⟩).curry.continuous) }
  let L  := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  refine ⟨L, ?_, ?_⟩
  · rintro ⟨j, d⟩
    exact hG₀ j d
  · intro t ⟨⟨j, d⟩, hd⟩
    exact hGA j t ⟨d, hd⟩

theorem sigmaFullCylinder_hasHomotopyExtension (S : ∀ j, Set (D j))
    (h : ∀ j, HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary (S j) → I × D j)) :
    HasHomotopyExtension
      (Subtype.val : FullCylinderBoundary (SigmaSubspace S) → I × (Σ j, D j)) := by
  intro Z _ f H h₀
  have hex j : ∃ G : C(I × (I × D j), Z),
      (∀ td, G (0, td) = f (td.1, ⟨j, td.2⟩)) ∧
      ∀ s (b : FullCylinderBoundary (S j)),
        G (s, b.val) = H (s, ⟨(b.val.1, ⟨j, b.val.2⟩), b.property⟩) := by
    let k : C(I × D j, I × (Σ j, D j)) :=
      ⟨fun td => (td.1, ⟨j, td.2⟩),
        continuous_fst.prodMk (continuous_sigmaMk.comp continuous_snd)⟩
    let kb : C(FullCylinderBoundary (S j), FullCylinderBoundary (SigmaSubspace S)) :=
      ⟨fun b => ⟨k b.val, b.property⟩, (k.continuous.comp continuous_subtype_val).subtype_mk _⟩
    exact h j Z (f.comp k)
      (H.comp ⟨fun sb => (sb.1, kb sb.2),
        continuous_fst.prodMk (kb.continuous.comp continuous_snd)⟩)
      (fun b => h₀ (kb b))
  choose G hG₀ hGA using hex
  let F : C((Σ j, I × D j), C(I, Z)) := {
    toFun := fun d => ((G d.1).comp ⟨Prod.swap, continuous_swap⟩).curry d.2
    continuous_toFun := continuous_sigma (fun j =>
      ((G j).comp ⟨Prod.swap, continuous_swap⟩).curry.continuous) }
  let L : C(I × (I × (Σ j, D j)), Z) := F.uncurry.comp
    ⟨fun s_td => ((sigmaCylinderHomeomorph (D := D)).symm s_td.2, s_td.1),
      ((sigmaCylinderHomeomorph (D := D)).symm.continuous.comp continuous_snd).prodMk
        continuous_fst⟩
  refine ⟨L, ?_, ?_⟩
  · rintro ⟨t, ⟨j, d⟩⟩
    exact hG₀ j (t, d)
  · intro s ⟨⟨t, ⟨j, d⟩⟩, hb⟩
    exact hGA j s ⟨(t, d), hb⟩

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def unitBoundarySubspaceHomeomorph :
    UnitBoundary E ≃ₜ {d : ClosedUnitBall E // ‖d.val‖ = 1} where
  toFun d := ⟨unitBoundaryInclusion E d, d.property⟩
  invFun d := ⟨d.val.val, d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (unitBoundaryInclusion E).continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _


theorem diskFamilySubspace_hasHomotopyExtension (J : Type u) :
    HasHomotopyExtension
      (Subtype.val : SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1}) →
        Σ _ : J, ClosedUnitBall E) :=
  sigmaSubspace_hasHomotopyExtension _ (fun _ => ((unitBoundary_hasHomotopyExtension E).homeomorph
    (unitBoundarySubspaceHomeomorph E) (Homeomorph.refl _) Subtype.val (fun _ => rfl)))

theorem diskFamilyFullCylinder_hasHomotopyExtension (J : Type u) :
    HasHomotopyExtension (Subtype.val :
      FullCylinderBoundary (SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1})) →
        I × (Σ _ : J, ClosedUnitBall E)) :=
  sigmaFullCylinder_hasHomotopyExtension _ (fun _ =>
    fullBallCylinderBoundary_hasHomotopyExtension E)

end FiniteChains.RelativeAttachment

namespace ContinuousMap.HomotopyEquiv

universe u v w z

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

/-- A left homotopy inverse and a possibly different right homotopy inverse
agree up to homotopy.  The result retains exactly the specified forward map. -/
def ofLeftRightHomotopyInverse (f : C(X, Y)) (l r : C(Y, X))
    (hl : (l.comp f).Homotopic (ContinuousMap.id X))
    (hr : (f.comp r).Homotopic (ContinuousMap.id Y)) : HomotopyEquiv X Y where
  toFun := f
  invFun := l
  left_inv := hl
  right_inv := by
    have hlr : l.Homotopic r :=
      ((Homotopic.refl l).comp hr.symm).trans (hl.comp (Homotopic.refl r))
    exact ((Homotopic.refl f).comp hlr).trans hr

@[simp] theorem ofLeftRightHomotopyInverse_toFun (f : C(X, Y)) (l r : C(Y, X))
    (hl : (l.comp f).Homotopic (ContinuousMap.id X))
    (hr : (f.comp r).Homotopic (ContinuousMap.id Y)) :
    (ofLeftRightHomotopyInverse f l r hl hr).toFun = f := rfl

/-- If `C ∘ F` is homotopic to the identity and `C` is an equivalence, then
`F` is its homotopy inverse.  The forward map is literally `F`. -/
def ofHomotopicSection (C : HomotopyEquiv Y X) (F : C(X, Y))
    (H : (C.toFun.comp F).Homotopic (ContinuousMap.id X)) : HomotopyEquiv X Y where
  toFun := F
  invFun := C.toFun
  left_inv := H
  right_inv := by
    have hF : F.Homotopic C.invFun :=
      (C.left_inv.symm.comp (Homotopic.refl F)).trans
        ((Homotopic.refl C.invFun).comp H)
    exact (hF.comp (Homotopic.refl C.toFun)).trans C.left_inv

@[simp] theorem ofHomotopicSection_toFun (C : HomotopyEquiv Y X) (F : C(X, Y))
    (H : (C.toFun.comp F).Homotopic (ContinuousMap.id X)) :
    (ofHomotopicSection C F H).toFun = F := rfl

@[simp] theorem ofHomotopicSection_invFun (C : HomotopyEquiv Y X) (F : C(X, Y))
    (H : (C.toFun.comp F).Homotopic (ContinuousMap.id X)) :
    (ofHomotopicSection C F H).invFun = C.toFun := rfl

variable (f : C(X, Y)) (g : C(Y, Z)) (h : C(Z, W))
  (E : HomotopyEquiv X Z) (hE : E.toFun = g.comp f)
  (D : HomotopyEquiv Y W) (hD : D.toFun = h.comp g)

/-- Two-of-six, middle map.  The inverse supplied by `D` is a left inverse
of `g`, and the inverse supplied by `E` gives a right inverse. -/
def twoOfSixMiddle : HomotopyEquiv Y Z :=
  ofLeftRightHomotopyInverse g (D.invFun.comp h) (f.comp E.invFun)
    (by
      change (D.invFun.comp (h.comp g)).Homotopic (ContinuousMap.id Y)
      rw [← hD]
      exact D.left_inv)
    (by
      change ((g.comp f).comp E.invFun).Homotopic (ContinuousMap.id Z)
      rw [← hE]
      exact E.right_inv)

@[simp] theorem twoOfSixMiddle_toFun : (twoOfSixMiddle f g h E hE D hD).toFun = g := rfl

@[simp] theorem twoOfSixMiddle_invFun :
    (twoOfSixMiddle f g h E hE D hD).invFun = D.invFun.comp h := rfl

/-- Two-of-six, left map, with forward map exactly `f` and inverse
`E.invFun ∘ g`. -/
def twoOfSixLeft : HomotopyEquiv X Y :=
  ofHomotopicSection ((twoOfSixMiddle f g h E hE D hD).trans E.symm) f (by
    change (E.invFun.comp (g.comp f)).Homotopic (ContinuousMap.id X)
    rw [← hE]
    exact E.left_inv)

@[simp] theorem twoOfSixLeft_toFun : (twoOfSixLeft f g h E hE D hD).toFun = f := rfl

@[simp] theorem twoOfSixLeft_invFun :
    (twoOfSixLeft f g h E hE D hD).invFun = E.invFun.comp g := rfl

/-- Two-of-six, right map, retaining the specified `h`. -/
def twoOfSixRight : HomotopyEquiv Z W :=
  ofHomotopicSection (D.symm.trans (twoOfSixMiddle f g h E hE D hD)) h (by
    change (g.comp (D.invFun.comp h)).Homotopic (ContinuousMap.id Z)
    exact (twoOfSixMiddle f g h E hE D hD).right_inv)

@[simp] theorem twoOfSixRight_toFun : (twoOfSixRight f g h E hE D hD).toFun = h := rfl

end ContinuousMap.HomotopyEquiv

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P K : Type u} [TopologicalSpace D] [TopologicalSpace P] [TopologicalSpace K]

def attachmentBaseMapEquivOfHomotopicId (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (h : C(P, P))
    (H : ContinuousMap.Homotopy (ContinuousMap.id P) h) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (h ∘ a) Subtype.val) := by
  let Hatt : a.Homotopy (h.comp a) := H.compContinuousMap a
  let C := (attachingHomotopyEquiv S hS hext hfull a (h.comp a) Hatt).symm
  let F := attachmentBaseMap a Subtype.val Subtype.val_injective h
  let L := attachingDiskExtension S hext a (h.comp a) Hatt
  let HOld : C(I × P, Space a Subtype.val) :=
    ⟨fun tp => old a Subtype.val (H tp), (old_continuous _ _).comp H.continuous⟩
  have hcompat : ∀ t b, HOld (t, a b) = L (t, b.val) := by
    intro t b
    exact (attachingDiskExtension_side S hext a (h.comp a) Hatt t b).symm
  let T := attachmentHomotopyPasting a Subtype.val HOld L hcompat
  have HT : ContinuousMap.Homotopy (ContinuousMap.id (Space a Subtype.val))
      (C.toFun.comp F) := {
    toContinuousMap := T
    map_zero_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p => exact congrArg (old a Subtype.val) (H.apply_zero p)
      | inr d =>
        exact (attachmentHomotopyPasting_cell a Subtype.val HOld L hcompat 0 d).trans
          (attachingDiskExtension_zero S hext a (h.comp a) Hatt d)
    map_one_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p =>
        change old a Subtype.val (H (1, p)) = old a Subtype.val (h p)
        exact congrArg (old a Subtype.val) (H.apply_one p)
      | inr d =>
        change T (1, cell a Subtype.val d) =
          attachingBackwardMap S hext a (h.comp a) Hatt (F (cell a Subtype.val d))
        rw [attachmentHomotopyPasting_cell, attachmentBaseMap_cell]
        exact (attachingBackwardMap_cell S hext a (h.comp a) Hatt d).symm }
  exact ContinuousMap.HomotopyEquiv.ofHomotopicSection C F ⟨HT.symm⟩

@[simp] theorem attachmentBaseMapEquivOfHomotopicId_toFun (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (h : C(P, P))
    (H : ContinuousMap.Homotopy (ContinuousMap.id P) h) :
    (attachmentBaseMapEquivOfHomotopicId S hS hext hfull a h H).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective h := rfl

/-- Change of the base by an actual homotopy equivalence induces an actual
homotopy equivalence on the attached spaces. Its forward map is precisely
the universal pushout map extending the original base map and disk maps. -/
def attachmentBaseChangeHomotopyEquiv (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (e.toFun ∘ a) Subtype.val) := by
  let f := attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun
  let g := attachmentBaseMap (e.toFun ∘ a) Subtype.val Subtype.val_injective e.invFun
  let h := attachmentBaseMap (e.invFun ∘ e.toFun ∘ a) Subtype.val
    Subtype.val_injective e.toFun
  let E := attachmentBaseMapEquivOfHomotopicId S hS hext hfull a
    (e.invFun.comp e.toFun) (Classical.choice e.left_inv).symm
  let D := attachmentBaseMapEquivOfHomotopicId S hS hext hfull (e.toFun.comp a)
    (e.toFun.comp e.invFun) (Classical.choice e.right_inv).symm
  have hE : E.toFun = g.comp f :=
    (attachmentBaseMap_comp a Subtype.val Subtype.val_injective e.toFun e.invFun).symm
  have hD : D.toFun = h.comp g :=
    (attachmentBaseMap_comp (e.toFun ∘ a) Subtype.val
      Subtype.val_injective e.invFun e.toFun).symm
  exact ContinuousMap.HomotopyEquiv.twoOfSixLeft f g h E hE D hD

@[simp] theorem attachmentBaseChangeHomotopyEquiv_toFun (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    (attachmentBaseChangeHomotopyEquiv S hS hext hfull a e).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun := rfl

@[simp] theorem attachmentBaseChangeHomotopyEquiv_old (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) (p : P) :
    attachmentBaseChangeHomotopyEquiv S hS hext hfull a e (old a Subtype.val p) =
      old (e.toFun ∘ a) Subtype.val (e p) := rfl

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped Classical

universe u
variable {A D P : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]

def attachmentBoundaryReparamForward (a : A → P) (i : A → D) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    C(Space a i, Space (a ∘ b.symm) Subtype.val) :=
  desc a i ⟨old (a ∘ b.symm) Subtype.val, old_continuous _ _⟩
    ⟨cell (a ∘ b.symm) Subtype.val, cell_continuous _ _⟩ (fun x => by
      change old (a ∘ b.symm) Subtype.val (a x) = cell (a ∘ b.symm) Subtype.val (i x)
      rw [← hb x, cell_boundary _ Subtype.val Subtype.val_injective]
      exact congrArg (old (a ∘ b.symm) Subtype.val)
        (congrArg a (b.symm_apply_apply x)).symm)

def attachmentBoundaryReparamBackward (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    C(Space (a ∘ b.symm) Subtype.val, Space a i) :=
  desc (a ∘ b.symm) Subtype.val ⟨old a i, old_continuous _ _⟩
    ⟨cell a i, cell_continuous _ _⟩ (fun x => by
      change old a i (a (b.symm x)) = cell a i x.val
      have hx : i (b.symm x) = x.val :=
        (hb (b.symm x)).symm.trans (congrArg Subtype.val (b.apply_symm_apply x))
      rw [← hx, cell_boundary a i hi])

def attachmentBoundaryReparam (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    Space a i ≃ₜ Space (a ∘ b.symm) Subtype.val where
  toFun := attachmentBoundaryReparamForward a i S b hb
  invFun := attachmentBoundaryReparamBackward a i hi S b hb
  left_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective a i z
    cases w with
    | inl p => rfl
    | inr d =>
      change desc _ _ _ _ _ (desc _ _ _ _ _ (cell a i d)) = cell a i d
      simp only [desc_cell, ContinuousMap.coe_mk]
  right_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective (a ∘ b.symm) Subtype.val z
    cases w with
    | inl p => rfl
    | inr d =>
      change desc _ _ _ _ _ (desc _ _ _ _ _ (cell (a ∘ b.symm) Subtype.val d)) = _
      simp only [desc_cell, ContinuousMap.coe_mk]
      rfl
  continuous_toFun := (attachmentBoundaryReparamForward a i S b hb).continuous
  continuous_invFun := (attachmentBoundaryReparamBackward a i hi S b hb).continuous

@[simp] theorem attachmentBoundaryReparam_old (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (p : P) :
    attachmentBoundaryReparam a i hi S b hb (old a i p) =
      old (a ∘ b.symm) Subtype.val p := rfl

@[simp] theorem attachmentBoundaryReparam_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (d : D) :
    attachmentBoundaryReparam a i hi S b hb (cell a i d) =
      cell (a ∘ b.symm) Subtype.val d := by
  change attachmentBoundaryReparamForward a i S b hb (cell a i d) = _
  unfold attachmentBoundaryReparamForward
  rw [desc_cell]
  rfl

@[simp] theorem attachmentBoundaryReparam_symm_old (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (p : P) :
    (attachmentBoundaryReparam a i hi S b hb).symm (old (a ∘ b.symm) Subtype.val p) =
      old a i p := rfl

@[simp] theorem attachmentBoundaryReparam_symm_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (d : D) :
    (attachmentBoundaryReparam a i hi S b hb).symm (cell (a ∘ b.symm) Subtype.val d) =
      cell a i d := by
  change attachmentBoundaryReparamBackward a i hi S b hb
    (cell (a ∘ b.symm) Subtype.val d) = _
  unfold attachmentBoundaryReparamBackward
  rw [desc_cell]
  rfl

end FiniteChains.RelativeAttachment

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable (J E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def diskFamilyBoundarySet : Set (DiskFamily J E) :=
  SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1})

omit [NormedSpace ℝ E] in
theorem diskFamilyBoundarySet_isClosed : IsClosed (diskFamilyBoundarySet J E) :=
  sigmaSubspace_isClosed _ (fun _ =>
    isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const)


def diskFamilyBoundaryHomeomorph : BoundaryFamily J E ≃ₜ diskFamilyBoundarySet J E :=
  (boundaryFamilyInclusion_isClosedEmbedding J E).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext d
      exact boundaryFamilyInclusion_range J E d))

omit [NormedSpace ℝ E] in
@[simp] theorem diskFamilyBoundaryHomeomorph_val (a : BoundaryFamily J E) :
    (diskFamilyBoundaryHomeomorph J E a).val = boundaryFamilyInclusion J E a := rfl

variable {J E}
variable {P K : Type u} [TopologicalSpace P] [TopologicalSpace K]

/-- The actual homotopy equivalence after attaching an arbitrary family
of disks along a homotopy equivalence of the old spaces. -/
def diskAttachmentBaseChangeHomotopyEquiv (r : C(BoundaryFamily J E, P))
    (e : ContinuousMap.HomotopyEquiv P K) :
    ContinuousMap.HomotopyEquiv (DiskAttachment r) (DiskAttachment (e.toFun ∘ r)) := by
  let S := diskFamilyBoundarySet J E
  let b := diskFamilyBoundaryHomeomorph J E
  have hb : ∀ a, (b a).val = boundaryFamilyInclusion J E a := fun _ => rfl
  have hi := (boundaryFamilyInclusion_isClosedEmbedding J E).injective
  let R₀ := attachmentBoundaryReparam r (boundaryFamilyInclusion J E) hi S b hb
  let R₁ := attachmentBoundaryReparam (e.toFun ∘ r) (boundaryFamilyInclusion J E) hi S b hb
  let a : C(S, P) := r.comp b.symm.toContinuousMap
  let H := attachmentBaseChangeHomotopyEquiv S (diskFamilyBoundarySet_isClosed J E)
    (diskFamilySubspace_hasHomotopyExtension E J)
    (diskFamilyFullCylinder_hasHomotopyExtension E J) a e
  exact (R₀.toHomotopyEquiv.trans H).trans R₁.symm.toHomotopyEquiv

@[simp] theorem diskAttachmentBaseChangeHomotopyEquiv_old
    (r : C(BoundaryFamily J E, P)) (e : ContinuousMap.HomotopyEquiv P K) (p : P) :
    diskAttachmentBaseChangeHomotopyEquiv r e (old r (boundaryFamilyInclusion J E) p) =
      old (e.toFun ∘ r) (boundaryFamilyInclusion J E) (e p) := rfl

@[simp] theorem diskAttachmentBaseChangeHomotopyEquiv_cell
    (r : C(BoundaryFamily J E, P)) (e : ContinuousMap.HomotopyEquiv P K)
    (d : DiskFamily J E) :
    diskAttachmentBaseChangeHomotopyEquiv r e (cell r (boundaryFamilyInclusion J E) d) =
      cell (e.toFun ∘ r) (boundaryFamilyInclusion J E) d := by
  simp only [diskAttachmentBaseChangeHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans,
    ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Homeomorph.toHomotopyEquiv, attachmentBoundaryReparam_cell,
    attachmentBaseChangeHomotopyEquiv_toFun]
  let R := attachmentBoundaryReparam (e.toFun ∘ r) (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl)
  exact (congrArg R.symm
    (attachmentBaseMap_cell (r.comp (diskFamilyBoundaryHomeomorph J E).symm.toContinuousMap)
      Subtype.val Subtype.val_injective e.toFun d)).trans
    (attachmentBoundaryReparam_symm_cell (e.toFun ∘ r) (boundaryFamilyInclusion J E)
      (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl) d)

/-- Moving all attaching maps through specified homotopies gives an actual
equivalence which is the identity on the old space. This permits cellular
representatives to be chosen after changing the base. -/
def diskAttachingHomotopyEquiv (r₀ r₁ : C(BoundaryFamily J E, P))
    (H : r₀.Homotopy r₁) :
    ContinuousMap.HomotopyEquiv (DiskAttachment r₀) (DiskAttachment r₁) := by
  let S := diskFamilyBoundarySet J E
  let b := diskFamilyBoundaryHomeomorph J E
  have hb : ∀ a, (b a).val = boundaryFamilyInclusion J E a := fun _ => rfl
  have hi := (boundaryFamilyInclusion_isClosedEmbedding J E).injective
  let R₀ := attachmentBoundaryReparam r₀ (boundaryFamilyInclusion J E) hi S b hb
  let R₁ := attachmentBoundaryReparam r₁ (boundaryFamilyInclusion J E) hi S b hb
  let E' := attachingHomotopyEquiv S (diskFamilyBoundarySet_isClosed J E)
    (diskFamilySubspace_hasHomotopyExtension E J)
    (diskFamilyFullCylinder_hasHomotopyExtension E J)
    (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
    (H.compContinuousMap b.symm.toContinuousMap)
  exact (R₀.toHomotopyEquiv.trans E').trans R₁.symm.toHomotopyEquiv

@[simp] theorem diskAttachingHomotopyEquiv_old (r₀ r₁ : C(BoundaryFamily J E, P))
    (H : r₀.Homotopy r₁) (p : P) :
    diskAttachingHomotopyEquiv r₀ r₁ H (old r₀ (boundaryFamilyInclusion J E) p) =
      old r₁ (boundaryFamilyInclusion J E) p := rfl

end FiniteChains.RelativeAttachment
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeAttachment
open scoped Topology Classical

variable {X J E : Type} [TopologicalSpace X]
  [NormedAddCommGroup E]
  (r : BoundaryFamily J E → X) (p : J → Prop)

def partitionFirstAttaching : BoundaryFamily {j : J // p j} E → X :=
  fun a => r ⟨a.1.val, a.2⟩

def partitionRestAttaching : BoundaryFamily {j : J // ¬p j} E →
    DiskAttachment (partitionFirstAttaching r p) :=
  fun a => old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
    (r ⟨a.1.val, a.2⟩)

abbrev PartitionAttachment := DiskAttachment (partitionRestAttaching r p)

def partitionDiskForget (s : J → Prop) :
    C(DiskFamily {j : J // s j} E, DiskFamily J E) where
  toFun d := ⟨d.1.val, d.2⟩
  continuous_toFun := continuous_sigma (fun j =>
    continuous_sigmaMk (σ := fun _ : J => ClosedUnitBall E) (i := j.val))

def partitionFirstInto :
    C(DiskAttachment (partitionFirstAttaching r p), DiskAttachment r) :=
  desc (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
    ⟨old r (boundaryFamilyInclusion J E), old_continuous _ _⟩
    ((⟨cell r (boundaryFamilyInclusion J E), cell_continuous _ _⟩ : C(DiskFamily J E, _)).comp
      (partitionDiskForget p))
    (fun a => (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      ⟨a.1.val, a.2⟩).symm)

def partitionFlatten : C(PartitionAttachment r p, DiskAttachment r) :=
  desc (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
    (partitionFirstInto r p)
    ((⟨cell r (boundaryFamilyInclusion J E), cell_continuous _ _⟩ : C(DiskFamily J E, _)).comp
      (partitionDiskForget (fun j => ¬p j)))
    (fun a => (cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      ⟨a.1.val, a.2⟩).symm)

@[simp] theorem partitionFlatten_old (x : X) :
    partitionFlatten r p
      (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) x)) =
      old r (boundaryFamilyInclusion J E) x := rfl

@[simp] theorem partitionFlatten_firstCell (d : DiskFamily {j // p j} E) :
    partitionFlatten r p
      (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d)) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  change partitionFirstInto r p
    (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) = _
  unfold partitionFirstInto
  rw [desc_cell]
  rfl

@[simp] theorem partitionFlatten_restCell (d : DiskFamily {j // ¬p j} E) :
    partitionFlatten r p
      (cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d) =
      cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩ := by
  unfold partitionFlatten
  rw [desc_cell]
  rfl

def partitionCellMap : C(DiskFamily J E, PartitionAttachment r p) where
  toFun d := if h : p d.1 then
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E)
        ⟨⟨d.1, h⟩, d.2⟩)
    else cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      ⟨⟨d.1, h⟩, d.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro j
    by_cases hj : p j
    · simp only [dif_pos hj]
      exact (old_continuous _ _).comp ((cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : {j : J // p j} => ClosedUnitBall E) (i := ⟨j, hj⟩)))
    · simp only [dif_neg hj]
      exact (cell_continuous _ _).comp
        (continuous_sigmaMk (σ := fun _ : {j : J // ¬p j} => ClosedUnitBall E) (i := ⟨j, hj⟩))

theorem partitionCellMap_boundary (a : BoundaryFamily J E) :
    old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
      (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) (r a)) =
      partitionCellMap r p (boundaryFamilyInclusion J E a) := by
  rcases a with ⟨j, a⟩
  by_cases hj : p j
  · simp only [partitionCellMap, ContinuousMap.coe_mk, boundaryFamilyInclusion, dif_pos hj]
    exact congrArg (old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E))
      (cell_boundary (partitionFirstAttaching r p) _
        (boundaryFamilyInclusion_isClosedEmbedding {j // p j} E).injective
        ⟨⟨j, hj⟩, a⟩).symm
  · simp only [partitionCellMap, ContinuousMap.coe_mk, boundaryFamilyInclusion, dif_neg hj]
    exact (cell_boundary (partitionRestAttaching r p) _
      (boundaryFamilyInclusion_isClosedEmbedding {j // ¬p j} E).injective
      ⟨⟨j, hj⟩, a⟩).symm

def partitionRegroup : C(DiskAttachment r, PartitionAttachment r p) :=
  desc r (boundaryFamilyInclusion J E)
    ((⟨old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E),
      old_continuous _ _⟩ : C(DiskAttachment (partitionFirstAttaching r p), _)).comp
        ⟨old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E),
          old_continuous _ _⟩)
    (partitionCellMap r p) (partitionCellMap_boundary r p)

@[simp] theorem partitionRegroup_old (x : X) :
    partitionRegroup r p (old r (boundaryFamilyInclusion J E) x) =
      old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (old (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) x) := rfl

@[simp] theorem partitionRegroup_firstCell (d : DiskFamily {j // p j} E) :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      old (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E)
        (cell (partitionFirstAttaching r p) (boundaryFamilyInclusion {j // p j} E) d) := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [partitionCellMap, ContinuousMap.coe_mk, dif_pos d.1.property]

@[simp] theorem partitionRegroup_restCell (d : DiskFamily {j // ¬p j} E) :
    partitionRegroup r p (cell r (boundaryFamilyInclusion J E) ⟨d.1.val, d.2⟩) =
      cell (partitionRestAttaching r p) (boundaryFamilyInclusion {j // ¬p j} E) d := by
  change desc _ _ _ _ _ (cell _ _ _) = _
  rw [desc_cell]
  simp only [partitionCellMap, ContinuousMap.coe_mk, dif_neg d.1.property]

/-- Regrouping preserves each disk point and every old point, with the
original quotient topologies on both sides. -/
def diskAttachmentPartitionHomeomorph : DiskAttachment r ≃ₜ PartitionAttachment r p where
  toFun := partitionRegroup r p
  invFun := partitionFlatten r p
  left_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective r (boundaryFamilyInclusion J E) z
    cases w with
    | inl x => rfl
    | inr d =>
        by_cases hd : p d.1
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_firstCell r p ⟨⟨d.1, hd⟩, d.2⟩)
        · exact (congrArg (partitionFlatten r p)
            (partitionRegroup_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)).trans
            (partitionFlatten_restCell r p ⟨⟨d.1, hd⟩, d.2⟩)
  right_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective (partitionRestAttaching r p)
      (boundaryFamilyInclusion {j // ¬p j} E) z
    cases w with
    | inl y =>
        obtain ⟨w, rfl⟩ := quotientMap_surjective (partitionFirstAttaching r p)
          (boundaryFamilyInclusion {j // p j} E) y
        cases w with
        | inl x => rfl
        | inr d => exact (congrArg (partitionRegroup r p)
            (partitionFlatten_firstCell r p d)).trans (partitionRegroup_firstCell r p d)
    | inr d => exact (congrArg (partitionRegroup r p)
        (partitionFlatten_restCell r p d)).trans (partitionRegroup_restCell r p d)
  continuous_toFun := (partitionRegroup r p).continuous
  continuous_invFun := (partitionFlatten r p).continuous

theorem partitionRestAttaching_continuous (hr : Continuous r) :
    Continuous (partitionRestAttaching r p) := by
  apply (old_continuous _ _).comp
  simp_all

end FiniteChains.RelativeAttachment
end

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

def roseAttaching (A : Type) : C(BoundaryFamily A (Fin 1 → ℝ), PUnit) :=
  ContinuousMap.const _ PUnit.unit

abbrev Rose (A : Type) := DiskAttachment (roseAttaching A)

def roseVertex (A : Type) : Rose A :=
  old (roseAttaching A) (boundaryFamilyInclusion A _) PUnit.unit

variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def nonTreeAttaching : C(BoundaryFamily {j : J // ¬T.isTree j} (Fin 1 → ℝ), TreeSpace r T) :=
  ⟨partitionRestAttaching r T.isTree, partitionRestAttaching_continuous r T.isTree hr⟩

/-- The concrete graph-to-rose equivalence. Its only combinatorial input is
the genuine spanning tree, whose contraction is constructed above. -/
def graphRoseHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (DiskAttachment r) (Rose {j : J // ¬T.isTree j}) :=
  (diskAttachmentPartitionHomeomorph r T.isTree).toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (nonTreeAttaching r hr T) (treeHomotopyEquivPUnit r T))

@[simp] theorem graphRoseHomotopyEquiv_old (v : V) :
    graphRoseHomotopyEquiv r hr T (old r (boundaryFamilyInclusion J _) v) =
      roseVertex {j : J // ¬T.isTree j} := rfl

@[simp] theorem graphRoseHomotopyEquiv_treeCell
    (d : DiskFamily {j : J // T.isTree j} (Fin 1 → ℝ)) :
    graphRoseHomotopyEquiv r hr T
      (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩) =
      roseVertex {j : J // ¬T.isTree j} := by
  change diskAttachmentBaseChangeHomotopyEquiv (nonTreeAttaching r hr T)
      (treeHomotopyEquivPUnit r T)
      (partitionRegroup r T.isTree (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩)) = _
  rw [partitionRegroup_firstCell r T.isTree d]
  exact diskAttachmentBaseChangeHomotopyEquiv_old (nonTreeAttaching r hr T)
    (treeHomotopyEquivPUnit r T)
    (cell (partitionFirstAttaching r T.isTree)
      (boundaryFamilyInclusion {j : J // T.isTree j} (Fin 1 → ℝ)) d)

@[simp] theorem graphRoseHomotopyEquiv_nonTreeCell
    (d : DiskFamily {j : J // ¬T.isTree j} (Fin 1 → ℝ)) :
    graphRoseHomotopyEquiv r hr T
      (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩) =
      cell (roseAttaching {j : J // ¬T.isTree j})
        (boundaryFamilyInclusion {j : J // ¬T.isTree j} _) d := by
  change diskAttachmentBaseChangeHomotopyEquiv (nonTreeAttaching r hr T)
      (treeHomotopyEquivPUnit r T)
      (partitionRegroup r T.isTree (cell r (boundaryFamilyInclusion J _) ⟨d.1.val, d.2⟩)) = _
  rw [partitionRegroup_restCell r T.isTree d]
  exact diskAttachmentBaseChangeHomotopyEquiv_cell (nonTreeAttaching r hr T)
    (treeHomotopyEquivPUnit r T) d

theorem graphRoseHomotopyEquiv_treePath (j : {j : J // T.isTree j}) (t : I) :
    graphRoseHomotopyEquiv r hr T (graphEdgePath r j.val t) =
      roseVertex {j : J // ¬T.isTree j} :=
  graphRoseHomotopyEquiv_treeCell r hr T ⟨j, graphDiskHomeomorph t⟩

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel Topology
open scoped Classical unitInterval

variable (α : Type)
    (L : Path (orderRoseBase PUnit) (orderRoseBase PUnit))
    (hsur : Function.Surjective L)
    (hfiber : ∀ s t : I, L s = L t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))

def roseDiskLoopMap : C(DiskFamily α (Fin 1 → ℝ),
    orderNerveRealization (Rose α)) where
  toFun d := roseCopyRealization d.1 (L (graphDiskHomeomorph.symm d.2))
  continuous_toFun := continuous_sigma (fun a =>
    (roseCopyRealization a).continuous.comp (L.continuous.comp graphDiskHomeomorph.symm.continuous))

def diskRoseToOrderRose : C(ClassicalGraphModel.Rose α, orderNerveRealization (Rose α)) :=
  desc (roseAttaching α) (boundaryFamilyInclusion α (Fin 1 → ℝ))
    (ContinuousMap.const _ (orderRoseBase α)) (roseDiskLoopMap α L) (by
      rintro ⟨a, b⟩
      rcases graphBoundary_cases b with rfl | rfl
      · change orderRoseBase α = roseCopyRealization a
          (L (graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryNeg)))
        rw [graphDiskHomeomorph_symm_neg, L.source, roseCopyRealization_base]
      · change orderRoseBase α = roseCopyRealization a
          (L (graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryPos)))
        rw [graphDiskHomeomorph_symm_pos, L.target, roseCopyRealization_base])

@[simp] theorem diskRoseToOrderRose_vertex :
    diskRoseToOrderRose α L (roseVertex α) = orderRoseBase α := rfl

@[simp] theorem diskRoseToOrderRose_cell (a : α) (d : ClosedUnitBall (Fin 1 → ℝ)) :
    diskRoseToOrderRose α L (cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, d⟩) =
      roseCopyRealization a (L (graphDiskHomeomorph.symm d)) := desc_cell ..

theorem diskRoseToOrderRose_interval (a : α) (t : I) :
    diskRoseToOrderRose α L
      (cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩) =
      roseCopyRealization a (L t) := by simp

theorem freshParameter_ne_endpoints
    (d : {d : DiskFamily α (Fin 1 → ℝ) // d ∉ Set.range (boundaryFamilyInclusion α _)}) :
    graphDiskHomeomorph.symm d.val.2 ≠ 0 ∧ graphDiskHomeomorph.symm d.val.2 ≠ 1 := by
  constructor
  · intro ht
    apply d.property
    refine ⟨⟨d.val.1, graphBoundaryNeg⟩, ?_⟩
    cases d with
    | mk d hd =>
      cases d with
      | mk a x =>
        dsimp at ht ⊢
        apply congrArg (Sigma.mk a)
        rw [← graphDiskHomeomorph_zero, ← ht, Homeomorph.apply_symm_apply]
  · intro ht
    apply d.property
    refine ⟨⟨d.val.1, graphBoundaryPos⟩, ?_⟩
    cases d with
    | mk d hd =>
      cases d with
      | mk a x =>
        dsimp at ht ⊢
        apply congrArg (Sigma.mk a)
        rw [← graphDiskHomeomorph_one, ← ht, Homeomorph.apply_symm_apply]

include hfiber in
theorem traversal_eq_base {t : I} (h : L t = orderRoseBase PUnit) : t = 0 ∨ t = 1 := by
  rcases hfiber t 0 (h.trans L.source.symm) with ht | ht | ht
  · simp_all
  · simp_all
  · simp_all

include hfiber in
theorem freshImage_ne_base
    (d : {d : DiskFamily α (Fin 1 → ℝ) // d ∉ Set.range (boundaryFamilyInclusion α _)}) :
    roseCopyRealization d.val.1 (L (graphDiskHomeomorph.symm d.val.2)) ≠ orderRoseBase α := by
  intro h
  have he  :=
    roseCopyRealization_injective d.val.1 (h.trans (roseCopyRealization_base d.val.1).symm)
  exact (traversal_eq_base L hfiber he).elim
    (freshParameter_ne_endpoints α d).1 (freshParameter_ne_endpoints α d).2

theorem diskRoseToOrderRose_fresh
    (d : {d : DiskFamily α (Fin 1 → ℝ) // d ∉ Set.range (boundaryFamilyInclusion α _)}) :
    diskRoseToOrderRose α L (Sum.inr d) =
      roseCopyRealization d.val.1 (L (graphDiskHomeomorph.symm d.val.2)) := rfl


def diskRoseOrderHomeomorphOfTraversal :
    ClassicalGraphModel.Rose α ≃ₜ orderNerveRealization (Rose α) := by
  let e := Equiv.ofBijective (diskRoseToOrderRose α L)
    (by
      constructor
      · intro x y h
        cases x with
        | inl x =>
          cases y with
          | inl y => exact congrArg Sum.inl (Subsingleton.elim x y)
          | inr y =>
            have hy : diskRoseToOrderRose α L (Sum.inl x) = orderRoseBase α := rfl
            rw [hy, diskRoseToOrderRose_fresh] at h
            exact (freshImage_ne_base α L hfiber y h.symm).elim
        | inr x =>
          cases y with
          | inl y =>
            have hy : diskRoseToOrderRose α L (Sum.inl y) = orderRoseBase α := rfl
            rw [hy, diskRoseToOrderRose_fresh] at h
            exact (freshImage_ne_base α L hfiber x h).elim
          | inr y =>
            rw [diskRoseToOrderRose_fresh, diskRoseToOrderRose_fresh] at h
            by_cases ha : x.val.1 = y.val.1
            · rw [← ha] at h
              have ht := roseCopyRealization_injective x.val.1 h
              rcases hfiber _ _ ht with ht | ht | ht
              · apply congrArg Sum.inr
                apply Subtype.ext
                exact Sigma.ext ha (heq_of_eq (graphDiskHomeomorph.symm.injective ht))
              · exact ((freshParameter_ne_endpoints α x).1 ht.1).elim
              · exact ((freshParameter_ne_endpoints α x).2 ht.1).elim
            · have hx := (roseCopyRealization_intersection ha _ _ h).1
              exact ((traversal_eq_base L hfiber hx).elim
                (freshParameter_ne_endpoints α x).1 (freshParameter_ne_endpoints α x).2).elim
      · intro x
        rcases orderRoseRealization_cases x with rfl | ⟨a, u, rfl⟩
        · exact ⟨roseVertex α, diskRoseToOrderRose_vertex α L⟩
        · obtain ⟨t, rfl⟩ := hsur u
          exact ⟨cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩,
            diskRoseToOrderRose_interval α L a t⟩)
  refine { toEquiv := e
           continuous_toFun := (diskRoseToOrderRose α L).continuous
           continuous_invFun := ?_ }
  apply (orderRoseRealization_continuous_iff e.symm).mpr
  intro a
  have hq : IsQuotientMap L := L.continuous.isClosedMap.isQuotientMap L.continuous hsur
  apply hq.continuous_iff.mpr
  have he : (e.symm ∘ roseCopyRealization a) ∘ L =
      fun t => cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩ := by
    funext t
    apply e.injective
    dsimp only [Function.comp_apply]
    rw [e.apply_symm_apply]
    exact (diskRoseToOrderRose_interval α L a t).symm
  rw [he]
  exact (cell_continuous (roseAttaching α) _).comp
    ((continuous_sigmaMk («σ» := fun _ : α => ClosedUnitBall (Fin 1 → ℝ)) (i := a)).comp
      graphDiskHomeomorph.continuous)

theorem diskRoseOrderHomeomorphOfTraversal_interval (a : α) (t : I) :
    diskRoseOrderHomeomorphOfTraversal α L hsur hfiber
      (cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩) =
      roseCopyRealization a (L t) := diskRoseToOrderRose_interval α L a t

@[simp] theorem diskRoseOrderHomeomorphOfTraversal_vertex :
    diskRoseOrderHomeomorphOfTraversal α L hsur hfiber (roseVertex α) = orderRoseBase α := rfl

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel
open scoped Classical unitInterval

def roseRank : Rose PUnit → ℕ
  | .base => 0
  | .mid _ => 0
  | .edg _ _ => 1

theorem roseRank_strictMono : StrictMono roseRank := by
  intro p q hpq
  have hn := ne_of_lt hpq
  have hl := hpq.le
  change Rose.le p q at hl
  cases p <;> cases q <;> simp_all [Rose.le, roseRank]

def roseFourCycle : FinitePosetCycle (Rose PUnit) 2 where
  positive := by decide
  vertex := roseFourVertexEquiv
  consecutive i := by
    change Rose.le (roseFourVertex i.castSucc) (roseFourVertex i.succ) ∨
      Rose.le (roseFourVertex i.succ) (roseFourVertex i.castSucc)
    fin_cases i <;> simp [roseFourVertex, Rose.le]
  closing := by
    change Rose.le (roseFourVertex (Fin.last 3)) (roseFourVertex 0) ∨
      Rose.le (roseFourVertex 0) (roseFourVertex (Fin.last 3))
    simp [roseFourVertex, Rose.le]
  edges a b hne hab := by
    obtain ⟨i, rfl⟩ := roseFourVertex_surjective a
    obtain ⟨j, rfl⟩ := roseFourVertex_surjective b
    change Rose.le (roseFourVertex i) (roseFourVertex j) ∨
      Rose.le (roseFourVertex j) (roseFourVertex i) at hab
    fin_cases i <;> fin_cases j <;>
      simp_all [roseFourVertexEquiv, roseFourVertex, Rose.le, Fin.exists_fin_succ]
  height := roseRank
  height_strict := roseRank_strictMono
  height_le p := by cases p <;> simp [roseRank]

def orderRoseTraversal : Path (orderRoseBase PUnit) (orderRoseBase PUnit) :=
  roseFourCycle.traversal

theorem orderRoseTraversal_surjective : Function.Surjective orderRoseTraversal :=
  roseFourCycle.traversal_surjective

theorem orderRoseTraversal_fiber (s t : I) (h : orderRoseTraversal s = orderRoseTraversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
  roseFourCycle.traversal_fiber s t h

/-- No extra traversal, injectivity, or topology premise remains in this map. -/
def orderRoseRealizationHomeomorph (α : Type) :
    orderNerveRealization (Rose α) ≃ₜ ClassicalGraphModel.Rose α :=
  (diskRoseOrderHomeomorphOfTraversal α orderRoseTraversal
    orderRoseTraversal_surjective orderRoseTraversal_fiber).symm

@[simp] theorem orderRoseRealizationHomeomorph_base (α : Type) :
    orderRoseRealizationHomeomorph α (orderRoseBase α) = roseVertex α := by
  apply (orderRoseRealizationHomeomorph α).symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem orderRoseRealizationHomeomorph_interval {α : Type} (a : α) (t : I) :
    orderRoseRealizationHomeomorph α (roseCopyRealization a (orderRoseTraversal t)) =
      cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩ := by
  apply (orderRoseRealizationHomeomorph α).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact (diskRoseOrderHomeomorphOfTraversal_interval α orderRoseTraversal
    orderRoseTraversal_surjective orderRoseTraversal_fiber a t).symm

end FiniteChains.PresModel

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)

def coneRadial (x : P) : (orderCx Q).E := ⟨(c, f x), hc x⟩
def coneEdgeTriangle (e : (orderCx P).E) : (orderCx Q).F :=
  ⟨(c, f e.1.1, f e.1.2), hc _, hf e.2⟩
def coneEdgeChain : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((orderCx Q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneEdgeTriangle f hf c hc e) (1 : ℤ))

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- Restore the deleted all-positive corner of the cube quotient. -/
def positiveCorner : QCube A :=
  ⟨∅, 0, by simp [IsSimplex], fun _ _ => rfl⟩

/-- The actual surface inclusion in the full cube quotient. -/
def surfaceFullCube (σ : NeSpx A) : QCube A := (posQCube σ).val

theorem surfaceFullCube_monotone : Monotone (surfaceFullCube A) :=
  posQCube_monotone

theorem positiveCorner_le_surface (σ : NeSpx A) :
    positiveCorner A ≤ surfaceFullCube A σ :=
  ⟨Finset.empty_subset _, fun _ _ => rfl⟩

/-- Every actual surface loop contracts through the restored positive corner. -/
theorem surfaceFullCube_loop_null {σ : NeSpx A}
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ σ) :
    Htpy (orderCx (QCube A)) (surfaceFullCube A σ) (surfaceFullCube A σ)
      (mapPath (orderCxMap (surfaceFullCube A) (surfaceFullCube_monotone A)) p) [] :=
  htpy_nil_mapPath_of_const_le (surfaceFullCube_monotone A) (surfaceFullCube_monotone A)
    (fun _ => le_refl _) (positiveCorner A) (positiveCorner_le_surface A) hp

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The explicit positive-corner fan on a finite surface edge chain. -/
def surfaceCornerFan :
    ((orderCx (NeSpx A)).E →₀ ℤ) →ₗ[ℤ] ((orderCx (QCube A)).F →₀ ℤ) :=
  coneEdgeChain (surfaceFullCube A) (surfaceFullCube_monotone A)
    (positiveCorner A) (positiveCorner_le_surface A)

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
  (f : P → Q) (hf : IsPosetCover f) (g : R → Q) (hg : Monotone g)

def strictPullbackOriginal :
    Hom (strictOrderCx (PosetCoverPullback f g)) (orderCx P) :=
  (orderCxMap (posetPullbackOriginal f g) (posetPullbackOriginal_monotone f g)).comp
    (strictOrderIncl _)

def strictPullbackProjection :
    Hom (strictOrderCx (PosetCoverPullback f g)) (strictOrderCx R) :=
  strictOrderCxMap (posetPullbackProjection f g) (hf.pullback g hg).strictMono

omit [PartialOrder Q] in
theorem pullback_lt {a b : PosetCoverPullback f g}
    (hp : a.1.1 ≤ b.1.1) (hr : a.1.2 < b.1.2) : a < b := lt_iff_le_not_ge.mpr ⟨⟨hp, hr.le⟩, fun h => (not_le_of_gt hr) h.2⟩

variable {K : Complex2.{u}} (r : Hom K (orderCx P)) (s : Hom K (strictOrderCx R))
  (h : (orderCxMap f hf.mono).comp r =
    (orderCxMap g hg).comp ((strictOrderIncl R).comp s))

def strictPullbackVertex (a : K.V) : PosetCoverPullback f g :=
  ⟨(r.onV a, s.onV a), congrArg (fun k : Hom K (orderCx Q) => k.onV a) h⟩

def strictPullbackEdge (e : K.E) : StrictOrdEdge (PosetCoverPullback f g) := by
  have he := congrArg (fun k : Hom K (orderCx Q) => k.onE e) h
  let a : PosetCoverPullback f g :=
    ⟨((r.onE e).1.1, (s.onE e).1.1), congrArg (fun x : OrdEdge Q => x.1.1) he⟩
  let b : PosetCoverPullback f g :=
    ⟨((r.onE e).1.2, (s.onE e).1.2), congrArg (fun x : OrdEdge Q => x.1.2) he⟩
  exact ⟨(a, b), pullback_lt f g (r.onE e).2 (s.onE e).2⟩

def strictPullbackFace (t : K.F) : StrictOrdTri (PosetCoverPullback f g) := by
  have ht := congrArg (fun k : Hom K (orderCx Q) => k.onF t) h
  let a : PosetCoverPullback f g :=
    ⟨((r.onF t).1.1, (s.onF t).1.1), congrArg (fun x : OrdTri Q => x.1.1) ht⟩
  let b : PosetCoverPullback f g :=
    ⟨((r.onF t).1.2.1, (s.onF t).1.2.1), congrArg (fun x : OrdTri Q => x.1.2.1) ht⟩
  let c : PosetCoverPullback f g :=
    ⟨((r.onF t).1.2.2, (s.onF t).1.2.2), congrArg (fun x : OrdTri Q => x.1.2.2) ht⟩
  exact ⟨(a, b, c), pullback_lt f g (r.onF t).2.1 (s.onF t).2.1,
    pullback_lt f g (r.onF t).2.2 (s.onF t).2.2⟩

theorem strictPullbackEdge_first (e : K.E) :
    (strictPullbackOriginal f g).onE (strictPullbackEdge f hf g hg r s h e) = r.onE e := rfl

theorem strictPullbackEdge_second (e : K.E) :
    (strictPullbackProjection f hf g hg).onE (strictPullbackEdge f hf g hg r s h e) =
      s.onE e := rfl

theorem strictPullbackFace_first (t : K.F) :
    (strictPullbackOriginal f g).onF (strictPullbackFace f hf g hg r s h t) = r.onF t := rfl

theorem strictPullbackFace_second (t : K.F) :
    (strictPullbackProjection f hf g hg).onF (strictPullbackFace f hf g hg r s h t) =
      s.onF t := rfl

theorem list_eq_of_two_maps {A B C : Type*} (p : A → B) (q : A → C)
    (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (l m : List A) (hp : l.map p = m.map p) (hq : l.map q = m.map q) : l = m := by
  induction l generalizing m with
  | nil => simp_all
  | cons x l ih =>
      cases m with
      | nil => cases hp
      | cons y m =>
          obtain ⟨hp0, hp1⟩ := List.cons.inj hp
          obtain ⟨hq0, hq1⟩ := List.cons.inj hq
          exact congrArg₂ List.cons (hi x y hp0 hq0) (ih m hp1 hq1)

theorem pullback_germ_ext
    (x y : (strictOrderCx (PosetCoverPullback f g)).E × Bool)
    (hp : ((strictPullbackOriginal f g).onE x.1, x.2) =
      ((strictPullbackOriginal f g).onE y.1, y.2))
    (hq : ((strictPullbackProjection f hf g hg).onE x.1, x.2) =
      ((strictPullbackProjection f hf g hg).onE y.1, y.2)) : x = y := by
  have hb  := congrArg (fun e : OrdEdge P × Bool => e.2) hp
  refine Prod.ext ?_ hb
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun e : OrdEdge P × Bool => e.1.1.1) hp)
      (congrArg (fun e : StrictOrdEdge R × Bool => e.1.1.1) hq)
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun e : OrdEdge P × Bool => e.1.1.2) hp)
      (congrArg (fun e : StrictOrdEdge R × Bool => e.1.1.2) hq)

/-- Two genuinely commuting cellular maps produce a cellular map into the
actual ordered fibre product. Its attaching paths follow from both projections. -/
def strictOrderPullbackHom :
    Hom K (strictOrderCx (PosetCoverPullback f g)) where
  onV := strictPullbackVertex f hf g hg r s h
  onE := strictPullbackEdge f hf g hg r s h
  onF := strictPullbackFace f hf g hg r s h
  src_onE e := by
    apply Subtype.ext
    exact Prod.ext (r.src_onE e) (s.src_onE e)
  tgt_onE e := by
    apply Subtype.ext
    exact Prod.ext (r.tgt_onE e) (s.tgt_onE e)
  base_onF t := by
    apply Subtype.ext
    exact Prod.ext (r.base_onF t) (s.base_onF t)
  att_onF t := by
    apply list_eq_of_two_maps
      (fun e => ((strictPullbackOriginal f g).onE e.1, e.2))
      (fun e => ((strictPullbackProjection f hf g hg).onE e.1, e.2))
      (pullback_germ_ext f hf g hg)
    · rw [← (strictPullbackOriginal f g).att_onF]
      rw [strictPullbackFace_first]
      simpa only [List.map_map, Function.comp_def, strictPullbackEdge_first]
        using r.att_onF t
    · rw [← (strictPullbackProjection f hf g hg).att_onF]
      rw [strictPullbackFace_second]
      simpa only [List.map_map, Function.comp_def, strictPullbackEdge_second]
        using s.att_onF t

end FiniteChains.Comb
end

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}


/-- The actual quotient projection is a poset covering, before removing any chambers. -/
theorem qProjCube_isPosetCover : IsPosetCover (qProjCube (A := A)) where
  mono := (by
    intro p q h
    refine ⟨h.1, fun w hw => ?_⟩
    have hwp  := fun hc => hw (h.1 hc)
    rw [qProjCube_sgn_of_not_mem hwp, qProjCube_sgn_of_not_mem hw]
    exact (phi_rep_eq_of_inChamber (inChamber_rep_of_le h) hw).symm)
  surj c := exists_zOld_qProjCube c
  up _ _ h := existsUnique_up_old h
  down _ _ h := existsUnique_down_old h

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Every cellular two-cycle in the actual Davis complex is the boundary of a finitely
 supported cellular three-chain. This keeps the three-cells of the full nerve. -/
theorem exists_cellular_bdry3_of_cycle_davis (A : CommRel V)
    (z : OrdTri (Sph A) →₀ ℤ) (hz : Comb.bdry2 (orderCx (Sph A)) z = 0) :
    ∃ y : OrdTet (Sph A) →₀ ℤ, ordBoundary3 y = z := by
  obtain ⟨y, hy, hdy⟩ := exists_bdry_eq_of_cycle_davis A (ordNerveChain2_mem_inc z)
    ((ordNerveChain2_cycle_iff z).mpr hz)
  refine ⟨decodeOrdNerve3 y, ?_⟩
  apply ordNerveChain2_injective
  rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hy,
    ← lengthProjection_bdry, hdy, ordNerveChain2_lengthProjection]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- Degree-two exactness in the actual path-class universal cover, retaining its full
 three-cell boundary. No desired asphericity or homology premise is assumed. -/
theorem exists_universal_bdry3_of_cycle_davis (A : CommRel V) (a : Sph A)
    (z : UF (orderCx (QCube A)) (qProjCube a) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (QCube A)) (qProjCube a)) z = 0) :
    ∃ y : UOrdTet (QCube A) (qProjCube a) →₀ ℤ, uOrdBoundary3 y = z :=
  exists_uOrdBoundary3_of_cover_exact qProjCube_isPosetCover a
    (isConnected_davis A) (simplyConnected_davis A)
    (exists_cellular_bdry3_of_cycle_davis A) z hz

/-- The same exactness at every base vertex of the quotient. -/
theorem exists_universal_bdry3_of_cycle_qCube (A : CommRel V) (b : QCube A)
    (z : UF (orderCx (QCube A)) b →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (QCube A)) b) z = 0) :
    ∃ y : UOrdTet (QCube A) b →₀ ℤ, uOrdBoundary3 y = z := by
  obtain ⟨a, rfl⟩ := qProjCube_isPosetCover.surj b
  exact exists_universal_bdry3_of_cycle_davis A a z hz

end FiniteChains.Davis

namespace FiniteChains.PresModel
open scoped Classical
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

instance relatorCircle_finite : Finite (RelatorCircle w j) := by
  let f : RelatorCircle w j → Fin (w j).length × CPos :=
    fun x => (⟨x.val.2.1, x.property.2⟩, x.val.2.2)
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · grind
  · grind

theorem relatorCircle_nonempty (hw : w j ≠ []) : Nonempty (RelatorCircle w j) := by
  have hn  := List.length_pos_of_ne_nil hw
  exact ⟨⟨TCirc.pt w j 0 CPos.cor, rfl, hn⟩⟩

end FiniteChains.PresModel

section
open scoped Classical unitInterval
open Set Topology
namespace FiniteChains.PresModel
open Comb RelativeAttachment

def cPosCyclicIndex : CPos ≃ Fin 4 where
  toFun
    | .cor => 0
    | .cedgL => 1
    | .cmid => 2
    | .cedgR => 3
  invFun i := ![CPos.cor, CPos.cedgL, CPos.cmid, CPos.cedgR] i
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

variable {A J : Type} (w : J → List (A × Bool)) (j : J)

def relatorCircleProductEquiv : RelatorCircle w j ≃ Fin (w j).length × CPos where
  toFun x := (⟨x.val.2.1, x.property.2⟩, x.val.2.2)
  invFun x := relatorCirclePoint w j x.1 x.2
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext x.property.1.symm rfl
  right_inv _ := rfl

def relatorCircleIndexEquiv : RelatorCircle w j ≃ Fin ((w j).length * 4) :=
  (relatorCircleProductEquiv w j).trans
    ((Equiv.prodCongr (Equiv.refl _) cPosCyclicIndex).trans finProdFinEquiv)

variable (hn : 0 < (w j).length)

theorem relatorCircleIndex_symm_pair (k : Fin (w j).length) (t : Fin 4) :
    (relatorCircleIndexEquiv w j).symm (finProdFinEquiv (k, t)) =
      relatorCirclePoint w j k (cPosCyclicIndex.symm t) := by
  apply (relatorCircleIndexEquiv w j).injective
  rw [Equiv.apply_symm_apply]
  change finProdFinEquiv (k, t) = finProdFinEquiv (k, cPosCyclicIndex (cPosCyclicIndex.symm t))
  rw [Equiv.apply_symm_apply]

def relatorCircleSuccessor (x : RelatorCircle w j) : RelatorCircle w j :=
  let k : Fin (w j).length := ⟨x.val.2.1, x.property.2⟩
  match x.val.2.2 with
  | .cor => relatorCirclePoint w j k .cedgL
  | .cedgL => relatorCirclePoint w j k .cmid
  | .cmid => relatorCirclePoint w j k .cedgR
  | .cedgR => relatorCirclePoint w j
      ⟨(k.val + 1) % (w j).length, Nat.mod_lt _ hn⟩ .cor

theorem relatorCircleSuccessor_comparable (x : RelatorCircle w j) :
    x ≤ relatorCircleSuccessor w j hn x ∨ relatorCircleSuccessor w j hn x ≤ x := by
  rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
  change j' = j at hj
  subst j'
  cases t
  · exact Or.inl (TCirc.cor_le_cedgL w hk)
  · exact Or.inl (TCirc.cmid_le_cedgR w hk)
  · exact Or.inr (TCirc.cmid_le_cedgL w hk)
  · exact Or.inr (TCirc.cor_csucc_le_cedgR w hk)

theorem relatorCircle_le_neighbors (a b : RelatorCircle w j) (hne : a ≠ b) (hab : a ≤ b) :
    relatorCircleSuccessor w j hn a = b ∨ relatorCircleSuccessor w j hn b = a := by
  rcases hab with he | he
  · exact (hne (Subtype.ext he)).elim
  rcases a with ⟨⟨ja, ka, ta⟩, hja, hka⟩
  rcases b with ⟨⟨jb, kb, tb⟩, hjb, hkb⟩
  change ja = j at hja
  change jb = j at hjb
  subst ja
  subst jb
  obtain ⟨_, _, ht⟩ := he
  rcases ht with ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩ |
    ⟨rfl, rfl, hk⟩ | ⟨rfl, rfl, hk⟩
  · subst kb
    exact Or.inl rfl
  · subst kb
    exact Or.inr rfl
  · subst kb
    exact Or.inl rfl
  · subst ka
    exact Or.inr rfl


theorem relatorCircleSuccessor_index (x : RelatorCircle w j) :
    (relatorCircleIndexEquiv w j (relatorCircleSuccessor w j hn x)).val =
      if (relatorCircleIndexEquiv w j x).val + 1 < (w j).length * 4 then
        (relatorCircleIndexEquiv w j x).val + 1 else 0 := by
  rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
  change j' = j at hj
  subst j'
  change k < (w j).length at hk
  cases t
  · change 1 + 4 * k = if 0 + 4 * k + 1 < (w j).length * 4 then 0 + 4 * k + 1 else 0
    split_ifs <;> omega
  · change 3 + 4 * k = if 2 + 4 * k + 1 < (w j).length * 4 then 2 + 4 * k + 1 else 0
    split_ifs <;> omega
  · change 2 + 4 * k = if 1 + 4 * k + 1 < (w j).length * 4 then 1 + 4 * k + 1 else 0
    split_ifs <;> omega
  · change 0 + 4 * ((k + 1) % (w j).length) =
      if 3 + 4 * k + 1 < (w j).length * 4 then 3 + 4 * k + 1 else 0
    by_cases hnext : k + 1 < (w j).length
    · rw [Nat.mod_eq_of_lt hnext]
      split_ifs <;> omega
    · have he : k + 1 = (w j).length := by omega
      rw [he, Nat.mod_self]
      split_ifs <;> omega

def relatorCircleSize : ℕ := (w j).length * 4 - 2

include hn in
theorem relatorCircleSize_add_two : relatorCircleSize w j + 2 = (w j).length * 4 := by
  dsimp [relatorCircleSize]
  omega

def relatorCircleEnumeration : Fin (relatorCircleSize w j + 2) ≃ RelatorCircle w j :=
  (finCongr (relatorCircleSize_add_two w j hn)).trans (relatorCircleIndexEquiv w j).symm

theorem relatorCircleEnumeration_index (i : Fin (relatorCircleSize w j + 2)) :
    (relatorCircleIndexEquiv w j (relatorCircleEnumeration w j hn i)).val = i.val := by
  change (relatorCircleIndexEquiv w j
    ((relatorCircleIndexEquiv w j).symm (Fin.cast (relatorCircleSize_add_two w j hn) i))).val = i.val
  rw [Equiv.apply_symm_apply]
  rfl

theorem relatorCircleEnumeration_next (i : Fin (relatorCircleSize w j + 1)) :
    relatorCircleSuccessor w j hn (relatorCircleEnumeration w j hn i.castSucc) =
      relatorCircleEnumeration w j hn i.succ := by
  apply (relatorCircleIndexEquiv w j).injective
  ext
  rw [relatorCircleSuccessor_index, relatorCircleEnumeration_index, relatorCircleEnumeration_index]
  have hi := i.isLt
  have hN := relatorCircleSize_add_two w j hn
  change (if i.val + 1 < (w j).length * 4 then i.val + 1 else 0) = i.val + 1
  rw [if_pos (by omega)]

theorem relatorCircleEnumeration_last_next :
    relatorCircleSuccessor w j hn
      (relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1))) =
        relatorCircleEnumeration w j hn 0 := by
  apply (relatorCircleIndexEquiv w j).injective
  ext
  rw [relatorCircleSuccessor_index, relatorCircleEnumeration_index, relatorCircleEnumeration_index]
  have hN := relatorCircleSize_add_two w j hn
  simp_all

theorem relatorCircle_next_edge (a : RelatorCircle w j) :
    (∃ i : Fin (relatorCircleSize w j + 1),
      a = relatorCircleEnumeration w j hn i.castSucc ∧
        relatorCircleSuccessor w j hn a = relatorCircleEnumeration w j hn i.succ) ∨
    (a = relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1)) ∧
      relatorCircleSuccessor w j hn a = relatorCircleEnumeration w j hn 0) := by
  obtain ⟨k, rfl⟩ := (relatorCircleEnumeration w j hn).surjective a
  refine Fin.lastCases ?_ ?_ k
  · exact Or.inr ⟨rfl, relatorCircleEnumeration_last_next w j hn⟩
  · intro i
    exact Or.inl ⟨i, rfl, relatorCircleEnumeration_next w j hn i⟩

def relatorCircleCycle : FinitePosetCycle (RelatorCircle w j) (relatorCircleSize w j) where
  positive := by dsimp [relatorCircleSize]; omega
  vertex := relatorCircleEnumeration w j hn
  consecutive i := by
    have h := relatorCircleSuccessor_comparable w j hn (relatorCircleEnumeration w j hn i.castSucc)
    rwa [relatorCircleEnumeration_next] at h
  closing := by
    have h := relatorCircleSuccessor_comparable w j hn
      (relatorCircleEnumeration w j hn (Fin.last (relatorCircleSize w j + 1)))
    rwa [relatorCircleEnumeration_last_next] at h
  edges a b hne hab := by
    rcases (show relatorCircleSuccessor w j hn a = b ∨ relatorCircleSuccessor w j hn b = a by
      rcases hab with hab | hba
      · exact relatorCircle_le_neighbors w j hn a b hne hab
      · exact (relatorCircle_le_neighbors w j hn b a hne.symm hba).symm) with h | h
    · rcases relatorCircle_next_edge w j hn a with ⟨i, ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨i, Or.inl ⟨ha, h.symm.trans hb⟩⟩
      · exact Or.inr (Or.inl ⟨ha, h.symm.trans hb⟩)
    · rcases relatorCircle_next_edge w j hn b with ⟨i, hb, ha⟩ | ⟨hb, ha⟩
      · exact Or.inl ⟨i, Or.inr ⟨hb, h.symm.trans ha⟩⟩
      · exact Or.inr (Or.inr ⟨hb, h.symm.trans ha⟩)
  height x := circleDimension w x.val
  height_strict := fun _ _ h => circleDimension_strictMono w h
  height_le x := circleDimension_le_one w x.val

def relatorCircleTraversal := (relatorCircleCycle w j hn).traversal

/-- The actual valid relator-circle realization, with the explicit
once-around parametrization retained by the exported traversal lemmas. -/
def relatorCircleBoundaryHomeomorph :
    orderNerveRealization (RelatorCircle w j) ≃ₜ UnitBoundary (Fin 2 → ℝ) :=
  (relatorCircleCycle w j hn).boundaryHomeomorph

end FiniteChains.PresModel
end

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (ψ : G →* Pi1 Y (f.onV T.root))

/-- Every actual lift of the image of a vertex has a receiving-group sheet. -/
theorem receiverVertex_fiber_surjective (hψ : Function.Surjective ψ)
    (a : K.V) (v : UV Y (f.onV T.root)) (hv : endV v = f.onV a) :
    ∃ g : G, receiverVertex T f ψ g a = v := by
  have he  :=
    (mappedTreeReference_end T f a).trans hv.symm
  obtain ⟨d, hd, _⟩ := (isRegular_univProj).simply_transitive
    (mappedTreeReference T f a) v he
  obtain ⟨g, rfl⟩ := hψ d
  exact ⟨g, hd⟩

theorem receiverVertex_fiber_injective (hψ : Function.Injective ψ) (a : K.V) :
    Function.Injective (fun g : G => receiverVertex T f ψ g a) := by
  intro g h hgh
  apply hψ
  obtain ⟨d, _, hd⟩ := (isRegular_univProj).simply_transitive
    (mappedTreeReference T f a) (receiverVertex T f ψ g a)
    ((mappedTreeReference_end T f a).trans (receiverVertex_end T f ψ g a).symm)
  exact (hd (ψ g) rfl).trans (hd (ψ h) hgh.symm).symm

/-- The based-face coordinate is also exact, not merely a homology class. -/
theorem receiverFace_fiber_surjective (hψ : Function.Surjective ψ)
    (t : K.F) (v : UF Y (f.onV T.root)) (hv : v.1.2 = f.onF t) :
    ∃ g : G, receiverFace T f ψ g t = v := by
  have he  :=
    v.2.trans ((congrArg Y.base hv).trans (f.base_onF t))
  obtain ⟨g, hg⟩ := receiverVertex_fiber_surjective T f ψ hψ (K.base t) v.1.1 he
  refine ⟨g, Subtype.ext ?_⟩
  exact Prod.ext hg hv.symm

end FiniteChains.Comb.ReceivedTree

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → Rose α) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = aFun w x.val)

/-- The actual lifted midpoint belonging to a specified actual attaching letter. -/
def roseCoverLetterMidpoint (k : Fin (w j).length) (a : α × Bool)
    (ha : (w j)[k.val]? = some a) : roseCoverMidpoints f :=
  ⟨(m (relatorCirclePoint w j k CPos.cmid), a.1),
    (hp _).trans (aFun_pt_cmid_of_get w ha)⟩

/-- Each actual lifted letter chain is the appropriately signed genuine generator chain. -/
theorem roseCoverLetterChain_map (k : Fin (w j).length) (a : α × Bool)
    (ha : (w j)[k.val]? = some a) :
    chain1 (strictOrderCxMap m hm) (relatorCircleLetterChain w j k) =
      (if a.2 then (1 : ℤ) else -1) •
        roseCoverGeneratorChain f hf (roseCoverLetterMidpoint w j f m hp k a ha) := by
  let p := roseCoverLetterMidpoint w j f m hp k a ha
  let M := strictOrderCxMap m hm
  have h1 : M.onE (relatorCircleEdge1 w j k) = roseCoverMidpointEndEdge f hf p (!a.2) := by
    apply hf.strictEdgeLiftFrom_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cmid_of_get w ha))
        ((hp _).trans (aFun_pt_cedgL_of_get w ha))
    · rfl
  have h2 : M.onE (relatorCircleEdge2 w j k) = roseCoverMidpointEndEdge f hf p a.2 := by
    apply hf.strictEdgeLiftFrom_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cmid_of_get w ha))
        ((hp _).trans (aFun_pt_cedgR_of_get w ha))
    · rfl
  have h0 : M.onE (relatorCircleEdge0 w j k) = roseCoverMidpointBaseEdge f hf p (!a.2) := by
    apply hf.strictEdgeLiftTo_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cor w j k.val))
        ((hp _).trans (aFun_pt_cedgL_of_get w ha))
    · simpa only [M, strictOrderCxMap, relatorCircleEdge0, relatorCircleEdge1] using
        congrArg (fun e : StrictOrdEdge P => e.val.2) h1
  have h3 : M.onE (relatorCircleEdge3 w j k) = roseCoverMidpointBaseEdge f hf p a.2 := by
    apply hf.strictEdgeLiftTo_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cor w j (relatorCircleNext w j k).val))
        ((hp _).trans (aFun_pt_cedgR_of_get w ha))
    · simpa only [M, strictOrderCxMap, relatorCircleEdge2, relatorCircleEdge3] using
        congrArg (fun e : StrictOrdEdge P => e.val.2) h2
  unfold relatorCircleLetterChain
  rw (config := { transparency := .default }) [map_sub, map_add, map_sub]
  change Finsupp.mapDomain M.onE (Finsupp.single _ 1) -
    Finsupp.mapDomain M.onE (Finsupp.single _ 1) +
    Finsupp.mapDomain M.onE (Finsupp.single _ 1) -
    Finsupp.mapDomain M.onE (Finsupp.single _ 1) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single, h0, h1, h2, h3]
  change _ = (if a.2 then 1 else -1) • roseCoverGeneratorChain f hf p
  cases hb : a.2 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, one_smul, neg_smul, roseCoverGeneratorChain]; abel

/-- The genuine lifted attaching-circle chain is the signed sum of its actual generator chains. -/
theorem roseCoverFundamentalChain_map :
    chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j) =
      ∑ k : Fin (w j).length,
        (if ((w j)[k.val]).2 then (1 : ℤ) else -1) •
          roseCoverGeneratorChain f hf
            (roseCoverLetterMidpoint w j f m hp k ((w j)[k.val])
              (List.getElem?_eq_getElem k.isLt)) := by
  erw [relatorCircleFundamentalChain, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact roseCoverLetterChain_map w j f hf m hm hp k _ (List.getElem?_eq_getElem k.isLt)

/-- The actual generator coefficients of the attaching circle are the signed sum of its lifted letters. -/
theorem roseCoverFundamentalChain_coordinates :
    roseCoverGeneratorCoordinates f hf
      (chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j)) =
      ∑ k : Fin (w j).length,
        (if ((w j)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single (roseCoverMidpointEdge f hf
            (roseCoverLetterMidpoint w j f m hp k ((w j)[k.val])
              (List.getElem?_eq_getElem k.isLt))) 1 := by grind [roseCoverFundamentalChain_map, map_sum, map_smul, roseCoverGeneratorChain_coordinates, Finset.sum_congr, roseCoverLetterMidpoint]

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- The actual attaching map preserves strict comparability on each valid relator circle. -/
theorem relatorCircleAttaching_strictMono :
    StrictMono (fun x : RelatorCircle w j => aFun w x.val) := by
  have he : ∀ e : StrictOrdEdge (RelatorCircle w j),
      aFun w e.val.1.val < aFun w e.val.2.val := by
    intro e
    obtain ⟨k, he⟩ := relatorCircle_edge_cases w j e
    obtain ⟨a, ha⟩ := exists_get_of_lt w k.isLt
    rcases he with rfl | rfl | rfl | rfl
    · change aFun w (TCirc.pt w j k.val CPos.cor) <
        aFun w (TCirc.pt w j k.val CPos.cedgL)
      rw [aFun_pt_cor, aFun_pt_cedgL_of_get w ha]
      exact (roseBaseEdge a.1 (!a.2)).property
    · change aFun w (TCirc.pt w j k.val CPos.cmid) <
        aFun w (TCirc.pt w j k.val CPos.cedgL)
      rw [aFun_pt_cmid_of_get w ha, aFun_pt_cedgL_of_get w ha]
      exact (roseMidEdge a.1 (!a.2)).property
    · change aFun w (TCirc.pt w j k.val CPos.cmid) <
        aFun w (TCirc.pt w j k.val CPos.cedgR)
      rw [aFun_pt_cmid_of_get w ha, aFun_pt_cedgR_of_get w ha]
      exact (roseMidEdge a.1 a.2).property
    · change aFun w (TCirc.pt w j (relatorCircleNext w j k).val CPos.cor) <
        aFun w (TCirc.pt w j k.val CPos.cedgR)
      rw [aFun_pt_cor, aFun_pt_cedgR_of_get w ha]
      exact (roseBaseEdge a.1 a.2).property
  intro x y h
  exact he ⟨(x, y), h⟩

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → CylBase w) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = cylOuter (aHom w) x.val)

/-- The actual collapsed attaching-circle vertices in the actual rose preimage. -/
def cylinderCoverCollapsedCircle (x : RelatorCircle w j) : cylinderCoverRoseSet w f :=
  ⟨cylinderCoverCollapse w hf (m x), cylinderCoverCollapse_mem_rose w f hf (m x)⟩

include hp in
/-- Actual collapse projects to the actual letter attaching map. -/
theorem cylinderCoverCollapsedCircle_projection (x : RelatorCircle w j) :
    cylinderCoverRoseEnd w f (cylinderCoverCollapsedCircle w j f hf m x) = aFun w x.val := by
  have h := cylinderCoverRoseEnd_projection w f (cylinderCoverCollapsedCircle w j f hf m x)
  erw [cylinderCoverCollapse_projection w hf (m x), hp x] at h
  exact Sum.inl.inj h

include hm hp in
/-- The actual collapsed circle map is strict because its actual attaching projection is strict. -/
theorem cylinderCoverCollapsedCircle_strictMono :
    StrictMono (cylinderCoverCollapsedCircle w j f hf m) := by
  intro x y h
  apply lt_of_le_of_ne ((cylinderCoverCollapse_monotone w hf) (hm h).le)
  intro he
  have hs : cylinderCoverCollapsedCircle w j f hf m x = cylinderCoverCollapsedCircle w j f hf m y := Subtype.ext he
  have hp' := congrArg (cylinderCoverRoseEnd w f) hs
  erw [cylinderCoverCollapsedCircle_projection w j f hf m hp,
    cylinderCoverCollapsedCircle_projection w j f hf m hp] at hp'
  exact (relatorCircleAttaching_strictMono w j h).ne hp'

include hm hp in
/-- Actual collapsed circle chains include as the normalized collapse of the original lifted chains. -/
theorem cylinderCoverCollapsedCircle_chain_inclusion
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) :
    chain1 (strictSubposetIncl (cylinderCoverRoseSet w f))
      (chain1 (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)) c) =
      normalizedStrictChain1 (cylinderCoverCollapse w hf) (cylinderCoverCollapse_monotone w hf)
        (chain1 (strictOrderCxMap m hm) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
    change Finsupp.mapDomain (strictSubposetIncl (cylinderCoverRoseSet w f)).onE
      (Finsupp.mapDomain (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)).onE (Finsupp.single e n)) =
      normalizedStrictChain1 _ _ (Finsupp.mapDomain (strictOrderCxMap m hm).onE (Finsupp.single e n))
    erw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      normalizedStrictChain1_single]
    have hn : cylinderCoverCollapse w hf (m e.val.1) ≠ cylinderCoverCollapse w hf (m e.val.2) :=
      fun he => (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp e.property).ne
        (Subtype.ext he)
    change Finsupp.single _ n = n • normalizeOrdEdge
      ⟨(cylinderCoverCollapse w hf (m e.val.1), cylinderCoverCollapse w hf (m e.val.2)), _⟩
    simp only [normalizeOrdEdge, dif_neg hn, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

include hm hp in
/-- The actual linear rose pullback equals the actual collapsed circle chain map. -/
theorem cylinderCoverCollapsedCircle_chain
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) :
    cylinderCoverCollapsedRoseChain w f hf (chain1 (strictOrderCxMap m hm) c) =
      chain1 (strictOrderCxMap (cylinderCoverCollapsedCircle w j f hf m)
        (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)) c := by
  apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective (cylinderCoverRoseSet w f))
  exact (cylinderCoverCollapsedRoseChain_inclusion w f hf _).trans
    (cylinderCoverCollapsedCircle_chain_inclusion w j f hf m hm hp c).symm

end FiniteChains.PresModel
end

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → CylBase w) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = cylOuter (aHom w) x.val)

/-- The actual collapsed midpoint associated to a valid letter of the lifted attaching circle. -/
def cylinderCoverCollapsedLetterMidpoint (k : Fin (w j).length) :=
  roseCoverLetterMidpoint w j (cylinderCoverRoseEnd w f)
    (cylinderCoverCollapsedCircle w j f hf m)
    (cylinderCoverCollapsedCircle_projection w j f hf m hp) k ((w j)[k.val])
      (List.getElem?_eq_getElem k.isLt)

/-- Actual collapsed attaching coefficients are the signed sum of actual lifted letter incidences. -/
theorem cylinderCoverCollapsedCircle_coordinates :
    cylinderCoverCollapsedGeneratorCoordinates w f hf
      (chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j)) =
      ∑ k : Fin (w j).length,
        (if ((w j)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single (roseCoverMidpointEdge (cylinderCoverRoseEnd w f)
            (cylinderCoverRoseEnd_isPosetCover w f hf)
            (cylinderCoverCollapsedLetterMidpoint w j f hf m hp k)) 1 := by
  change roseCoverGeneratorCoordinates (cylinderCoverRoseEnd w f)
    (cylinderCoverRoseEnd_isPosetCover w f hf)
      (cylinderCoverCollapsedRoseChain w f hf
        (chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j))) = _
  rw [cylinderCoverCollapsedCircle_chain w j f hf m hm hp]
  exact roseCoverFundamentalChain_coordinates w j (cylinderCoverRoseEnd w f)
    (cylinderCoverRoseEnd_isPosetCover w f hf) (cylinderCoverCollapsedCircle w j f hf m)
    (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)
    (cylinderCoverCollapsedCircle_projection w j f hf m hp)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

/-- The genuine cylinder projection of a lifted attaching circle is the actual outer circle. -/
theorem presCoverCircleCylinderInclusion_projection (p : PresCoverRelator w f)
    (x : RelatorCircle w p.val.2) :
    coneAdjCoverBaseEnd f (presCoverCircleCylinderInclusion w f hf p x) =
      cylOuter (aHom w) x.val := by
  apply Sum.inl.inj
  exact (coneAdjCoverBaseEnd_spec f _).trans
    (presCoverConeCircleOrderIso_symm_projection w f hf p.val.1 p.val.2 p.property x)

/-- Actual collapsed lifted-letter midpoints for a genuine lifted relator. -/
def presCoverRelatorLetterMidpoint (p : PresCoverRelator w f)
    (k : Fin (w p.val.2).length) :=
  cylinderCoverCollapsedLetterMidpoint w p.val.2 (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf) (presCoverCircleCylinderInclusion w f hf p)
      (presCoverCircleCylinderInclusion_projection w f hf p) k

/-- The actual relator generator-boundary column is its signed actual lifted-letter sum. -/
theorem presCoverRelatorGeneratorBoundary_single (p : PresCoverRelator w f) :
    presCoverRelatorGeneratorBoundary w f hf (Finsupp.single p 1) =
      ∑ k : Fin (w p.val.2).length,
        (if ((w p.val.2)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single (roseCoverMidpointEdge
            (cylinderCoverRoseEnd w (coneAdjCoverBaseEnd f))
            (cylinderCoverRoseEnd_isPosetCover w (coneAdjCoverBaseEnd f)
              (coneAdjCoverBaseEnd_isPosetCover f hf))
            (presCoverRelatorLetterMidpoint w f hf p k)) 1 := by
  change cylinderCoverCollapsedGeneratorCoordinates w (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (Finsupp.single p 1)) = _
  rw [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, one_smul]
  exact cylinderCoverCollapsedCircle_coordinates w p.val.2 (coneAdjCoverBaseEnd f)
    (coneAdjCoverBaseEnd_isPosetCover f hf) (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)
    (presCoverCircleCylinderInclusion_projection w f hf p)

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb
universe u
variable {α β γ J K L : Type u}

/-- Literal inclusions of labelled attaching words. This retains positions, including
the chosen subdivisions, and does not choose new word representatives. -/
structure PresWordEmbedding (w : J → List (α × Bool)) (v : K → List (β × Bool)) where
  gen : α ↪ β
  cell : J ↪ K
  word : ∀ j, v (cell j) = (w j).map (fun p => (gen p.1, p.2))

namespace PresWordEmbedding
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  {z : L → List (γ × Bool)} (h : PresWordEmbedding w v)

def roseMap : Rose α ↪o Rose β where
  toFun
    | .base => .base
    | .mid a => .mid (h.gen a)
    | .edg a b => .edg (h.gen a) b
  inj' := by
    intro x y he
    cases x <;> cases y <;> simp_all [h.gen.injective.eq_iff]
  map_rel_iff' := by
    intro x y
    change Rose.le _ _ ↔ Rose.le x y
    cases x <;> cases y <;> simp [Rose.le, h.gen.injective.eq_iff, Function.Embedding.coeFn_mk]

def circleFun (c : TCirc w) : TCirc v := (h.cell c.1, c.2)

theorem word_length (j : J) : (v (h.cell j)).length = (w j).length := by
  simp only [h.word, List.length_map]

theorem circleFun_injective : Function.Injective h.circleFun := by
  rintro ⟨j, k, t⟩ ⟨j', k', t'⟩ he
  change (h.cell j, k, t) = (h.cell j', k', t') at he
  simp_all

theorem circleFun_le_iff (c d : TCirc w) : h.circleFun c ≤ h.circleFun d ↔ c ≤ d := by
  rcases c with ⟨j, k, t⟩
  rcases d with ⟨j', k', t'⟩
  change h.circleFun _ = h.circleFun _ ∨ TCirc.lt v _ _ ↔
    (j, k, t) = (j', k', t') ∨ TCirc.lt w _ _
  erw [h.circleFun_injective.eq_iff]
  simp only [circleFun, TCirc.lt, TCirc.csucc, h.cell.injective.eq_iff, h.word_length]

def circleMap : TCirc w ↪o TCirc v where
  toFun := h.circleFun
  inj' := h.circleFun_injective
  map_rel_iff' := h.circleFun_le_iff _ _

theorem attaching_map (c : TCirc w) : aFun v (h.circleFun c) = h.roseMap (aFun w c) := by
  rcases c with ⟨j, k, t⟩
  have he : (v (h.cell j))[k]? = ((w j)[k]?).map (fun p => (h.gen p.1, p.2)) := by
    rw [h.word, List.getElem?_map]
  cases t <;> simp only [circleFun, aFun, he] <;>
    cases hg : (w j)[k]? <;> rfl

def posFun : PresPos w → PresPos v
  | .inl (.inl r) => iRose v (h.roseMap r)
  | .inl (.inr c) => iCirc v (h.circleFun c)
  | .inr j => apexOf v (h.cell j)

theorem circle_le_apex_iff (c : TCirc w) (j : J) :
    iCirc w c ≤ apexOf w j ↔ c.1 = j ∧ c.2.1 < (w j).length := by
  constructor
  · intro hc
    rcases (presPos_le_apex_iff w j _).mp hc with he | ⟨k, t, hk, he⟩
    · cases he
    · have he'  := Sum.inr.inj (Sum.inl.inj he)
      rw [he']
      exact ⟨rfl, hk⟩
  · rintro ⟨hj, hk⟩
    rcases c with ⟨j', k, t⟩
    change j' = j at hj
    subst j'
    exact iCirc_le_apexOf w t hk

theorem rose_not_le_apex (r : Rose α) (j : J) : ¬ iRose w r ≤ apexOf w j := by
  intro hr
  rcases (presPos_le_apex_iff w j _).mp hr with he | ⟨k, t, hk, he⟩ <;> cases he


theorem posFun_le_iff (p q : PresPos w) : h.posFun p ≤ h.posFun q ↔ p ≤ q := by
  cases p with
  | inr j =>
    cases q with
    | inr k => exact h.cell.injective.eq_iff
    | inl q => cases q <;> exact Iff.rfl
  | inl p =>
    cases q with
    | inr j =>
      cases p with
      | inl r => exact iff_of_false (rose_not_le_apex _ _) (rose_not_le_apex _ _)
      | inr c =>
        change iCirc v (h.circleFun c) ≤ apexOf v (h.cell j) ↔ iCirc w c ≤ apexOf w j
        rw [circle_le_apex_iff, circle_le_apex_iff]
        simp only [circleFun, h.cell.injective.eq_iff, h.word_length]
    | inl q =>
      cases p with
      | inl r =>
        cases q with
        | inl s => exact h.roseMap.le_iff_le
        | inr c => exact Iff.rfl
      | inr c =>
        cases q with
        | inl r =>
          change aFun v (h.circleFun c) ≤ h.roseMap r ↔ aFun w c ≤ r
          rw [h.attaching_map]
          exact h.roseMap.le_iff_le
        | inr d => exact h.circleFun_le_iff c d

def posMap : PresPos w ↪o PresPos v where
  toFun := h.posFun
  inj' := (by
    intro p q he
    cases p with
    | inr j =>
      cases q with
      | inr k => exact congrArg Sum.inr (h.cell.injective (Sum.inr.inj he))
      | inl q => cases q <;> cases he
    | inl p =>
      cases q with
      | inr k => cases p <;> cases he
      | inl q =>
        cases p with
        | inl r =>
          cases q with
          | inl s => exact congrArg (iRose w) (h.roseMap.injective (Sum.inl.inj (Sum.inl.inj he)))
          | inr c => cases he
        | inr c =>
          cases q with
          | inl r => cases he
          | inr d => exact congrArg (iCirc w) (h.circleFun_injective (Sum.inr.inj (Sum.inl.inj he))))
  map_rel_iff' := h.posFun_le_iff _ _

end PresWordEmbedding
end FiniteChains.PresModel
end

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval

variable {A B : Type} (f : A → B)

def diskRoseMap : C(Rose A, Rose B) :=
  desc (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ))
    (ContinuousMap.const _ (roseVertex B))
    ⟨fun d => cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f d.1, d.2⟩,
      continuous_sigma (fun a => (cell_continuous _ _).comp
        (continuous_sigmaMk («σ» := fun _ : B => ClosedUnitBall (Fin 1 → ℝ)) (i := f a)))⟩
    (fun a => (cell_boundary (roseAttaching B) _
      (boundaryFamilyInclusion_isClosedEmbedding B _).injective ⟨f a.1, a.2⟩).symm)

@[simp] theorem diskRoseMap_vertex : diskRoseMap f (roseVertex A) = roseVertex B := rfl

@[simp] theorem diskRoseMap_cell (d : DiskFamily A (Fin 1 → ℝ)) :
    diskRoseMap f (cell (roseAttaching A) (boundaryFamilyInclusion A _) d) =
      cell (roseAttaching B) (boundaryFamilyInclusion B _) ⟨f d.1, d.2⟩ := desc_cell ..

end FiniteChains.ClassicalGraphModel

namespace FiniteChains.PresModel
open Comb ClassicalGraphModel RelativeAttachment
open scoped Classical unitInterval

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
    (h : PresWordEmbedding w v)

theorem roseMapRealization_copy (a : A) (x : orderNerveRealization (Rose PUnit)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (roseCopyRealization a x) =
      roseCopyRealization (h.gen a) x := by
  change orderNerveRealizationMap h.roseMap h.roseMap.monotone
    (orderNerveRealizationMap (roseCopy a) (roseCopy a).monotone x) = _
  rw [orderNerveRealizationMap_comp]
  have he : h.roseMap ∘ roseCopy a = (roseCopy (h.gen a)) := by
    funext p
    cases p <;> rfl
  have mapEq (f g : Rose PUnit → Rose B) hf hg
      (he : f = g) : orderNerveRealizationMap f hf x = orderNerveRealizationMap g hg x := by
    subst g
    rfl
  exact mapEq _ _ _ _ he

theorem orderRoseRealizationHomeomorph_natural (x : orderNerveRealization (Rose A)) :
    orderRoseRealizationHomeomorph B (orderNerveRealizationMap h.roseMap h.roseMap.monotone x) =
      diskRoseMap h.gen (orderRoseRealizationHomeomorph A x) := by
  rcases orderRoseRealization_cases x with rfl | ⟨a, u, rfl⟩
  · change orderRoseRealizationHomeomorph B
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone
          (orderNerveRealizationVertex Rose.base)) = _
    rw [realizedMap_vertex]
    change orderRoseRealizationHomeomorph B (orderRoseBase B) = _
    rw [orderRoseRealizationHomeomorph_base, orderRoseRealizationHomeomorph_base,
      diskRoseMap_vertex]
  · obtain ⟨t, rfl⟩ := orderRoseTraversal_surjective u
    rw [roseMapRealization_copy, orderRoseRealizationHomeomorph_interval,
      orderRoseRealizationHomeomorph_interval, diskRoseMap_cell]

end FiniteChains.PresModel

namespace FiniteChains
open Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b)

def sameFiberForward (y : Y) : Z := g (hf.surjective y).choose

include hfg in
omit [TopologicalSpace Z] in
theorem sameFiberForward_apply (x : X) :
    sameFiberForward f g hf (f x) = g x :=
  (hfg _ _).mp (hf.surjective (f x)).choose_spec

def quotientSameFibersHomeomorph : Y ≃ₜ Z where
  toFun := sameFiberForward f g hf
  invFun := sameFiberForward g f hg
  left_inv y := by
    obtain ⟨x, rfl⟩ := hf.surjective y
    rw [sameFiberForward_apply f g hf hfg]
    exact sameFiberForward_apply g f hg (fun a b => (hfg a b).symm) x
  right_inv z := by
    obtain ⟨x, rfl⟩ := hg.surjective z
    rw [sameFiberForward_apply g f hg (fun a b => (hfg a b).symm)]
    exact sameFiberForward_apply f g hf hfg x
  continuous_toFun := by
    apply hf.continuous_iff.mpr
    have he : sameFiberForward f g hf ∘ f = g :=
      funext (sameFiberForward_apply f g hf hfg)
    rw [he]
    exact hg.continuous
  continuous_invFun := by
    apply hg.continuous_iff.mpr
    have he : sameFiberForward g f hg ∘ g = f :=
      funext (sameFiberForward_apply g f hg (fun a b => (hfg a b).symm))
    rw [he]
    exact hf.continuous

@[simp] theorem quotientSameFibersHomeomorph_apply (x : X) :
    quotientSameFibersHomeomorph f g hf hg hfg (f x) = g x :=
  sameFiberForward_apply f g hf hfg x

end FiniteChains

namespace FiniteChains.Comb
open scoped Classical unitInterval

variable (P : Type) [PartialOrder P]

def orderNerveConeBase : C(orderNerveRealization P, orderNerveRealization (WithTop P)) :=
  (orderNerveRealizationMap (fun p : P => (p : WithTop P)) WithTop.coe_mono).hom

def orderNerveRadialCone : C(I × orderNerveRealization P,
    orderNerveRealization (WithTop P)) where
  toFun rx := orderNerveRealizationCone (⊤ : WithTop P)
    (fun _ => Or.inl le_top) (unitInterval.symm rx.1) (orderNerveConeBase P rx.2)
  continuous_toFun := (orderNerveRealizationCone_continuous
    (⊤ : WithTop P) (fun _ => Or.inl le_top)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((orderNerveConeBase P).continuous.comp continuous_snd))

@[simp] theorem orderNerveConeBase_coordinate (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) p =
      orderNerveRealizationCoordinates P x p :=
  orderNerveRealizationCoordinates_map_injective _ WithTop.coe_mono
    WithTop.coe_injective x p

@[simp] theorem orderNerveConeBase_top (x : orderNerveRealization P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveConeBase P x) ⊤ = 0 :=
  orderNerveRealizationCoordinates_map_outside _ WithTop.coe_mono x ⊤
    (by rintro ⟨p, hp⟩; exact WithTop.coe_ne_top hp)

@[simp] theorem orderNerveRadialCone_top (r : I) (x : orderNerveRealization P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) ⊤ =
      1 - (r : ℝ) := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_coordinate (r : I) (x : orderNerveRealization P)
    (p : P) :
    orderNerveRealizationCoordinates (WithTop P) (orderNerveRadialCone P (r, x)) p =
      (r : ℝ) * orderNerveRealizationCoordinates P x p := by
  simp [orderNerveRadialCone, orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRadialCone_zero (x : orderNerveRealization P) :
    orderNerveRadialCone P (0, x) = orderNerveRealizationVertex (⊤ : WithTop P) := by
  simp [orderNerveRadialCone]

@[simp] theorem orderNerveRadialCone_one (x : orderNerveRealization P) :
    orderNerveRadialCone P (1, x) = orderNerveConeBase P x := by
  simp [orderNerveRadialCone]

theorem orderNerveRadialCone_eq_iff (a b : I × orderNerveRealization P) :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  constructor
  · intro h
    have ht := (orderNerveRadialCone_top P a.1 a.2).symm.trans
      ((congrArg (fun z => orderNerveRealizationCoordinates (WithTop P) z ⊤) h).trans
        (orderNerveRadialCone_top P b.1 b.2))
    have hr : a.1 = b.1 := Subtype.ext (by linarith)
    refine ⟨hr, ?_⟩
    by_cases hz : a.1 = 0
    · simp_all
    · right
      apply orderNerveRealizationCoordinates_injective P
      funext p
      have hp := (orderNerveRadialCone_coordinate P a.1 a.2 p).symm.trans
        ((congrArg (fun z => orderNerveRealizationCoordinates (WithTop P) z p) h).trans
          (orderNerveRadialCone_coordinate P b.1 b.2 p))
      erw [← hr] at hp
      have hn  := fun ha => hz (Subtype.ext ha)
      exact (mul_left_cancel₀ hn) hp
  · rintro ⟨hr, hz | hx⟩
    · obtain ⟨r, x⟩ := a
      obtain ⟨s, y⟩ := b
      dsimp at hr hz
      subst r
      subst s
      simp
    · exact congrArg (orderNerveRadialCone P) (Prod.ext hr hx)

theorem orderNerveRadialCone_surjective [Fintype P] [Nonempty P] :
    Function.Surjective (orderNerveRadialCone P) := by
  intro x
  let c := orderNerveRealizationCoordinates (WithTop P) x
  have hc p : 0 ≤ c p := orderNerveRealizationCoordinates_nonneg x p
  have hsum : c ⊤ + ∑ p : P, c p = 1 := by
    have hs := orderNerveRealizationCoordinates_sum x
    erw [Fintype.sum_option] at hs
    exact hs
  have hsnonneg : 0 ≤ ∑ p : P, c p := Finset.sum_nonneg (fun p _ => hc p)
  let r : I := ⟨1 - c ⊤, by constructor <;> linarith [hc ⊤]⟩
  have hsumr : ∑ p : P, c p = r := by dsimp [r]; linarith
  by_cases hr : r = 0
  · let p₀ : P := Classical.choice inferInstance
    refine ⟨(0, orderNerveRealizationVertex p₀), ?_⟩
    erw [orderNerveRadialCone_zero]
    apply orderNerveRealizationCoordinates_injective (WithTop P)
    funext p
    induction p using WithTop.recTopCoe with
    | top =>
        have hz := congrArg (fun t : I => (t : ℝ)) hr
        dsimp [r] at hz
        simp only [orderNerveRealizationCoordinates_vertex, ite_true]
        change 1 = c ⊤
        linarith
    | coe p =>
        have hp : c p ≤ ∑ q : P, c q :=
          Finset.single_le_sum (f := fun q : P => c q)
            (fun q _ => hc q) (Finset.mem_univ p)
        rw (config := { transparency := .default }) [hsumr, hr] at hp
        simp only [Set.Icc.coe_zero] at hp
        simp only [orderNerveRealizationCoordinates_vertex, WithTop.top_ne_coe, ite_false]
        exact (le_antisymm hp (hc p)).symm
  · have hrpos : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1
      (fun hz => hr (Subtype.ext hz.symm))
    let d : P → ℝ := fun p => c p / r
    have hd : ∀ p, 0 ≤ d p := fun p => div_nonneg (hc p) r.property.1
    have hdsum : ∑ p, d p = 1 := by
      dsimp [d]
      rw (config := { transparency := .default }) [← Finset.sum_div, hsumr, div_self (ne_of_gt hrpos)]
    have hdchain : IsChain (· ≤ ·) {p | 0 < d p} := by
      intro p hp q hq hpq
      have hp' : 0 < c p := (div_pos_iff_of_pos_right hrpos).mp hp
      have hq' : 0 < c q := (div_pos_iff_of_pos_right hrpos).mp hq
      have h := orderNerveRealizationCoordinates_support_chain x hp' hq'
        (fun he => hpq (WithTop.coe_injective he))
      exact h.elim (fun h => Or.inl (WithTop.coe_le_coe.mp h))
        (fun h => Or.inr (WithTop.coe_le_coe.mp h))
    obtain ⟨y, hy⟩ := orderNerveRealizationCoordinates_exists d hd hdsum hdchain
    refine ⟨(r, y), ?_⟩
    apply orderNerveRealizationCoordinates_injective (WithTop P)
    funext p
    induction p using WithTop.recTopCoe with
    | top =>
        rw (config := { transparency := .default }) [orderNerveRadialCone_top]
        change 1 - (1 - c ⊤) = c ⊤
        ring
    | coe p =>
        rw (config := { transparency := .default }) [orderNerveRadialCone_coordinate, hy p]
        change r * (c p / r) = c p
        field_simp [ne_of_gt hrpos]

end FiniteChains.Comb

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Classical

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]


def ballRadialQuotient : C(I × UnitBoundary E, ClosedUnitBall E) where
  toFun rx := ⟨(rx.1 : ℝ) • rx.2.val, (by
    rw [norm_smul, Real.norm_of_nonneg (rx.1).property.1, (rx.2).property, mul_one]
    exact (rx.1).property.2)⟩
  continuous_toFun := by fun_prop

@[simp] theorem ballRadialQuotient_norm (r : I) (x : UnitBoundary E) :
    ‖(ballRadialQuotient E (r, x)).val‖ = (r : ℝ) := by
  change ‖(r : ℝ) • x.val‖ = _
  rw [norm_smul, Real.norm_of_nonneg r.property.1, x.property, mul_one]

@[simp] theorem ballRadialQuotient_one (x : UnitBoundary E) :
    ballRadialQuotient E (1, x) = unitBoundaryInclusion E x := by
  apply Subtype.ext
  exact one_smul ℝ x.val

theorem ballRadialQuotient_eq_iff (a b : I × UnitBoundary E) :
    ballRadialQuotient E a = ballRadialQuotient E b ↔
      a.1 = b.1 ∧ (a.1 = 0 ∨ a.2 = b.2) := by
  constructor
  · intro h
    have hn := (ballRadialQuotient_norm E a.1 a.2).symm.trans
      ((congrArg (fun x : ClosedUnitBall E => ‖x.val‖) h).trans
        (ballRadialQuotient_norm E b.1 b.2))
    have hr  := Subtype.ext hn
    refine ⟨hr, ?_⟩
    by_cases hz : a.1 = 0
    · simp_all
    · right
      ext
      have he := congrArg (fun x : ClosedUnitBall E => x.val) h
      change (a.1 : ℝ) • a.2.val = (b.1 : ℝ) • b.2.val at he
      rw [← hr] at he
      have hrne  := fun ha => hz (Subtype.ext ha)
      have hi := congrArg (fun x : E => (a.1 : ℝ)⁻¹ • x) he
      simpa only [smul_smul, inv_mul_cancel₀ hrne, one_smul] using hi
  · rintro ⟨hr, hz | hx⟩
    · apply Subtype.ext
      change (a.1 : ℝ) • a.2.val = (b.1 : ℝ) • b.2.val
      rw [← hr, hz]
      simp
    · exact congrArg (ballRadialQuotient E) (Prod.ext hr hx)

theorem ballRadialQuotient_surjective (u : UnitBoundary E) :
    Function.Surjective (ballRadialQuotient E) := by
  intro x
  by_cases hx : x.val = 0
  · exact ⟨(0, u), Subtype.ext (by simp [ballRadialQuotient, hx])⟩
  · have hn  := norm_ne_zero_iff.mpr hx
    let r : I := ⟨‖x.val‖, norm_nonneg _, x.property⟩
    let v : UnitBoundary E := ⟨‖x.val‖⁻¹ • x.val, by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn]⟩
    refine ⟨(r, v), Subtype.ext ?_⟩
    change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]


end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open RelativeAttachment
open scoped Classical unitInterval

variable {P : Type} [PartialOrder P] [Fintype P] [Nonempty P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : orderNerveRealization P ≃ₜ UnitBoundary E)

def coneBallQuotient : C(I × orderNerveRealization P, ClosedUnitBall E) :=
  (ballRadialQuotient E).comp
    ⟨fun rx => (rx.1, e rx.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩


omit [Fintype P] [Nonempty P] [ProperSpace E] in
theorem coneBallQuotient_fibers (a b : I × orderNerveRealization P) :
    orderNerveRadialCone P a = orderNerveRadialCone P b ↔
      coneBallQuotient e a = coneBallQuotient e b := by simp_all [orderNerveRadialCone_eq_iff, ballRadialQuotient_eq_iff, coneBallQuotient]

/-- Extend a boundary homeomorphism radially over the actual order cone. -/
def orderNerveWithTopBallHomeomorph :
    orderNerveRealization (WithTop P) ≃ₜ ClosedUnitBall E := by
  letI : CompactSpace (UnitBoundary E) := isCompact_iff_compactSpace.mp
    (show IsCompact {x : E | ‖x‖ = 1} by
      simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1)
  letI : CompactSpace (orderNerveRealization P) := e.isClosedEmbedding.compactSpace
  exact quotientSameFibersHomeomorph (orderNerveRadialCone P) (coneBallQuotient e)
    ((orderNerveRadialCone P).continuous.isClosedMap.isQuotientMap
      (orderNerveRadialCone P).continuous (orderNerveRadialCone_surjective P))
    ((coneBallQuotient e).continuous.isClosedMap.isQuotientMap
      (coneBallQuotient e).continuous (by
        let p₀ : P := Classical.choice inferInstance
        intro x
        obtain ⟨⟨r, u⟩, hu⟩ := ballRadialQuotient_surjective E
          (e (orderNerveRealizationVertex p₀)) x
        exact ⟨(r, e.symm u), by simpa only [coneBallQuotient, ContinuousMap.comp_apply,
          ContinuousMap.coe_mk, Homeomorph.apply_symm_apply] using hu⟩))
    (coneBallQuotient_fibers e)

theorem orderNerveWithTopBallHomeomorph_radial (r : I) (x : orderNerveRealization P) :
    orderNerveWithTopBallHomeomorph e (orderNerveRadialCone P (r, x)) =
      ballRadialQuotient E (r, e x) := quotientSameFibersHomeomorph_apply _ _ _ _ _ (r, x)

/-- The boundary restriction is exactly the supplied map, with no reparametrization. -/
theorem orderNerveWithTopBallHomeomorph_boundary (x : orderNerveRealization P) :
    orderNerveWithTopBallHomeomorph e (orderNerveConeBase P x) =
      unitBoundaryInclusion E (e x) := by
  rw [← orderNerveRadialCone_one P x, orderNerveWithTopBallHomeomorph_radial,
    ballRadialQuotient_one]

end FiniteChains.Comb

namespace FiniteChains.Comb
open scoped Classical

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] (v : Q)
    (e : P ≃o StrictBelow v)

def lowerConeMap : WithTop P → Set.Iic v := WithTop.recTopCoe
  ⟨v, le_rfl⟩ (fun p => ⟨(e p).val, (e p).property.le⟩)

@[simp] theorem lowerConeMap_top : lowerConeMap v e ⊤ = ⟨v, le_rfl⟩ := rfl
@[simp] theorem lowerConeMap_coe (p : P) :
    lowerConeMap v e (p : WithTop P) = ⟨(e p).val, (e p).property.le⟩ := rfl


def lowerConeOrderIso : WithTop P ≃o Set.Iic v where
  toEquiv := Equiv.ofBijective (lowerConeMap v e) (by
    constructor
    · intro a b h
      induction a using WithTop.recTopCoe with
      | top =>
          induction b using WithTop.recTopCoe with
          | top => rfl
          | coe b => exact ((ne_of_lt (e b).property)
              (congrArg Subtype.val h).symm).elim
      | coe a =>
          induction b using WithTop.recTopCoe with
          | top => exact ((ne_of_lt (e a).property) (congrArg Subtype.val h)).elim
          | coe b =>
              exact congrArg (fun p : P => (p : WithTop P))
                (e.injective (Subtype.ext (congrArg (fun y : Set.Iic v => y.val) h)))
    · intro x
      by_cases hx : x.val = v
      · exact ⟨⊤, Subtype.ext hx.symm⟩
      · let p : StrictBelow v := ⟨x.val, lt_of_le_of_ne x.property hx⟩
        exact ⟨(e.symm p : WithTop P), Subtype.ext
          (congrArg (fun y : StrictBelow v => y.val) (e.apply_symm_apply p))⟩)
  map_rel_iff' := by
    intro a b
    induction a using WithTop.recTopCoe with
    | top =>
        induction b using WithTop.recTopCoe with
        | top => exact iff_of_true le_rfl le_rfl
        | coe b =>
            change v ≤ (e b).val ↔ (⊤ : WithTop P) ≤ b
            exact iff_of_false (not_le_of_gt (e b).property) (not_le_of_gt (WithTop.coe_lt_top b))
    | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact iff_of_true (e a).property.le le_top
        | coe b =>
            change (e a).val ≤ (e b).val ↔ (a : WithTop P) ≤ b
            exact e.map_rel_iff.trans WithTop.coe_le_coe.symm

def lowerConeBoundary : P →o Set.Iic v where
  toFun p := ⟨(e p).val, (e p).property.le⟩
  monotone' := fun _ _ h => e.monotone h


variable [Fintype P] [Nonempty P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (b : orderNerveRealization P ≃ₜ RelativeAttachment.UnitBoundary E)

def lowerConeBallHomeomorph :
    orderNerveRealization (Set.Iic v) ≃ₜ RelativeAttachment.ClosedUnitBall E :=
  (orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm.trans
    (orderNerveWithTopBallHomeomorph b)

theorem lowerConeBallHomeomorph_boundary (x : orderNerveRealization P) :
    lowerConeBallHomeomorph v e b
      (orderNerveRealizationMap (lowerConeBoundary v e) (lowerConeBoundary v e).monotone x) =
      RelativeAttachment.unitBoundaryInclusion E (b x) := by
  rw [← (show orderNerveRealizationOrderIso (lowerConeOrderIso v e) (orderNerveConeBase P x) =
      orderNerveRealizationMap (lowerConeBoundary v e) (lowerConeBoundary v e).monotone x by
    change orderNerveRealizationMap (lowerConeOrderIso v e) (lowerConeOrderIso v e).monotone
        (orderNerveRealizationMap (fun p : P => (p : WithTop P)) WithTop.coe_mono x) = _
    rw [orderNerveRealizationMap_comp]
    rfl)]
  change orderNerveWithTopBallHomeomorph b
      ((orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm
        (orderNerveRealizationOrderIso (lowerConeOrderIso v e) (orderNerveConeBase P x))) = _
  rw [Homeomorph.symm_apply_apply, orderNerveWithTopBallHomeomorph_boundary]

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Classical

variable {α J : Type} (w : J → List (α × Bool)) (j : J)
    (hn : 0 < (w j).length)

instance relatorCircle_fintype : Fintype (RelatorCircle w j) :=
  Fintype.ofFinite _

def presConeBallHomeomorph :
    orderNerveRealization (Set.Iic (apexOf w j)) ≃ₜ ClosedUnitBall (Fin 2 → ℝ) := by
  letI : Nonempty (RelatorCircle w j) := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  exact lowerConeBallHomeomorph (apexOf w j) (relatorCircleOrderIso w j)
    (relatorCircleBoundaryHomeomorph w j hn)

end FiniteChains.PresModel

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual lifted-order face coordinates commute with the actual path-class deck action. -/
theorem uOrderFace_deck (g : Pi1 (orderCx P) a) (t : OrdTri (UOrder P a)) :
    uOrderFace ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF t) =
      deckF g (uOrderFace t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (endV (deckV g t.1.1), endV (deckV g t.1.2.1), endV (deckV g t.1.2.2)) =
      (endV t.1.1, endV t.1.2.1, endV t.1.2.2)
    simp

end FiniteChains.Comb

namespace FiniteChains.Comb
universe u
variable {K : Complex2.{u}} {P : Type u} [Preorder P]
  (k : Hom K (orderCx P)) (S : P → Prop) (hk : ∀ v, S (k.onV v))

include hk in
theorem orderCxRestrict_edge_support (e : K.E) :
    S (k.onE e).1.1 ∧ S (k.onE e).1.2 := by
  constructor
  · change S ((orderCx P).src (k.onE e))
    rw [k.src_onE]
    exact hk _
  · change S ((orderCx P).tgt (k.onE e))
    rw [k.tgt_onE]
    exact hk _

include hk in
/-- The middle and final vertices of the image triangle occur as targets of
its attaching edges, so vertex support suffices even for a general two-complex. -/
theorem orderCxRestrict_face_support (t : K.F) :
    S (k.onF t).1.1 ∧ S (k.onF t).1.2.1 ∧ S (k.onF t).1.2.2 := by
  have he : ∀ e : OrdEdge P, (e, true) ∈ (orderCx P).att (k.onF t) → S e.1.2 := by
    intro e he
    rw [k.att_onF] at he
    obtain ⟨eb, _, heb⟩ := List.mem_map.mp he
    have ht := congrArg (fun z : OrdEdge P × Bool => z.1.1.2) heb
    rw [← ht]
    exact (orderCxRestrict_edge_support k S hk eb.1).2
  refine ⟨?_, ?_, ?_⟩
  · change S ((orderCx P).base (k.onF t))
    rw [k.base_onF]
    exact hk _
  · exact he ⟨((k.onF t).1.1, (k.onF t).1.2.1), (k.onF t).2.1⟩
      (by simp [orderCx])
  · exact he ⟨((k.onF t).1.2.1, (k.onF t).1.2.2), (k.onF t).2.2⟩
      (by simp [orderCx])

def orderCxRestrictEdge (e : K.E) : OrdEdge {p : P // S p} :=
  ⟨(⟨(k.onE e).1.1, (orderCxRestrict_edge_support k S hk e).1⟩,
    ⟨(k.onE e).1.2, (orderCxRestrict_edge_support k S hk e).2⟩), (k.onE e).2⟩

def orderCxRestrictFace (t : K.F) : OrdTri {p : P // S p} :=
  ⟨(⟨(k.onF t).1.1, (orderCxRestrict_face_support k S hk t).1⟩,
    ⟨(k.onF t).1.2.1, (orderCxRestrict_face_support k S hk t).2.1⟩,
    ⟨(k.onF t).1.2.2, (orderCxRestrict_face_support k S hk t).2.2⟩), (k.onF t).2⟩


/-- The actual codomain restriction; no edge or face support premise is added. -/
def orderCxRestrict : Hom K (orderCx {p : P // S p}) where
  onV v := ⟨k.onV v, hk v⟩
  onE := orderCxRestrictEdge k S hk
  onF := orderCxRestrictFace k S hk
  src_onE e := Subtype.ext (k.src_onE e)
  tgt_onE e := Subtype.ext (k.tgt_onE e)
  base_onF t := Subtype.ext (k.base_onF t)
  att_onF t := by
    apply List.map_injective_iff.mpr (show Function.Injective (fun eb : (orderCx {p : P // S p}).E × Bool =>
      ((subposetHom S).onE eb.1, eb.2)) by
      intro x y h
      refine Prod.ext ?_ (congrArg (fun e : OrdEdge P × Bool => e.2) h)
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun e : OrdEdge P × Bool => e.1.1.1) h
      · apply Subtype.ext
        exact congrArg (fun e : OrdEdge P × Bool => e.1.1.2) h)
    rw [← (subposetHom S).att_onF]
    change (orderCx P).att (k.onF t) =
      ((K.att t).map (fun eb => (orderCxRestrictEdge k S hk eb.1, eb.2))).map
        (fun eb => ((subposetHom S).onE eb.1, eb.2))
    rw [List.map_map, k.att_onF]
    congr 1

@[simp] theorem orderCxRestrict_onV (v : K.V) :
    (orderCxRestrict k S hk).onV v = ⟨k.onV v, hk v⟩ := rfl

/-- Forgetting the support proofs recovers the original cellular map on every cell. -/
theorem orderCxRestrict_projects :
    (orderCxMap Subtype.val (fun _ _ h => h)).comp (orderCxRestrict k S hk) = k := rfl

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical
variable {P : Type} [PartialOrder P]

/-- Two simplices whose vertices are pairwise cross-comparable lie in an actual
common simplex, with explicit simplex operators for both inclusions. -/
theorem orderNerveSimplex_common {n k : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) (t : (nerve P).obj (Opposite.op k))
    (hc : ∀ i j, s.obj i ≤ t.obj j ∨ t.obj j ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (b : k ⟶ m),
      (nerve P).map a.op u = s ∧ (nerve P).map b.op u = t := by
  let A  := Set.range s.obj ∪ Set.range t.obj
  have hA : IsChain (· ≤ ·) A := by
    intro x hx y hy _
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (s.map (homOfLE h)))
        · exact Or.inr (leOfHom (s.map (homOfLE h)))
      · exact hc i j
    · rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact (hc j i).symm
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (t.map (homOfLE h)))
        · exact Or.inr (leOfHom (t.map (homOfLE h)))
  letI := ((Set.finite_range s.obj).union (Set.finite_range t.obj)).fintype
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  letI : Nonempty A := ⟨⟨s.obj 0, Or.inl ⟨0, rfl⟩⟩⟩
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e  := (Fintype.orderIsoFinOfCardEq A hr).symm
  let u  :=
    (show Monotone (fun i : Fin (r + 1) => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor
  let a  := SimplexCategory.mkHom
    ⟨fun i => e ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (s.map (homOfLE h)))⟩
  let b  := SimplexCategory.mkHom
    ⟨fun i => e ⟨t.obj i, Or.inr ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (t.map (homOfLE h)))⟩
  refine ⟨⦋r⦌, u, a, b, ?_, ?_⟩
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply ⟨s.obj i, Or.inl ⟨i, rfl⟩⟩))
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply ⟨t.obj i, Or.inr ⟨i, rfl⟩⟩))

end FiniteChains.Comb
