module

public import RequestProject.OrderNerveRealizationCover
public import RequestProject.OrderNerveRealizationNestedSubcomplex
public import RequestProject.ConeAdjBaseCover
public import RequestProject.PosetCoverLowerInterval
public import RequestProject.AttachmentQuotientHomeomorph

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)

abbrev ConeAdjBase := coneAdjBaseSet (S := S)
abbrev ConeAdjDisk (j : J) := Set.Iic (ConeAdj.apex (S := S) j)
abbrev ConeAdjBoundary (j : J) :=
  setOf (fun x : ConeAdjDisk S j => x.val ∈ ConeAdjBase S)

def coneAdjBoundaryOrderIso (j : J) : ConeAdjBoundary S j ≃o StrictBelow (ConeAdj.apex (S := S) j) where
  toFun x := ⟨x.val.val, lt_of_le_of_ne x.val.property fun h =>
    let ⟨_, hp⟩ := x.property; Sum.inl_ne_inr (hp.trans h)⟩
  invFun x := ⟨⟨x.val, x.property.le⟩, by
    rcases x with ⟨p | k, hq⟩
    · exact ⟨p, rfl⟩
    · cases (hq.le : k = j); exact (lt_irrefl _ hq).elim⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def coneAdjRealizationOld :
    C(orderNerveRealization (ConeAdjBase S), orderNerveRealization (ConeAdj S)) :=
  (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom

def coneAdjRealizationCell :
    C((Σ j, orderNerveRealization (ConeAdjDisk S j)),
      orderNerveRealization (ConeAdj S)) :=
  ⟨fun z => orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2,
    continuous_sigma fun _ =>
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom.continuous⟩

def coneAdjRealizationBoundary :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      (Σ j, orderNerveRealization (ConeAdjDisk S j))) :=
  ⟨fun z => ⟨z.1, orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2⟩,
    continuous_sigma fun j => (continuous_sigmaMk
      (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)).comp
      (orderNerveRealizationMap (Subtype.val : ConeAdjBoundary S j → ConeAdjDisk S j)
        (fun _ _ h => h)).hom.continuous⟩

def coneAdjBoundaryToBase (j : J) : ConeAdjBoundary S j → ConeAdjBase S :=
  fun x => ⟨x.val.val, x.property⟩

theorem coneAdjBoundaryToBase_monotone (j : J) : Monotone (coneAdjBoundaryToBase S j) :=
  fun _ _ h => h

def coneAdjRealizationAttaching :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      orderNerveRealization (ConeAdjBase S)) :=
  ⟨fun z => orderNerveRealizationMap (coneAdjBoundaryToBase S z.1)
      (coneAdjBoundaryToBase_monotone S z.1) z.2,
    continuous_sigma fun j =>
      (orderNerveRealizationMap (coneAdjBoundaryToBase S j)
        (coneAdjBoundaryToBase_monotone S j)).hom.continuous⟩

theorem coneAdjRealizationCell_boundary_iff
    (z : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationCell S z ∈ Set.range (coneAdjRealizationOld S) ↔
      z ∈ Set.range (coneAdjRealizationBoundary S) := by
  rcases z with ⟨j, x⟩
  rw [coneAdjRealizationOld, orderNerveRealizationSubtype_range (ConeAdjBase S),
    show (⟨j, x⟩ : Σ k, orderNerveRealization (ConeAdjDisk S k)) ∈ Set.range (coneAdjRealizationBoundary S) ↔
      x ∈ orderNerveRealizationSupported (ConeAdjDisk S j) (ConeAdjBoundary S j) by
    change _ ↔ x ∈ (orderNerveRealizationSubcomplex (ConeAdjDisk S j) (ConeAdjBoundary S j) : Set _)
    rw [← orderNerveRealizationSubtype_range (ConeAdjBoundary S j)]
    exact ⟨by rintro ⟨⟨k, z⟩, h⟩; cases congrArg Sigma.fst h; exact ⟨z, eq_of_heq (Sigma.mk.inj h).2⟩,
      by rintro ⟨z, rfl⟩; exact ⟨⟨j, z⟩, rfl⟩⟩]
  exact Set.ext_iff.mp
    (orderNerveRealizationSubtype_preimage_supported (ConeAdjDisk S j) (ConeAdjBase S)) x

theorem coneAdjRealizationCell_injective_off_boundary
    (z t : Σ j, orderNerveRealization (ConeAdjDisk S j))
    (hz : z ∉ Set.range (coneAdjRealizationBoundary S))
    (_ht : t ∉ Set.range (coneAdjRealizationBoundary S))
    (he : coneAdjRealizationCell S z = coneAdjRealizationCell S t) : z = t := by
  rcases z with ⟨j, x⟩; rcases t with ⟨k, y⟩
  by_cases hjk : j = k
  · subst k
    exact congrArg (Sigma.mk j) (orderNerveRealizationMap_injective
      (Subtype.val : ConeAdjDisk S j → ConeAdj S) (fun _ _ h => h) Subtype.val_injective he)
  · refine (hz ((coneAdjRealizationCell_boundary_iff S ⟨j, x⟩).mp ?_)).elim
    rw [coneAdjRealizationOld, orderNerveRealizationSubtype_range (ConeAdjBase S)]
    have hx : coneAdjRealizationCell S ⟨j, x⟩ ∈
        orderNerveRealizationSupported (ConeAdj S) (ConeAdjDisk S j) := by
      change _ ∈ (orderNerveRealizationSubcomplex (ConeAdj S) (ConeAdjDisk S j) :
        Set (orderNerveRealization (ConeAdj S)))
      rw [← orderNerveRealizationSubtype_range (ConeAdjDisk S j)]; exact ⟨x, rfl⟩
    have hy : coneAdjRealizationCell S ⟨j, x⟩ ∈
        orderNerveRealizationSupported (ConeAdj S) (ConeAdjDisk S k) := by
      change _ ∈ (orderNerveRealizationSubcomplex (ConeAdj S) (ConeAdjDisk S k) :
        Set (orderNerveRealization (ConeAdj S)))
      rw [he, ← orderNerveRealizationSubtype_range (ConeAdjDisk S k)]; exact ⟨y, rfl⟩
    intro p hp
    by_cases hpj : p ∈ ConeAdjDisk S j
    · refine hy p fun hpk => hp ?_
      rcases p with p | l
      · exact ⟨p, rfl⟩
      · exact (hjk ((show l = j from hpj).symm.trans (show l = k from hpk))).elim
    · exact hx p hpj

theorem coneAdjRealization_piece_isQuotientMap :
    IsQuotientMap (Sum.elim (coneAdjRealizationOld S) (coneAdjRealizationCell S)) := by
  have hpiece (n : SimplexCategory) (s : (nerve (ConeAdj S)).obj (Opposite.op n)) :
      (∀ i, s.obj i ∈ ConeAdjBase S) ∨ ∃ j, ∀ i, s.obj i ∈ ConeAdjDisk S j := by
    have hlast (i : Fin (n.len + 1)) : s.obj i ≤ s.obj (Fin.last n.len) :=
      leOfHom (s.map (homOfLE (Fin.le_last i)))
    cases he : s.obj (Fin.last n.len) with
    | inl p =>
        exact .inl fun i => coneAdjBaseSet_down_closed
          (show s.obj (Fin.last n.len) ∈ ConeAdjBase S by rw [he]; exact ⟨p, rfl⟩) (hlast i)
    | inr j =>
        exact .inr ⟨j, fun i => by change s.obj i ≤ ConeAdj.apex j; simpa only [he, ConeAdj.apex] using hlast i⟩
  refine isQuotientMap_iff_isClosed.mpr ⟨fun x => ?_, fun T => ⟨fun hT =>
    hT.preimage ((coneAdjRealizationOld S).continuous.sumElim (coneAdjRealizationCell S).continuous),
    fun hT => (orderNerveRealization_isClosed_iff (ConeAdj S) T).mpr fun n s => ?_⟩⟩
  · obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective (ConeAdj S) x
    rcases hpiece n s with h | ⟨j, h⟩
    · exact ⟨Sum.inl (orderNerveRealizationSimplex (ConeAdjBase S)
        (orderNerveSimplexSubtype (ConeAdjBase S) s h) z),
        orderNerveRealizationSimplex_subtype (ConeAdjBase S) s h z⟩
    · exact ⟨Sum.inr ⟨j, orderNerveRealizationSimplex (ConeAdjDisk S j)
        (orderNerveSimplexSubtype (ConeAdjDisk S j) s h) z⟩,
        orderNerveRealizationSimplex_subtype (ConeAdjDisk S j) s h z⟩
  · rcases hpiece n s with h | ⟨j, h⟩
    · convert (hT.preimage (continuous_inl : Continuous
        (Sum.inl : orderNerveRealization (ConeAdjBase S) →
          orderNerveRealization (ConeAdjBase S) ⊕ (Σ j, orderNerveRealization (ConeAdjDisk S j))))).preimage
        (orderNerveRealizationSimplex (ConeAdjBase S)
          (orderNerveSimplexSubtype (ConeAdjBase S) s h)).hom.continuous using 1
      ext z
      exact iff_of_eq (congrArg (· ∈ T) (orderNerveRealizationSimplex_subtype (ConeAdjBase S) s h z).symm)
    · convert (hT.preimage ((continuous_inr : Continuous
        (Sum.inr : (Σ j, orderNerveRealization (ConeAdjDisk S j)) →
          orderNerveRealization (ConeAdjBase S) ⊕ (Σ j, orderNerveRealization (ConeAdjDisk S j)))).comp
        (continuous_sigmaMk (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)))).preimage
        (orderNerveRealizationSimplex (ConeAdjDisk S j)
          (orderNerveSimplexSubtype (ConeAdjDisk S j) s h)).hom.continuous using 1
      ext z
      exact iff_of_eq (congrArg (· ∈ T) (orderNerveRealizationSimplex_subtype (ConeAdjDisk S j) s h z).symm)

def coneAdjRealizationAttachmentHomeomorph :
    RelativeAttachment.Space (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
      ≃ₜ orderNerveRealization (ConeAdj S) :=
  RelativeAttachment.attachmentQuotientHomeomorph
    (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
    (coneAdjRealizationOld S) (coneAdjRealizationCell S)
    (fun z => by
      change orderNerveRealizationMap Subtype.val (fun _ _ h => h)
          (orderNerveRealizationMap (coneAdjBoundaryToBase S z.1)
            (coneAdjBoundaryToBase_monotone S z.1) z.2) =
        orderNerveRealizationMap Subtype.val (fun _ _ h => h)
          (orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2)
      rw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]; rfl)
    (orderNerveRealizationMap_injective Subtype.val (fun _ _ h => h) Subtype.val_injective)
    (coneAdjRealizationCell_boundary_iff S)
    (coneAdjRealizationCell_injective_off_boundary S)
    (coneAdjRealization_piece_isQuotientMap S)

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_old
    (x : orderNerveRealization (ConeAdjBase S)) :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.old (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationOld S x :=
  RelativeAttachment.attachmentQuotientHomeomorph_old _ _ _ _ _ _ _ _ _ x

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_cell
    (x : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.cell (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationCell S x :=
  RelativeAttachment.attachmentQuotientHomeomorph_cell _ _ _ _ _ _ _ _ _ x
