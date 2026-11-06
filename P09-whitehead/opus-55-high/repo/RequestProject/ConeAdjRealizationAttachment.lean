import RequestProject.OrderNerveRealizationCover
import RequestProject.OrderNerveRealizationNestedSubcomplex
import RequestProject.ConeAdjBaseCover
import RequestProject.PosetCoverLowerInterval
import RequestProject.AttachmentQuotientHomeomorph


/-! The realization of a poset obtained by adjoining cone points is the
actual attachment of the realized lower ideals to the realized old part.
The family can be infinite: the quotient argument uses the simplexwise
weak topology, not a finite closed-cover assertion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Topology

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)

abbrev ConeAdjBase := coneAdjBaseSet (S := S)
abbrev ConeAdjDisk (j : J) := Set.Iic (ConeAdj.apex (S := S) j)
abbrev ConeAdjBoundary (j : J) :=
  setOf (fun x : ConeAdjDisk S j => x.val ∈ ConeAdjBase S)

/-- The old boundary of a cone is exactly its strict lower interval. -/
def coneAdjBoundaryOrderIso j : ConeAdjBoundary S j ≃o StrictBelow (ConeAdj.apex (S := S) j) where
  toFun x := ⟨x.val.val, lt_of_le_of_ne x.val.property (by
    intro h
    cases' x.property with p hp
    exact Sum.inl_ne_inr (hp.trans h))⟩
  invFun x := ⟨⟨x.val, x.property.le⟩, by
    cases' x with q hq
    cases q with
    | inl p => tauto
    | inr k =>
        have hk := hq.le
        subst k
        exact (lt_irrefl _ hq).elim⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := Iff.rfl

def coneAdjRealizationOld :
    C(orderNerveRealization (ConeAdjBase S), orderNerveRealization (ConeAdj S)) :=
  ⟨orderNerveRealizationMap Subtype.val (by tauto),
    (orderNerveRealizationMap Subtype.val (by tauto)).hom.continuous⟩

def coneAdjRealizationCell :
    C((Σ j, orderNerveRealization (ConeAdjDisk S j)),
      orderNerveRealization (ConeAdj S)) :=
  ⟨fun z => orderNerveRealizationMap Subtype.val (by tauto) z.2,
    continuous_sigma (fun _ =>
      (orderNerveRealizationMap Subtype.val (by tauto)).hom.continuous)⟩

def coneAdjRealizationBoundary :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      (Σ j, orderNerveRealization (ConeAdjDisk S j))) :=
  ⟨fun z => ⟨z.1, orderNerveRealizationMap Subtype.val (by tauto) z.2⟩,
    continuous_sigma (fun j => (continuous_sigmaMk
      (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)).comp
      (orderNerveRealizationMap (Subtype.val : ConeAdjBoundary S j → ConeAdjDisk S j)
        (by tauto)).hom.continuous)⟩

def coneAdjBoundaryToBase j : ConeAdjBoundary S j → ConeAdjBase S :=
  fun x => ⟨x.val.val, x.property⟩

theorem coneAdjBoundaryToBase_monotone j : Monotone (coneAdjBoundaryToBase S j) :=
  by tauto

def coneAdjRealizationAttaching :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      orderNerveRealization (ConeAdjBase S)) :=
  ⟨fun z => orderNerveRealizationMap _
      (coneAdjBoundaryToBase_monotone S z.1) z.2,
    continuous_sigma (fun j =>
      (orderNerveRealizationMap _
        (coneAdjBoundaryToBase_monotone S j)).hom.continuous)⟩

theorem coneAdjRealization_boundary_commutes
    z :
    coneAdjRealizationOld S (coneAdjRealizationAttaching S z) =
      coneAdjRealizationCell S (coneAdjRealizationBoundary S z) := by
  change orderNerveRealizationMap Subtype.val (by tauto)
      (orderNerveRealizationMap _
        (coneAdjBoundaryToBase_monotone S z.1) z.2) =
    orderNerveRealizationMap Subtype.val (by tauto)
      (orderNerveRealizationMap Subtype.val (by tauto) z.2)
  rw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem coneAdjRealizationOld_range :
    Set.range (coneAdjRealizationOld S) =
      orderNerveRealizationSupported (ConeAdj S) (ConeAdjBase S) :=
  orderNerveRealizationSubtype_range _

theorem coneAdjRealizationBoundary_range j
    x :
    (⟨j, x⟩ : Σ k, orderNerveRealization (ConeAdjDisk S k)) ∈
        Set.range (coneAdjRealizationBoundary S) ↔
      x ∈ orderNerveRealizationSupported (ConeAdjDisk S j) (ConeAdjBoundary S j) := by
  change _ ↔ x ∈ (orderNerveRealizationSubcomplex (ConeAdjDisk S j)
    (ConeAdjBoundary S j) : Set (orderNerveRealization (ConeAdjDisk S j)))
  rw [← orderNerveRealizationSubtype_range _]
  constructor
  · rintro ⟨⟨k, z⟩, h⟩
    have hk : k = j := congrArg Sigma.fst h
    subst k
    exact ⟨z, eq_of_heq (Sigma.mk.inj h).2⟩
  aesop

theorem coneAdjRealizationCell_boundary_iff
    z :
    coneAdjRealizationCell S z ∈ Set.range (coneAdjRealizationOld S) ↔
      z ∈ Set.range (coneAdjRealizationBoundary S) := by
  cases' z with j x
  rw [coneAdjRealizationOld_range, coneAdjRealizationBoundary_range]
  exact Set.ext_iff.mp
    (orderNerveRealizationSubtype_preimage_supported _ _) x

theorem coneAdj_disks_inter_subset_base (hjk : j ≠ k) :
    ConeAdjDisk S j ∩ ConeAdjDisk S k ⊆ ConeAdjBase S := by
  rintro (p | l) ⟨hj, hk⟩
  · tauto
  · exact (hjk ((show l = j from hj).symm.trans (by aesop))).elim

theorem coneAdjRealizationCell_inter_base (hjk : j ≠ k)
    x
    y
    (h : coneAdjRealizationCell S ⟨j, x⟩ = coneAdjRealizationCell S ⟨k, y⟩) :
    coneAdjRealizationCell S ⟨j, x⟩ ∈ Set.range (coneAdjRealizationOld S) := by
  rw [coneAdjRealizationOld_range]
  have hx : coneAdjRealizationCell S ⟨j, x⟩ ∈
      orderNerveRealizationSupported _ (ConeAdjDisk S j) := by
    change _ ∈ (orderNerveRealizationSubcomplex (ConeAdj S) (ConeAdjDisk S j) :
      Set (orderNerveRealization (ConeAdj S)))
    rw [← orderNerveRealizationSubtype_range _]
    tauto
  have hy : coneAdjRealizationCell S ⟨j, x⟩ ∈
      orderNerveRealizationSupported _ (ConeAdjDisk S k) := by
    change _ ∈ (orderNerveRealizationSubcomplex (ConeAdj S) (ConeAdjDisk S k) :
      Set (orderNerveRealization (ConeAdj S)))
    rw [h, ← orderNerveRealizationSubtype_range _]
    tauto
  intro p hp
  by_cases hpj : p ∈ ConeAdjDisk S j
  · apply hy p
    intro hpk
    exact hp (coneAdj_disks_inter_subset_base S hjk ⟨hpj, hpk⟩)
  tauto

theorem coneAdjRealizationCell_injective_off_boundary
    z t
    (hz : z ∉ Set.range (coneAdjRealizationBoundary S))
    (_ht : t ∉ Set.range (coneAdjRealizationBoundary S))
    (he : coneAdjRealizationCell S z = coneAdjRealizationCell S t) : z = t := by
  cases' z with j x
  cases' t with k y
  by_cases hjk : j = k
  · subst k
    exact congrArg _ (orderNerveRealizationMap_injective
      _ _
      Subtype.val_injective he)
  · exact (hz ((coneAdjRealizationCell_boundary_iff S _).mp
      (coneAdjRealizationCell_inter_base S hjk x y he))).elim

/-- Every simplex is entirely old or is contained in one cone lower ideal. -/
theorem coneAdj_simplex_in_piece n
    (s : (nerve (ConeAdj S)).obj (Opposite.op n)) :
    (∀ i, s.obj i ∈ ConeAdjBase S) ∨
      ∃ j, ∀ i, s.obj i ∈ ConeAdjDisk S j := by
  have hlast (i : Fin (n.len + 1)) :=
    leOfHom (s.map (homOfLE i.le_last))
  cases he : s.obj (Fin.last n.len) with
  | inl p =>
      exact Or.inl (fun i => coneAdjBaseSet_down_closed
        (by tauto)
        (hlast i))
  | inr j =>
      aesop

theorem coneAdjRealization_piece_isQuotientMap :
    IsQuotientMap (Sum.elim (coneAdjRealizationOld S) (coneAdjRealizationCell S)) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective _ x
    rcases coneAdj_simplex_in_piece S n s with h | ⟨j, h⟩
    · exact ⟨Sum.inl (orderNerveRealizationSimplex _
        (orderNerveSimplexSubtype _ s h) z),
        orderNerveRealizationSimplex_subtype _ s h z⟩
    · exact ⟨Sum.inr ⟨j, orderNerveRealizationSimplex _
        (orderNerveSimplexSubtype _ s h) z⟩,
        orderNerveRealizationSimplex_subtype _ s h z⟩
  · intro T
    constructor
    · intro hT
      exact hT.preimage ((coneAdjRealizationOld S).continuous.sumElim
        (coneAdjRealizationCell S).continuous)
    · intro hT
      apply (orderNerveRealization_isClosed_iff _ T).mpr
      intro n s
      rcases coneAdj_simplex_in_piece S n s with h | ⟨j, h⟩
      · have hb := hT.preimage continuous_inl
        have ht := hb.preimage
          (orderNerveRealizationSimplex _
            (orderNerveSimplexSubtype _ s h)).hom.continuous
        convert ht using 1
        ext z
        exact iff_of_eq (congrArg _
          (orderNerveRealizationSimplex_subtype _ s h z).symm)
      · have hc := hT.preimage (continuous_inr.comp
          (continuous_sigmaMk (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)))
        have ht := hc.preimage
          (orderNerveRealizationSimplex _
            (orderNerveSimplexSubtype _ s h)).hom.continuous
        convert ht using 1
        ext z
        exact iff_of_eq (congrArg _
          (orderNerveRealizationSimplex_subtype _ s h z).symm)

/-- The topological attachment is the actual nerve realization, with
the actual old inclusion and the actual cone inclusions. -/
def coneAdjRealizationAttachmentHomeomorph :=
  RelativeAttachment.attachmentQuotientHomeomorph
    (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
    (coneAdjRealizationOld S) (coneAdjRealizationCell S)
    (coneAdjRealization_boundary_commutes S)
    (orderNerveRealizationMap_injective Subtype.val (by tauto) Subtype.val_injective)
    (coneAdjRealizationCell_boundary_iff S)
    (coneAdjRealizationCell_injective_off_boundary S)
    (coneAdjRealization_piece_isQuotientMap S)

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_old
    x :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.old (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationOld S x :=
  by rfl

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_cell
    x :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.cell (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationCell S x :=
  RelativeAttachment.attachmentQuotientHomeomorph_cell _ _ _ _ _ _ _ _ _ x
