module

public import RequestProject.OrderNerveRealizationCover
public import RequestProject.OrderNerveRealizationNestedSubcomplex
public import RequestProject.ConeAdjBaseCover
public import RequestProject.PosetCoverLowerInterval
public import RequestProject.AttachmentQuotientHomeomorph

@[expose] public section

/-! The realization of a poset obtained by adjoining cone points is the
actual attachment of the realized lower ideals to the realized old part.
The family can be infinite: the quotient argument uses the simplexwise
weak topology, not a finite closed-cover assertion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)

abbrev ConeAdjBase := coneAdjBaseSet (S := S)
variable (j : J)

abbrev ConeAdjDisk := Set.Iic (ConeAdj.apex (S := S) j)
abbrev ConeAdjBoundary :=
  setOf (fun x : ConeAdjDisk S j => x.val ∈ ConeAdjBase S)

/-- The old boundary of a cone is exactly its strict lower interval. -/
def coneAdjBoundaryOrderIso : ConeAdjBoundary S j ≃o StrictBelow (ConeAdj.apex (S := S) j) where
  toFun x := ⟨x.val.val, lt_of_le_of_ne x.val.property (by
    intro h
    obtain ⟨p, hp⟩ := x.property
    exact Sum.inl_ne_inr (hp.trans h))⟩
  invFun x := ⟨⟨x.val, x.property.le⟩, by
    rcases x with ⟨q, hq⟩
    cases q with
    | inl p => solve_by_elim
    | inr k =>
        have hk := hq.le
        subst k
        exact (lt_irrefl _ hq).elim⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := Iff.rfl

def coneAdjRealizationOld :
    C(orderNerveRealization (ConeAdjBase S), orderNerveRealization (ConeAdj S)) :=
  ⟨orderNerveRealizationMap Subtype.val (fun _ _ h => h),
    (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom.continuous⟩

def coneAdjRealizationCell :
    C((Σ j, orderNerveRealization (ConeAdjDisk S j)),
      orderNerveRealization (ConeAdj S)) :=
  ⟨fun z => orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2,
    continuous_sigma (fun _ =>
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom.continuous)⟩

def coneAdjRealizationBoundary :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      (Σ j, orderNerveRealization (ConeAdjDisk S j))) :=
  ⟨fun z => ⟨z.1, orderNerveRealizationMap Subtype.val (fun _ _ h => h) z.2⟩,
    continuous_sigma (fun j => (continuous_sigmaMk
      (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)).comp
      (orderNerveRealizationMap Subtype.val
        (fun _ _ h => h)).hom.continuous)⟩

variable (j : J)

def coneAdjBoundaryToBase : ConeAdjBoundary S j → ConeAdjBase S :=
  fun x => ⟨x.val.val, x.property⟩

theorem coneAdjBoundaryToBase_monotone : Monotone (coneAdjBoundaryToBase S j) :=
  by solve_by_elim

def coneAdjRealizationAttaching :
    C((Σ j, orderNerveRealization (ConeAdjBoundary S j)),
      orderNerveRealization (ConeAdjBase S)) :=
  ⟨fun z => orderNerveRealizationMap _
      (coneAdjBoundaryToBase_monotone S z.1) z.2,
    continuous_sigma (fun j =>
      (orderNerveRealizationMap (coneAdjBoundaryToBase S j)
        (coneAdjBoundaryToBase_monotone S j)).hom.continuous)⟩

theorem coneAdjRealization_boundary_commutes
    (z : Σ j, orderNerveRealization (ConeAdjBoundary S j)) :
    coneAdjRealizationOld S (coneAdjRealizationAttaching S z) =
      coneAdjRealizationCell S (coneAdjRealizationBoundary S z) := by
  change orderNerveRealizationMap Subtype.val _
      (orderNerveRealizationMap _
        _ z.2) =
    orderNerveRealizationMap Subtype.val _
      (orderNerveRealizationMap Subtype.val _ z.2)
  rw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

theorem coneAdjRealizationOld_range :
    Set.range (coneAdjRealizationOld S) =
      orderNerveRealizationSupported _ (ConeAdjBase S) :=
  by apply orderNerveRealizationSubtype_range

theorem coneAdjRealizationBoundary_range (j : J)
    (x : orderNerveRealization (ConeAdjDisk S j)) :
    (⟨j, x⟩) ∈
        Set.range (coneAdjRealizationBoundary S) ↔
      x ∈ orderNerveRealizationSupported _ (ConeAdjBoundary S j) := by
  change _ ↔ x ∈ (orderNerveRealizationSubcomplex _
    (ConeAdjBoundary S j) : Set _)
  rw [← orderNerveRealizationSubtype_range (ConeAdjBoundary S j)]
  constructor
  · rintro ⟨⟨k, z⟩, h⟩
    have hk : k = j := congrArg Sigma.fst h
    subst k
    exact ⟨z, eq_of_heq (Sigma.mk.inj h).2⟩
  · rintro ⟨z, rfl⟩
    solve_by_elim

theorem coneAdjRealizationCell_boundary_iff
    (z : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationCell S z ∈ Set.range (coneAdjRealizationOld S) ↔
      z ∈ Set.range (coneAdjRealizationBoundary S) := by
  rcases z with ⟨j, x⟩
  rw [coneAdjRealizationOld_range, coneAdjRealizationBoundary_range]
  exact Set.ext_iff.mp
    (orderNerveRealizationSubtype_preimage_supported (ConeAdjDisk S j) (ConeAdjBase S)) x

section

variable {j k : J} (hjk : j ≠ k)
include hjk

theorem coneAdj_disks_inter_subset_base :
    ConeAdjDisk S j ∩ ConeAdjDisk S k ⊆ ConeAdjBase S := by
  rintro (p | l) ⟨hj, hk⟩
  · solve_by_elim
  · exact (hjk ((show l = j from hj).symm.trans (show l = k from hk))).elim

theorem coneAdjRealizationCell_inter_base
    (x : orderNerveRealization (ConeAdjDisk S j))
    (y : orderNerveRealization (ConeAdjDisk S k))
    (h : coneAdjRealizationCell S ⟨j, x⟩ = coneAdjRealizationCell S ⟨k, y⟩) :
    coneAdjRealizationCell S ⟨j, x⟩ ∈ Set.range (coneAdjRealizationOld S) := by
  rw [coneAdjRealizationOld_range]
  have hx : coneAdjRealizationCell S ⟨j, x⟩ ∈
      orderNerveRealizationSupported _ (ConeAdjDisk S j) := by
    change _ ∈ (orderNerveRealizationSubcomplex _ (ConeAdjDisk S j) :
      Set (orderNerveRealization (ConeAdj S)))
    rw [← orderNerveRealizationSubtype_range (ConeAdjDisk S j)] <;> aesop
  have hy : coneAdjRealizationCell S ⟨j, x⟩ ∈
      orderNerveRealizationSupported _ (ConeAdjDisk S k) := by
    change _ ∈ (orderNerveRealizationSubcomplex _ (ConeAdjDisk S k) :
      Set (orderNerveRealization (ConeAdj S)))
    rw [h, ← orderNerveRealizationSubtype_range (ConeAdjDisk S k)] <;> aesop
  intro p hp
  by_cases hpj : p ∈ ConeAdjDisk S j
  · apply hy p
    intro hpk
    exact hp (coneAdj_disks_inter_subset_base S hjk ⟨hpj, hpk⟩)
  · exact hx p hpj

end

theorem coneAdjRealizationCell_injective_off_boundary
    (z t : Σ j, orderNerveRealization (ConeAdjDisk S j))
    (hz : z ∉ Set.range (coneAdjRealizationBoundary S))
    (_ht : t ∉ Set.range (coneAdjRealizationBoundary S))
    (he : coneAdjRealizationCell S z = coneAdjRealizationCell S t) : z = t := by
  rcases z with ⟨j, x⟩
  rcases t with ⟨k, y⟩
  by_cases hjk : j = k
  · subst k
    exact congrArg _ (orderNerveRealizationMap_injective
      Subtype.val (fun _ _ h => h)
      Subtype.val_injective he)
  · exact (hz ((coneAdjRealizationCell_boundary_iff S ⟨j, x⟩).mp
      (coneAdjRealizationCell_inter_base S hjk x y he))).elim

/-- Every simplex is entirely old or is contained in one cone lower ideal. -/
theorem coneAdj_simplex_in_piece (n : SimplexCategory)
    (s : (nerve (ConeAdj S)).obj (Opposite.op n)) :
    (∀ i, s.obj i ∈ ConeAdjBase S) ∨
      ∃ j, ∀ i, s.obj i ∈ ConeAdjDisk S j := by
  have hlast (i : Fin _) :=
    leOfHom (s.map (homOfLE (Fin.le_last i)))
  cases he : s.obj _ with
  | inl p =>
      exact Or.inl (fun i => coneAdjBaseSet_down_closed
        (show s.obj (Fin.last n.len) ∈ ConeAdjBase S by solve_by_elim)
        (hlast i))
  | inr j =>
      exact Or.inr ⟨j, fun i => by
        aesop⟩

theorem coneAdjRealization_piece_isQuotientMap :
    IsQuotientMap (Sum.elim (coneAdjRealizationOld S) (coneAdjRealizationCell S)) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective _ x
    rcases coneAdj_simplex_in_piece S n s with h | ⟨j, h⟩
    · exact ⟨Sum.inl _,
        orderNerveRealizationSimplex_subtype _ s h z⟩
    · exact ⟨Sum.inr ⟨j, orderNerveRealizationSimplex (ConeAdjDisk S j)
        (orderNerveSimplexSubtype (ConeAdjDisk S j) s h) z⟩,
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
          (orderNerveRealizationSimplex (ConeAdjBase S)
            (orderNerveSimplexSubtype (ConeAdjBase S) s h)).hom.continuous
        convert ht using 1
        ext z
        exact iff_of_eq (congrArg (fun y => y ∈ T)
          (orderNerveRealizationSimplex_subtype (ConeAdjBase S) s h z).symm)
      · have hc := hT.preimage (continuous_inr.comp
          (continuous_sigmaMk (σ := fun k => orderNerveRealization (ConeAdjDisk S k)) (i := j)))
        have ht := hc.preimage
          (orderNerveRealizationSimplex (ConeAdjDisk S j)
            (orderNerveSimplexSubtype (ConeAdjDisk S j) s h)).hom.continuous
        convert ht using 1
        ext z
        exact iff_of_eq (congrArg (fun y => y ∈ T)
          (orderNerveRealizationSimplex_subtype (ConeAdjDisk S j) s h z).symm)

/-- The topological attachment is the actual nerve realization, with
the actual old inclusion and the actual cone inclusions. -/
def coneAdjRealizationAttachmentHomeomorph :=
  RelativeAttachment.attachmentQuotientHomeomorph
    _ _
    _ _
    (coneAdjRealization_boundary_commutes S)
    (orderNerveRealizationMap_injective Subtype.val (fun _ _ h => h) Subtype.val_injective)
    (coneAdjRealizationCell_boundary_iff S)
    (coneAdjRealizationCell_injective_off_boundary S)
    (coneAdjRealization_piece_isQuotientMap S)

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_old
    (x : orderNerveRealization (ConeAdjBase S)) :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.old (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationOld S x :=
  rfl

@[simp] theorem coneAdjRealizationAttachmentHomeomorph_cell
    (x : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationAttachmentHomeomorph S
      (RelativeAttachment.cell (coneAdjRealizationAttaching S)
        (coneAdjRealizationBoundary S) x) = coneAdjRealizationCell S x :=
  RelativeAttachment.attachmentQuotientHomeomorph_cell _ _ _ _ _ _ _ _ _ x

end FiniteChains.Comb
