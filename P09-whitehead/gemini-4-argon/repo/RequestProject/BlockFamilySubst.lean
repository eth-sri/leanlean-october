module

public import RequestProject.BlockSubstitutionMor

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.BlockFamily

open MonoidAlgebra

universe u

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

def genEmb (s : Sx) : α ⊕ Zt s → α ⊕ (Σ s : Sx, Zt s) :=
  Sum.map id (fun z => ⟨s, z⟩)

@[simp] theorem genEmb_inl (s : Sx) (i : α) :
    genEmb (Zt := Zt) s (Sum.inl i) = Sum.inl i := rfl

@[simp] theorem genEmb_inr (s : Sx) (z : Zt s) :
    genEmb (α := α) s (Sum.inr z) = Sum.inr ⟨s, z⟩ := rfl

theorem genEmb_injective (s : Sx) : Function.Injective (genEmb (α := α) (Zt := Zt) s) := by
  rintro (i | z) (i' | z') h
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · cases h
  · cases h
  · exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj (Sum.inr_injective h)).2)

theorem inr_ne_genEmb {s s' : Sx} (hs : s ≠ s') (z : Zt s') (x : α ⊕ Zt s) :
    (Sum.inr ⟨s', z⟩ : α ⊕ (Σ s : Sx, Zt s)) ≠ genEmb s x := by
  rcases x with i | w <;> simp [genEmb]
  exact fun h _ => hs h.symm

variable (ρ : Jr ⊕ Sx → FreeGroup α) (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

def substPresF : Jr ⊕ (Σ s : Sx, Mt s) → FreeGroup (α ⊕ (Σ s : Sx, Zt s)) :=
  Sum.elim (fun j => FreeGroup.map Sum.inl (ρ (Sum.inl j)))
    (fun p => FreeGroup.map (genEmb p.1) (bsub p.1 p.2))

@[simp] theorem substPresF_inl (j : Jr) :
    substPresF ρ bsub (Sum.inl j) = FreeGroup.map Sum.inl (ρ (Sum.inl j)) := rfl

@[simp] theorem substPresF_inr (p : Σ s : Sx, Mt s) :
    substPresF ρ bsub (Sum.inr p) = FreeGroup.map (genEmb p.1) (bsub p.1 p.2) := rfl

abbrev FilledF : Prop := ∀ s : Sx,
  FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) (ρ (Sum.inr s))
    ∈ Subgroup.normalClosure (Set.range (substPresF ρ bsub))

def substHomF (hfill : FilledF ρ bsub) : PresGroup ρ →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨j | s, rfl⟩
      · exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)
      · exact (QuotientGroup.eq_one_iff _).2 (hfill s))

variable (hfill : FilledF ρ bsub)

@[simp] theorem substHomF_mk (w : FreeGroup α) :
    substHomF ρ bsub hfill (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) w) := rfl

noncomputable def coeffF : MonoidAlgebra ℤ (PresGroup ρ) →+*
    MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)

theorem coeffF_quotRingHom (x : FreeGroupRing α) :
    coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) x)
      = quotRingHom ℤ (relSub (substPresF ρ bsub))
          (freeRingMap (Sum.inl (β := Σ s : Sx, Zt s)) x) := by
  show MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub ρ)) x)
    = MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (substPresF ρ bsub)))
        (MonoidAlgebra.mapDomainRingHom ℤ
          (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))) x)
  rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp']
  congr 1

section

variable [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]

theorem foxMatrix_inl_inl (i : α) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inl j)
      = coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inl j)) := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inl i) (substPresF ρ bsub (Sum.inl j)))
    = coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) (fox i (ρ (Sum.inl j))))
  rw [coeffF_quotRingHom, substPresF_inl, fox_map Sum.inl Sum.inl_injective]

theorem foxMatrix_inr_inl (w : Σ s : Sx, Zt s) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr w) (Sum.inl j) = 0 := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inr w) (substPresF ρ bsub (Sum.inl j))) = 0
  rw [substPresF_inl, fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero]

theorem foxMatrix_inr_inr_of_ne {s s' : Sx} (hs : s ≠ s') (z : Zt s') (m : Mt s) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr ⟨s, m⟩) = 0 := by
  show quotRingHom ℤ (relSub (substPresF ρ bsub))
      (fox (Sum.inr ⟨s', z⟩) (substPresF ρ bsub (Sum.inr ⟨s, m⟩))) = 0
  rw [substPresF_inr,
    fox_map_of_not_mem_range (genEmb s) (inr_ne_genEmb hs z), map_zero]

end

variable (c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))

noncomputable def cellsF (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    Jr ⊕ (Σ s : Sx, Mt s) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  Sum.elim (fun j => coeffF ρ bsub hfill (y (Sum.inl j)))
    (fun p => coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)

@[simp] theorem cellsF_inl (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) (j : Jr) :
    cellsF ρ bsub hfill c y (Sum.inl j) = coeffF ρ bsub hfill (y (Sum.inl j)) := rfl

@[simp] theorem cellsF_inr (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ))
    (p : Σ s : Sx, Mt s) :
    cellsF ρ bsub hfill c y (Sum.inr p)
      = coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2 := rfl

theorem cellsF_add (y y' : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsF ρ bsub hfill c (y + y') = cellsF ρ bsub hfill c y + cellsF ρ bsub hfill c y' := by
  funext k
  rcases k with j | p
  · exact map_add (coeffF ρ bsub hfill) _ _
  · show coeffF ρ bsub hfill (y (Sum.inr p.1) + y' (Sum.inr p.1)) * c p.1 p.2 = _
    rw [map_add, add_mul]; rfl

theorem cellsF_smul (x : MonoidAlgebra ℤ (PresGroup ρ))
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsF ρ bsub hfill c (x • y)
      = coeffF ρ bsub hfill x • cellsF ρ bsub hfill c y := by
  funext k
  rcases k with j | p
  · exact map_mul (coeffF ρ bsub hfill) _ _
  · show coeffF ρ bsub hfill (x * y (Sum.inr p.1)) * c p.1 p.2
      = coeffF ρ bsub hfill x * (coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)
    rw [map_mul, mul_assoc]


variable {ρ bsub hfill c}

theorem augPres_cellsF_eq_zero {y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ)}
    (hy : ∀ k, augPres ρ (y k) = 0) (k : Jr ⊕ (Σ s : Sx, Mt s)) :
    augPres (substPresF ρ bsub) (cellsF ρ bsub hfill c y k) = 0 := by
  have haug (x : MonoidAlgebra ℤ (PresGroup ρ)) :
      augPres (substPresF ρ bsub) (coeffF ρ bsub hfill x) = augPres ρ x :=
    augQ_mapDomain (substHomF ρ bsub hfill) x
  rcases k with j | p
  · rw [cellsF_inl, haug, hy (Sum.inl j)]
  · rw [cellsF_inr, map_mul, haug, hy (Sum.inr p.1), zero_mul]
