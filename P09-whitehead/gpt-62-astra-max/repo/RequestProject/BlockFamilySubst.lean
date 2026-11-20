module

public import RequestProject.BlockSubstitutionMor

@[expose] public section

/-!
# Rule 3 for a family of simultaneously replaced entries

`RequestProject/BlockSubstitutionMor.lean` formalises the substitution of one block for one
labelled relator entry (`FiniteChains.BlockMor.substMor`).  The article's property (B2) is
stated for an **arbitrary family** of labelled entries replaced at the same time, each by its
own block with its own copy of the internal generators; the family form is what rule 3 uses,
because rule 3 replaces all extra entries of a presentation simultaneously.

This file carries out that generalisation.  The source presentation is written as

  `ρ : Jr ⊕ Sx → FreeGroup α`,

the entries indexed by `Sx` being the ones that are replaced and the entries indexed by `Jr`
the retained ones (every family of labelled entries of a presentation is of this shape after
reindexing).  For each `s : Sx` a block is given by its own set `Zt s` of internal generators
and its own set `Mt s` of relator entries,

  `bsub s : Mt s → FreeGroup (α ⊕ Zt s)`,

and the substituted presentation of the article, equation (3.4) in its simultaneous form, is

  `substPresF ρ bsub : Jr ⊕ (Σ s, Mt s) → FreeGroup (α ⊕ (Σ s, Zt s))`.

What is proved here is that this simultaneous substitution is a *structural map* in the sense
of `RequestProject/GenerationStep.lean`:

* `FiniteChains.BlockFamily.substHomF` — the induced homomorphism of fundamental groups,
  available as soon as every replaced relator dies in the substituted presentation
  (`FiniteChains.BlockFamily.FilledF`, the algebraic shadow of the chosen surface fillings
  of (B1));
* `FiniteChains.BlockFamily.cellsF` — the induced map on the two-chains of the universal
  covers: a retained two-cell keeps its coefficient, and the coefficient of a replaced
  two-cell is spread over its own block along that block's filling chain `c s`;
* `FiniteChains.BlockFamily.substMorF` — the two together form a `FiniteChains.PresMor`:
  the map is additive and semilinear, carries Fox cycles to Fox cycles and preserves zero
  augmentations.

As in the one-entry case, nothing here proves property (B2) itself: that is the subject of
`RequestProject/BlockFamilyChainModel.lean`, where the chain model of the double mapping
cylinder of the whole family is built over this structural map.

Since the ambient framework of the project is that of finite presentations (the Fox boundary
is a finite sum over the relator entries), `Sx` is a finite index type here; within a finite
presentation an arbitrary set of labelled entries is of this form.
-/

noncomputable section

namespace FiniteChains

namespace BlockFamily

open MonoidAlgebra

universe u

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}

variable (s : Sx)

/-- The generators used by the block substituted at the entry `s`: the old generators
together with the copy `Zt s` of the internal generators belonging to `s`. -/
def genEmb : α ⊕ Zt s → α ⊕ (Σ s : Sx, Zt s) :=
  Sum.map id (fun z => ⟨s, z⟩)

@[simp] theorem genEmb_inl (i : α) :
    genEmb (Zt := Zt) s (Sum.inl i) = Sum.inl i := rfl

@[simp] theorem genEmb_inr (z : Zt s) :
    genEmb (α := α) s (Sum.inr z) = Sum.inr ⟨s, z⟩ := rfl

theorem genEmb_injective : Function.Injective (genEmb (α := α) (Zt := Zt) s) := by
  rintro (i | z) (i' | z') h <;> simp_all

/-- A generator belonging to another block, or an internal generator of a different entry,
is outside the range of `genEmb s`. -/
theorem inr_ne_genEmb {s s' : Sx} (hs : s ≠ s') (z : Zt s') (x : α ⊕ Zt s) :
    (Sum.inr ⟨s', z⟩) ≠ genEmb s x := by
  aesop

variable (ρ : Jr ⊕ Sx → FreeGroup α) (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- **The simultaneous substitution (3.4).**  The retained relators, read in the free group
on the old generators and all the new internal generators, together with the relators of the
blocks substituted at the entries of `Sx`. -/
def substPresF : Jr ⊕ (Σ s : Sx, Mt s) → FreeGroup (α ⊕ (Σ s : Sx, Zt s)) :=
  Sum.elim (fun j => FreeGroup.map Sum.inl (ρ (Sum.inl j)))
    (fun p => FreeGroup.map (genEmb p.1) (bsub p.1 p.2))

@[simp] theorem substPresF_inl (j : Jr) :
    substPresF ρ bsub (Sum.inl j) = FreeGroup.map Sum.inl (ρ (Sum.inl j)) := rfl

@[simp] theorem substPresF_inr (p : Σ s : Sx, Mt s) :
    substPresF ρ bsub (Sum.inr p) = FreeGroup.map (genEmb p.1) (bsub p.1 p.2) := rfl

/-- The hypothesis supplied by the chosen fillings of (B1): every replaced relator is a
consequence of the relators of the substituted presentation. -/
abbrev FilledF := ∀ s : Sx,
  FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) (ρ (Sum.inr s))
    ∈ Subgroup.normalClosure (Set.range (substPresF ρ bsub))

/-- **The structural map on fundamental groups** of the simultaneous substitution. -/
def substHomF (hfill : FilledF ρ bsub) : PresGroup ρ →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨k, rfl⟩
      cases k with
      | inl j =>
          exact (QuotientGroup.eq_one_iff _).2
            (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)
      | inr s => exact (QuotientGroup.eq_one_iff _).2 (hfill s))

variable (hfill : FilledF ρ bsub)

@[simp] theorem substHomF_mk (w : FreeGroup α) :
    substHomF ρ bsub hfill (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s)) w) := rfl

/-- The coefficient homomorphism of the structural map. -/
def coeffF :=
  MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)

section Fox

variable [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr]
  [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype (Mt s)]

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype _] in
theorem coeffF_quotRingHom (x : FreeGroupRing α) :
    coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) x)
      = quotRingHom ℤ (relSub _)
          (freeRingMap (Sum.inl (β := Σ s : Sx, Zt s)) x) := by
  show MonoidAlgebra.mapDomainRingHom ℤ (substHomF ρ bsub hfill)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub ρ)) x)
    = MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' _)
        (MonoidAlgebra.mapDomainRingHom ℤ
          (FreeGroup.map (Sum.inl (β := Σ s : Sx, Zt s))) x)
  rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp']
  rfl

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype _] in
/-- **A retained relator contributes the old Fox matrix.** -/
theorem foxMatrix_inl_inl (i : α) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inl j)
      = coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inl j)) := by
  show quotRingHom ℤ (relSub _)
      _
    = coeffF ρ bsub hfill (quotRingHom ℤ (relSub ρ) (fox i (ρ (Sum.inl j))))
  rw [coeffF_quotRingHom, substPresF_inl, fox_map Sum.inl Sum.inl_injective]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype _] in
/-- **A retained relator has no derivative in an internal generator.** -/
theorem foxMatrix_inr_inl (w : Σ s : Sx, Zt s) (j : Jr) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr w) (Sum.inl j) = 0 := by
  show quotRingHom ℤ (relSub _)
      _ = 0
  simp_all [substPresF_inl, fox_map_of_not_mem_range]

omit [Fintype α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [∀ s, Fintype (Zt s)]
  [∀ s, Fintype _] in
/-- **A block relator has no derivative in the internal generators of another block.**  This
is what makes the simultaneous replacement of a whole family behave like a single one: the
blocks do not interfere. -/
theorem foxMatrix_inr_inr_of_ne {s s' : Sx} (hs : s ≠ s') (z : Zt s') (m : Mt s) :
    foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s', z⟩) (Sum.inr ⟨s, m⟩) = 0 := by
  show quotRingHom ℤ (relSub _)
      _ = 0
  simp_all [substPresF_inr, fox_map_of_not_mem_range, inr_ne_genEmb]

/-! ### The structural map on two-chains -/

variable (c : ∀ s : Sx, Mt s → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)))

variable (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ))

/-- The map on two-chains induced by the simultaneous substitution: a retained two-cell keeps
its coefficient, the coefficient of the two-cell replaced at `s` is spread over the block at
`s` along the filling chain `c s`. -/
def cellsF :
    Jr ⊕ (Σ s : Sx, Mt s) → MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub)) :=
  Sum.elim (fun j => coeffF ρ bsub hfill (y (Sum.inl j)))
    (fun p => coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2)

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype _] in
@[simp] theorem cellsF_inl (j : Jr) :
    cellsF ρ bsub hfill c y (Sum.inl j) = coeffF ρ bsub hfill (y (Sum.inl j)) := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype _] in
@[simp] theorem cellsF_inr
    (p : Σ s : Sx, Mt s) :
    cellsF ρ bsub hfill c y (Sum.inr p)
      = coeffF ρ bsub hfill (y (Sum.inr p.1)) * c p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype _] in
theorem cellsF_add (y y' : Jr ⊕ Sx → MonoidAlgebra ℤ _) :
    cellsF ρ bsub hfill c (y + y') = cellsF ρ bsub hfill c y + cellsF ρ bsub hfill c y' := by
  funext k
  cases k with
  | inl j =>
      show coeffF ρ bsub hfill (y (Sum.inl j) + y' (Sum.inl j)) = _
      rw [map_add]; rfl
  | inr p =>
      show coeffF ρ bsub hfill (y (Sum.inr p.1) + y' (Sum.inr p.1)) * c p.1 p.2 = _
      rw [map_add, add_mul]; rfl

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype _] in
theorem cellsF_smul (x : MonoidAlgebra ℤ _)
    (y : Jr ⊕ Sx → MonoidAlgebra ℤ _) :
    cellsF ρ bsub hfill c (x • y)
      = coeffF ρ bsub hfill x • cellsF ρ bsub hfill c y := by
  funext k
  cases k with
  | inl j =>
      simp
  | inr p =>
      simp [map_mul, mul_assoc]

/-- The boundary conditions on the family of filling chains: for every replaced entry the
cellular boundary of its filling chain is the boundary of the replaced two-cell. -/
structure IsFillingF : Prop where
  /-- On an old generator the boundary of the filling chain at `s` is the Fox derivative of
  the relator replaced at `s`. -/
  base : ∀ (s : Sx) (i : α),
    ∑ m : Mt s, c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)
      = coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s))
  /-- On an internal generator of its own block the boundary of the filling chain
  vanishes. -/
  internal : ∀ (s : Sx) (z : Zt s),
    ∑ m : Mt s, c s m * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)
      = 0

variable {ρ bsub hfill c}

section

variable (hc : IsFillingF ρ bsub hfill c)
include hc

variable (y : Jr ⊕ Sx → MonoidAlgebra ℤ (PresGroup ρ))

end

omit [Fintype α] [DecidableEq α] [Fintype Jr] [DecidableEq Jr] [Fintype Sx] [DecidableEq Sx]
  [∀ s, Fintype (Zt s)] [∀ s, DecidableEq (Zt s)] [∀ s, Fintype _] in
/-- **The simultaneous substitution preserves zero augmentations** (naturality of the
Hurewicz map). -/
theorem augPres_cellsF_eq_zero {y : Jr ⊕ Sx → MonoidAlgebra ℤ _}
    (hy : ∀ k, augPres ρ (y k) = 0) (k : Jr ⊕ (Σ s : Sx, Mt s)) :
    augPres _ (cellsF ρ bsub hfill c y k) = 0 := by
  have haug : ∀ x : MonoidAlgebra ℤ _,
      augPres _ (coeffF ρ bsub hfill x) = augPres ρ x :=
    fun x => augQ_mapDomain _ x
  cases k with
  | inl j => grind [cellsF_inl]
  | inr p => simp [cellsF_inr, map_mul, haug, hy, zero_mul]

variable (ρ bsub hfill c)

variable (hc : IsFillingF ρ bsub hfill c)

end Fox

end BlockFamily

end FiniteChains
