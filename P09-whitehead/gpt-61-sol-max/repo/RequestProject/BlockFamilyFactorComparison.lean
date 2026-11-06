import Mathlib.Tactic

import RequestProject.BlockFamilyAmalgamation

/-!
# Individual factors of a simultaneous substitution

The simultaneous substituted group is the actual wide amalgamated product of the
individual substituted groups over the original group.  Both comparison maps are
constructed here from the presentation and pushout universal properties.  In
particular, injectivity of every individual base map implies injectivity of every
individual factor in the simultaneous group, and hence of its group-ring map.

There is no finiteness or nonemptiness assumption on the family.  These are group
and group-ring comparison results; they do not assert the polygon coefficient
calculation or property (B2).

-/


namespace FiniteChains.BlockFamily

noncomputable section

variable {α Jr Sx : Type} {Zt Mt : Sx → Type}
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

variable (s : Sx)
/-- Replace only the selected original relator, retaining all other entries. -/
abbrev IndividualGroup  :=
  PresGroup (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))

/-- The actual inclusion of the generators of one individual substitution. -/
def individualGenEmb  :
    α ⊕ (Σ _ : PUnit.{1}, Zt s) → α ⊕ (Σ t : Sx, Zt t) :=
  Sum.elim Sum.inl (fun p => Sum.inr ⟨s, p.2⟩)

theorem individualGenEmb_old  (w : FreeGroup α) :
    FreeGroup.map (individualGenEmb (Zt := Zt) s)
        (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s)) w) =
      FreeGroup.map (Sum.inl (β := Σ t : Sx, Zt t)) w := by
  have h : (FreeGroup.map (individualGenEmb (α := α) (Zt := Zt) s)).comp
      (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s))) =
      FreeGroup.map (Sum.inl (β := Σ t : Sx, Zt t)) := by
    aesop
  exact DFunLike.congr_fun h w

theorem individualGenEmb_block  (w : FreeGroup (α ⊕ Zt s)) :
    FreeGroup.map (individualGenEmb (Zt := Zt) s)
        (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit) w) =
      FreeGroup.map (genEmb (Zt := Zt) s) w := by
  have h : (FreeGroup.map (individualGenEmb (α := α) (Zt := Zt) s)).comp
      (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit)) =
      FreeGroup.map (genEmb (Zt := Zt) s) := by
    aesop
  exact DFunLike.congr_fun h w

variable (hfill : FilledF ρ bsub)
/-- The canonical map of an individual substituted factor to the simultaneous group.
Its definition uses the genuine simultaneous fillings to kill the other old entries. -/
def factorToFamily  (s : Sx) :
    IndividualGroup ρ bsub s →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (individualGenEmb (Zt := Zt) s))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨k, rfl⟩
    change (QuotientGroup.mk (FreeGroup.map (individualGenEmb (Zt := Zt) s)
      (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) k)) :
      PresGroup (substPresF ρ bsub)) = 1
    rcases k with (r | ⟨p, m⟩)
    · rw [substPresF_inl, individualGenEmb_old]
      rcases r with (r | t)
      · exact (QuotientGroup.eq_one_iff _).2
          (Subgroup.subset_normalClosure ⟨Sum.inl r, rfl⟩)
      · aesop
    · cases p
      rw [substPresF_inr, individualGenEmb_block]
      exact (QuotientGroup.eq_one_iff _).2
        (Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩))



variable (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
/-- The original group maps to an individual factor by the single substitution,
with the original relator indexing restored. -/
def individualBase
    
    (s : Sx)  :=
  (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)).comp
    (oneEquiv ρ s).toMonoidHom





/-- The block free group maps to its own individual substituted factor. -/
def individualBlockFree  : FreeGroup (α ⊕ Zt s) →* IndividualGroup ρ bsub s :=
  (QuotientGroup.mk' _).comp
    (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit))

theorem individualBlockFree_mark
    
    (s : Sx) (a : α) :
    individualBlockFree ρ bsub s (FreeGroup.of (Sum.inl a)) =
      individualBase ρ bsub hone s (QuotientGroup.mk (FreeGroup.of a)) := rfl

theorem individualBlockFree_rel  (m : Mt s) :
    individualBlockFree ρ bsub s (bsub s m) = 1 := by
  apply (QuotientGroup.eq_one_iff _).2
  exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨PUnit.unit, m⟩, rfl⟩

/-- A concrete marked receiver in the wide amalgamated product of the individual factors. -/
def familyAmalgamMaps
     :
    BlockMaps ρ bsub (Monoid.PushoutI.base (individualBase ρ bsub hone)) where
  b s := (Monoid.PushoutI.of s).comp (individualBlockFree ρ bsub s)
  mark s a := by
    classical grind [MonoidHom.comp_apply, FiniteChains.BlockFamily.individualBlockFree_mark, Monoid.PushoutI.of_apply_eq_base]
  rel s m := by rw [MonoidHom.comp_apply, individualBlockFree_rel, map_one]

/-- The comparison from the simultaneous presentation to the actual wide pushout. -/
def familyToAmalgam
      :=
  (familyAmalgamMaps ρ bsub hone).psi

@[simp] theorem familyToAmalgam_old
     (a : α) :
    familyToAmalgam ρ bsub hone (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) =
      Monoid.PushoutI.base (individualBase ρ bsub hone)
        (QuotientGroup.mk (FreeGroup.of a)) := rfl



variable (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
/-- The factor comparison triangle identifies the composite with the genuine pushout injection. -/
theorem familyToAmalgam_comp_factor 
     (s : Sx) :
    (familyToAmalgam ρ bsub hone).comp (factorToFamily ρ bsub hfill s) =
      Monoid.PushoutI.of s := by
  have hw : ((familyToAmalgam ρ bsub hone).comp (factorToFamily ρ bsub hfill s)).comp
      (QuotientGroup.mk' _) =
      (Monoid.PushoutI.of (φ := individualBase ρ bsub hone) s).comp
        (QuotientGroup.mk' _) := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨p, z⟩)
    · change familyToAmalgam ρ bsub hone
        (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) =
          Monoid.PushoutI.of s
            (individualBase ρ bsub hone s (QuotientGroup.mk (FreeGroup.of a)))
      rw [familyToAmalgam_old, Monoid.PushoutI.of_apply_eq_base]
    · rfl
  aesop







/-- Each individual factor embeds when every individual substitution embeds the original group.
The only injectivity input concerns the already constructed individual base maps. -/
theorem factorToFamily_injective 
    
    (hinj : ∀ s, Function.Injective
      (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)))
    (s : Sx) : Function.Injective (factorToFamily ρ bsub hfill s) := by
  have hj : ∀ s, Function.Injective (individualBase ρ bsub hone s) :=
    fun t => (hinj t).comp (oneEquiv ρ t).injective
  have hs := Monoid.PushoutI.of_injective hj s
  intro x y hxy
  apply hs
  calc
    Monoid.PushoutI.of s x =
        familyToAmalgam ρ bsub hone (factorToFamily ρ bsub hfill s x) :=
      (DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) x).symm
    _ = familyToAmalgam ρ bsub hone (factorToFamily ρ bsub hfill s y) :=
      congrArg (familyToAmalgam ρ bsub hone) hxy
    _ = Monoid.PushoutI.of s y :=
      DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) y

end

end FiniteChains.BlockFamily
