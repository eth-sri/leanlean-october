import Mathlib.Tactic

import RequestProject.SubstOneWay
import RequestProject.BlockSurfaceFilling
import Mathlib.GroupTheory.PushoutI

/-! Independent block receivers can be combined by a wide amalgamated product. -/

namespace FiniteChains.BlockFamily


variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  {ρ : Jr ⊕ Sx → FreeGroup α}
  {bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s)}

/-- Simultaneous substitution is injective when each block has its own marked receiver.
No common geometric attaching map, or finiteness of the family, is required. -/
theorem injective_substHomF_of_separate_receivers
    (hfill : FilledF ρ bsub) {G : Sx → Type v} [∀ s, Group (G s)]
    (j : ∀ s, PresGroup ρ →* G s) (hj : ∀ s, Function.Injective (j s))
    (b : ∀ s, FreeGroup (α ⊕ Zt s) →* G s)
    (hmark : ∀ s a, b s (FreeGroup.of (Sum.inl a)) =
      j s (QuotientGroup.mk (FreeGroup.of a)))
    (hrel : ∀ s m, b s (bsub s m) = 1) :
    Function.Injective (substHomF ρ bsub hfill) := by
  let B : BlockMaps ρ bsub (Monoid.PushoutI.base j) :=
    { b := fun s => (Monoid.PushoutI.of s).comp (b s)
      mark := fun s a => by
        simp_all [Monoid.PushoutI.of_apply_eq_base]
      rel := fun s m => by rw [MonoidHom.comp_apply, hrel s m, map_one] }
  exact B.injective_substHomF hfill (Monoid.PushoutI.base_injective hj)

end FiniteChains.BlockFamily

namespace FiniteChains.BlockFamily

variable {α Jr Sx : Type} {Zt Mt : Sx → Type}
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- Fillings using only the relators of their own block give simultaneous fillings. -/
theorem filledF_of_block_consequences
    (h : ∀ s, FreeGroup.map (Sum.inl (β := Zt s)) (ρ (Sum.inr s)) ∈
      Subgroup.normalClosure (Set.range (bsub s))) : FilledF ρ bsub := by
  intro s
  have hm : (FreeGroup.map (genEmb (Zt := Zt) s)).comp
      (FreeGroup.map (Sum.inl (β := Zt s))) =
      FreeGroup.map (Sum.inl (α := α) (β := Σ s, Zt s)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  rw [← DFunLike.congr_fun hm (ρ (Sum.inr s))]
  apply Davis.map_mem_normalClosure (FreeGroup.map (genEmb s)) ?_ (h s)
  rintro w ⟨m, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩

variable (s : Sx)
/-- Reindex the source so that just the selected entry is replaced. -/
def oneRel  : (Jr ⊕ {t : Sx // t ≠ s}) ⊕ PUnit.{1} → FreeGroup α :=
  Sum.elim (Sum.elim (fun r => ρ (Sum.inl r)) (fun t => ρ (Sum.inr t.val)))
    (fun _ => ρ (Sum.inr s))

theorem range_oneRel  : Set.range (oneRel ρ s) = Set.range ρ := by
  classical
  ext w
  constructor
  · aesop
  · rintro ⟨(r | t), rfl⟩
    · exact ⟨Sum.inl (Sum.inl r), rfl⟩
    · by_cases h : t = s
      · subst t; exact ⟨Sum.inr PUnit.unit, rfl⟩
      · aesop

/-- The reindexing preserves the group and every old word. -/
noncomputable def oneEquiv  : PresGroup ρ ≃* PresGroup (oneRel ρ s) :=
  QuotientGroup.congr _ _ (MulEquiv.refl _) (by
    simp_all [relSub, range_oneRel])



/-- Injectivity of every individual substitution implies injectivity of their simultaneous
substitution, even for an infinite or empty family of entries. -/
theorem injective_substHomF_of_individual
    (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (hinj : ∀ s, Function.Injective
      (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s))) :
    Function.Injective (substHomF ρ bsub hfill) := by
  let G s := PresGroup (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
  let j  := fun s =>
    (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)).comp
      (oneEquiv ρ s).toMonoidHom
  let b : ∀ s, FreeGroup (α ⊕ Zt s) →* G s := fun s =>
    (QuotientGroup.mk' _).comp
      (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit))
  apply injective_substHomF_of_separate_receivers hfill j
    (fun s => (hinj s).comp (oneEquiv ρ s).injective) b
  · intro s a
    rfl
  · intro s m
    apply (QuotientGroup.eq_one_iff _).2
    exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨PUnit.unit, m⟩, rfl⟩

end FiniteChains.BlockFamily
