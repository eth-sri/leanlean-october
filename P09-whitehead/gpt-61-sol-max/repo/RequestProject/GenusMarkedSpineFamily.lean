import Mathlib.Tactic

import RequestProject.GenusMarkedSpineInjection
import RequestProject.BlockFamilyBlockwise

/-! Simultaneous substitution by the actual finite surviving two-dimensional spines. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)

noncomputable def familyFiniteSpineWordBlock (s : Sx)  :=
  finiteSpineWordBlock (q s) (u s) PUnit.unit

variable (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

include hrho in
/-- Each replaced word follows from its own genuine finite spine relators. -/
theorem familyFiniteSpineWordBlock_consequence (s : Sx) :
    FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s))) (ρ (Sum.inr s)) ∈
      Subgroup.normalClosure (Set.range (familyFiniteSpineWordBlock q u s)) := by
  let φ := blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
    (fun _ => u s) PUnit.unit
  have hv : φ (commWord (fun x => FreeGroup.of (Sum.inl x)) (finitePairs (q s))) =
      FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s))) (ρ (Sum.inr s)) := by
    aesop (add simp [map_commWord])
  rw [← hv]
  apply map_mem_normalClosure φ ?_ (markedSpine_surface_mem (q s))
  rintro v ⟨m, rfl⟩
  exact Subgroup.subset_normalClosure ⟨m, rfl⟩

include hrho in
abbrev familyFiniteSpineWordBlock_filled  :=
  FiniteChains.BlockFamily.filledF_of_block_consequences ρ (FiniteChains.Davis.Genus.familyFiniteSpineWordBlock q u)
    (FiniteChains.Davis.Genus.familyFiniteSpineWordBlock_consequence ρ q u hrho)

/-- The actual finite-spine structural inclusion is injective for every family,
including infinite families and independently varying genera. -/
abbrev familyFiniteSpineWordBlock_injective  :=
  FiniteChains.BlockFamily.injective_substHomF_of_individual ρ (FiniteChains.Davis.Genus.familyFiniteSpineWordBlock q u)
    (FiniteChains.Davis.Genus.familyFiniteSpineWordBlock_filled ρ q u hrho)
    (fun (s : Sx) =>
      FiniteChains.Davis.Genus.finiteSpineWordBlock_filled (FiniteChains.BlockFamily.oneRel ρ s) (q s) (u s) (hrho s))
    fun (s : Sx) =>
    FiniteChains.Davis.Genus.finiteSpineWordBlock_injective (FiniteChains.BlockFamily.oneRel ρ s) (q s) (u s) (hrho s)

end FiniteChains.Davis.Genus
