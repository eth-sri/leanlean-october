import Mathlib.Tactic

import RequestProject.GenusMarkedSpineFamily
import RequestProject.GenusCappedSpineFox
import RequestProject.BlockSubstitutionFoxCoordinates
import RequestProject.NamedPresentationRelativeBoundary

/-! Exact relative boundary of a genuinely substituted finite genus spine. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
open scoped Classical

variable (q₀ : ℕ) [NeZero q₀]

/-- Reordering distinguished and internal generators in the actual presentation. -/
noncomputable def spineReorderHom : PresGroup (namedSpinePresentation q₀) →*
    PresGroup (markedSpineBeta q₀) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (markedSpineBeta q₀))).comp (FreeGroup.map Sum.swap)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩))

theorem spineReorderHom_coeff (x : FreeGroupRing (NamedSpineGen q₀)) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q₀)
      (quotRingHom ℤ (relSub (namedSpinePresentation q₀)) x) =
    quotRingHom ℤ (relSub (markedSpineBeta q₀)) (freeRingMap Sum.swap x) := by
  unfold FiniteChains.quotRingHom FiniteChains.freeRingMap
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

theorem spineReorderHom_fox_internal (z : SpinePresentationGen q₀) (m : NamedSpineRel q₀) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q₀)
      (foxMatrixPres (namedSpinePresentation q₀) (Sum.inl z) m) =
    foxMatrixPres (markedSpineBeta q₀) (Sum.inr z) m := by
  rw [foxMatrixPres, spineReorderHom_coeff, foxMatrixPres]
  change _ = quotRingHom ℤ _
    (fox (Sum.swap (Sum.inl z)) (FreeGroup.map Sum.swap (namedSpinePresentation q₀ m)))
  rw [fox_map Sum.swap (Equiv.sumComm _ _).injective]

variable {A Jr S : Type} (ρ : Jr ⊕ S → FreeGroup A)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup A)

variable (s : S)
/-- The constructed receiver from the genuine named spine into the actual
simultaneously substituted group. No injectivity of this receiver is asserted. -/
noncomputable def familySpineHom  : PresGroup (namedSpinePresentation (q s)) →*
    PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  (markedBlockHom ρ u (fun s => markedSpineBeta (q s)) s).comp (spineReorderHom (q s))

set_option maxHeartbeats 500000 in
theorem familySpine_matrix_internal  (z : SpinePresentationGen (q s))
    (m : NamedSpineRel (q s)) :
    foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
    MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
      (foxMatrixPres (namedSpinePresentation (q s)) (Sum.inl z) m) := by
  have h := foxMatrix_markedBlock_internal (Z := fun s => SpinePresentationGen (q s))
    ρ u (fun s => markedSpineBeta (q s)) s z m
  rw [← spineReorderHom_fox_internal, BlockMor.mapDomainRingHom_comp'] at h
  convert h using 1 <;>
    simp only [blockSubst] <;> rfl

variable (β : NamedSpineRel (q s) → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
/-- The actual internal Fox boundary equals the boundary of the named spine
over precisely the group ring of the simultaneous substitution. -/
theorem familySpine_internalBoundary 
    
    (z : SpinePresentationGen (q s)) :
    (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) =
    NamedPresentation.receivedFoxBoundary (spinePresentation (q s))
      (spinePresentationMarkedWord (q s)) (familySpineHom ρ q u s) β (Sum.inl z) := by
  unfold NamedPresentation.receivedFoxBoundary
  exact Finset.sum_congr (by ext; simp) (fun m _ => congrArg (β m * ·)
    (familySpine_matrix_internal ρ q u s z m))

/-- The hypothesis on one block in B2 is exactly a prescribed marked boundary
in its original spine presentation, with the full group-ring coefficients. -/
theorem familySpine_internal_zero_iff 
     :
    (∀ z : SpinePresentationGen (q s),
      (∑ m, β m * foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) ↔
    ∀ z : SpinePresentationGen (q s),
      (∑ j, β (Sum.inl j) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentation (q s) j))) =
      ∑ i, β (Sum.inr i) * NamedPresentation.receivedWordCoefficientMap
        (spinePresentation (q s)) (spinePresentationMarkedWord (q s))
        (familySpineHom ρ q u s) (fox z (spinePresentationMarkedWord (q s) i)) := by
  simp_all [FiniteChains.Davis.Genus.familySpine_internalBoundary, FiniteChains.NamedPresentation.receivedFoxBoundary_internal_zero_iff]

end FiniteChains.Davis.Genus
