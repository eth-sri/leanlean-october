module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem finite_ideals_absNorm_le (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X}.Finite := by
  rcases lt_or_ge X 0 with hX | hX
  · refine Set.finite_empty.subset ?_
    rintro I hI
    exact absurd (le_trans (Nat.cast_nonneg (Ideal.absNorm I)) hI) (not_le.mpr hX)
  · refine (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset ?_
    rintro I hI
    exact (Nat.le_floor_iff hX).mpr hI

noncomputable def boundedNormIdeals (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  (finite_ideals_absNorm_le F X).toFinset

@[simp]
theorem mem_boundedNormIdeals {F : Type*} [Field F] [NumberField F]
    {X : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ boundedNormIdeals F X ↔ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [boundedNormIdeals, Set.Finite.mem_toFinset]
  rfl

theorem boundedNormIdeals_mono (F : Type*) [Field F] [NumberField F]
    {X Y : ℝ} (hXY : X ≤ Y) :
    boundedNormIdeals F X ⊆ boundedNormIdeals F Y := by
  intro I hI
  rw [mem_boundedNormIdeals] at hI ⊢
  exact le_trans hI hXY
