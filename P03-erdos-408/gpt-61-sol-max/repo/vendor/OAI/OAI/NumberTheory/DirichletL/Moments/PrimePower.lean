module

public import OAI.NumberTheory.DirichletL.Moments.Correlation
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

def primePowerReduction (P : Ideal (𝓞 K)) {c } (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

theorem primePowerReduction_multiplicity (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply  P   {c}   hc 
     χ  (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl


variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

theorem primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ)  v k  :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl


end
end SevenEighths.CenteredMomentCorrelation

end OAI
