module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.IdealCharacter
public import Mathlib.NumberTheory.MulChar.Duality

@[expose] public section

namespace OAI

namespace SevenEighths.RayOrthogonality

open scoped Classical
noncomputable section

section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]

def characters (H : Subgroup Rˣ)  :=
  (MulChar.subgroupOrderIsoSubgroupMulChar R ℂ H).ofDual

instance (H : Subgroup Rˣ) : Fintype (characters H) := Fintype.ofFinite _

section
variable (H : Subgroup Rˣ)

theorem mem_characters_iff    χ  :
    χ ∈ characters H ↔ ∀ u ∈ H, χ u = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

theorem card_characters   :
    Fintype.card (characters H) = Nat.card (Rˣ ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

theorem exists_character_ne_one    {u}  (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by
  by_contra hn
  apply hu
  have hall : ∀ χ ∈ characters H, χ u = 1 := by
    simp_all
  have hh := (MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff).mpr hall
  simpa only [characters, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hh

theorem sum_characters_unit   (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hu : u ∈ H
  · simp only [hu, ite_true]
    calc
      _ = ∑ _χ : characters H, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        simp_all [mem_characters_iff]
      _ = _ := by simp [card_characters]
  · simp only [hu, ite_false]
    obtain ⟨χ, hχ⟩ := exists_character_ne_one H hu
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

def inUnitSubgroup (H : Subgroup Rˣ) (r : R)  :=
  ∃ u : Rˣ, (u : R) = r ∧ u ∈ H

theorem sum_characters    r  :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hi : inUnitSubgroup H (u : R) ↔ u ∈ H := by
      constructor
      · rintro ⟨v, hv, h⟩
        exact (Units.ext hv) ▸ h
      · exact fun h ↦ ⟨u, rfl, h⟩
    rw [sum_characters_unit, hi]
  · have hn : ¬ inUnitSubgroup H r := by
      rintro ⟨u, rfl, _⟩
      exact hr u.isUnit
    simp only [hn, ite_false]
    exact Finset.sum_eq_zero fun χ _ ↦ MulChar.map_nonunit χ.val hr

theorem ray_card_pos   : 0 < Nat.card (Rˣ ⧸ H) :=
  Nat.card_pos

end

end FiniteMonoid


variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]

def globalUnits  :=
  (Units.map (Ideal.Quotient.mk M).toMonoidHom).range

abbrev rayCharacters := characters (globalUnits M)

theorem mem_rayCharacters_iff  χ  :
    χ ∈ rayCharacters M ↔ IdealCharacter.UnitInvariant M χ := by
  rw [mem_characters_iff]
  constructor
  · intro h u
    exact h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact h v


variable [IsDomain A] [IsPrincipalIdealRing A]

def idealCharacter (χ : rayCharacters M)  :=
  IdealCharacter.ofResidue M χ ((mem_rayCharacters_iff M χ).mp χ.property)

theorem norm_idealCharacter_le_one  χ   I  :
    ‖idealCharacter M χ I‖ ≤ 1 := IdealCharacter.norm_ofResidue_le_one M χ _ I

theorem idealCharacter_one  I  :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I




end
end SevenEighths.RayOrthogonality

end OAI
