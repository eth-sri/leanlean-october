module
import Mathlib
public import OAI.NumberTheory.DirichletL.ConductorBounds
public import OAI.NumberTheory.DirichletL.CharacterTransport

@[expose] public section

namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]



end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

section Transport

variable {A : Type*} [CommRing A]

section
variable (M : Ideal A) (I : Ideal (A ⧸ M))
include M I

section
variable (φ : MulChar ((A ⧸ M) ⧸ I) ℂ)
include φ

def quotientCharacter  : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ

@[simp] theorem quotientCharacter_mk  (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl

theorem primitive_quotientCharacter  (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ
end


theorem source_le_comap  :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem
end


end Transport

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]

section
variable (M : Ideal A) [Finite (A ⧸ M)]
include M

theorem comap_ne_bot  (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  let : Finite ((A ⧸ M) ⧸ I) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hpos : 0 < (I.comap (Ideal.Quotient.mk M)).absNorm := by
    rw [absNorm_comap_eq_quotient_card]
    exact Nat.card_pos
  intro hzero
  simp_all

section
variable (χ : MulChar (A ⧸ M) ℂ)
include χ

theorem exists_primitive_presentation_above_quotient
    
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ J.comap (Ideal.Quotient.mk M) ≤ K ∧ K ≠ ⊥ ∧
      IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, ψ, hJI, hψ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_quotient_above_with_norm_and_mask M χ J hJ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I ψ,
    source_le_comap M I, Ideal.comap_mono hJI, comap_ne_bot M I,
    primitive_quotientCharacter M I ψ hprimitive, hnorm, ?_⟩
  simp_all <;> nlinarith

theorem exists_primitive_presentation  :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm
end
end









