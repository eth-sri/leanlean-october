module
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

end Moebius

theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by grind

theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by grind

theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by grind

end SevenEighths.InverseMoment

end OAI
