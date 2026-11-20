module

public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Low-degree Herbrand quotients

The foundational constructions and their comparison with mathlib Tate
cohomology are split into focused modules.  This public module retains the
Herbrand quotient and its multiplicativity result.
-/

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- Herbrand-quotient theory the Herbrand-quotient definition: the Herbrand quotient of the actual
low-degree multiplicative Tate quotients.  The finiteness assumptions prevent
`Nat.card` from silently taking the value `0` on infinite quotients. -/
noncomputable def herbrandQuotient (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] : ℚ :=
  (Nat.card (HerbrandH0 G A) : ℚ) / (Nat.card (HerbrandHMinusOne G A σ) : ℚ)

section

variable (σ : G) [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]

/-- The Herbrand quotient is definitionally the ratio `#H⁰ / #H^{-1}`. -/
theorem herbrandQuotient_eq_card_ratio :
    herbrandQuotient (G := G) (A := A) σ =
      (Nat.card (HerbrandH0 G A) : ℚ) /
        (Nat.card (HerbrandHMinusOne G A σ) : ℚ) :=
  rfl

/-- If the actual low-degree quotients have the same finite cardinality, then
the Herbrand quotient is `1`. -/
theorem herbrandQuotient_eq_one_of_card_eq
    (hcard : Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)) :
    herbrandQuotient (G := G) (A := A) σ = 1 := by
  unfold herbrandQuotient
  rw [hcard]
  exact div_self (Nat.cast_ne_zero.mpr (Finite.card_pos).ne')

end

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: the Herbrand quotient of a finite
cyclic module is `1`. -/
theorem herbrandQuotient_finite_module_eq_one
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 := herbrandQuotient_eq_one_of_card_eq σ
    (herbrand_finite_module_card_eq σ hgen)

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: Herbrand quotient multiplicativity
for a short exact sequence of multiplicative `G`-modules, proved from the
standard two-periodic Tate complex and mathlib's homology long exact
sequence. -/
theorem herbrandQuotient_exact_multiplicative
    {G A B C : Type}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ := by
  unfold herbrandQuotient
  field_simp [(Nat.cast_ne_zero.mpr
    (Finite.card_pos).ne'), (Nat.cast_ne_zero.mpr
    (Finite.card_pos).ne'), (Nat.cast_ne_zero.mpr
    (Finite.card_pos).ne')]
  have hcardQ :
      (Nat.card (HerbrandH0 G B) : ℚ) *
          Nat.card (HerbrandHMinusOne G A σ) *
          Nat.card (HerbrandHMinusOne G C σ) =
        Nat.card (HerbrandH0 G A) *
          Nat.card (HerbrandH0 G C) *
          Nat.card (HerbrandHMinusOne G B σ) := by
    exact_mod_cast (herbrand_exact_cardinality_identity

      i j hi hj hker hinj hsurj σ hgen)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcardQ

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
