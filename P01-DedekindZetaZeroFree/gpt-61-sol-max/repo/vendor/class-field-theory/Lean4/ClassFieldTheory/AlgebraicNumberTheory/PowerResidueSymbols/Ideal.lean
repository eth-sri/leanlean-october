module

public import Mathlib

public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Power-residue symbols at prime ideals and integral ideals

Let `K` contain the `n`-th roots of unity and let `P` be a prime ideal
whose absolute norm is coprime to `n`.  Reduction identifies
`μₙ(𝓞 K)` with `μₙ(𝓞 K / P)`.  Pulling the finite-field symbol back along
this identification gives `(a/P)`.

For a nonzero integral ideal `I`, `(a/I)` is the finite product of
`(a/P)` raised to the multiplicity of `P` in `I`.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

noncomputable section

namespace AlgebraicNumberTheory
namespace PowerResidueSymbols

attribute [local instance] Ideal.Quotient.field

variable (K : Type*) [Field K] [NumberField K]

noncomputable local instance primeIdealResidueFintype
    (P : HeightOneSpectrum (𝓞 K)) :
    Fintype (𝓞 K ⧸ P.asIdeal) :=
  Fintype.ofFinite _

/-- Reduction of `n`-th roots of unity modulo an integral prime ideal. -/
def rootsOfUnityReduction
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rootsOfUnity n (𝓞 K) →*
      rootsOfUnity n (𝓞 K ⧸ P.asIdeal) where
  toFun z :=
    ⟨Ideal.rootsOfUnityMapQuot P.asIdeal n z, by
      change Ideal.rootsOfUnityMapQuot P.asIdeal n (z ^ n) = 1
      rw [show z ^ n = 1 by exact Subtype.ext z.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply map_one
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul (Ideal.rootsOfUnityMapQuot P.asIdeal n) z w

/-- Reduction on `μₙ` is injective away from `n`. -/
theorem rootsOfUnityReduction_injective
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    Function.Injective (rootsOfUnityReduction K P (n : ℕ)) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  intro z w hzw
  exact
    Ideal.rootsOfUnityMapQuot_injective
      (I := P.asIdeal) (n : ℕ)
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
      hcoprime
      (congrArg Subtype.val hzw)

section
variable (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
include P n hmu hcoprime
/-- If `K` contains `μₙ`, then `n` divides `N(P)-1` at every prime
`P ∤ n`. -/
theorem dvd_absNorm_sub_one_of_primitiveRoots
      :
    (n : ℕ) ∣ Ideal.absNorm P.asIdeal - 1 := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hmu
  have hzetaK  :=
    (mem_primitiveRoots n.pos).1 hzeta
  have hcard  :=
    hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have hinjective  :=
    Ideal.rootsOfUnityMapQuot_injective
      (I := P.asIdeal) (n : ℕ)
      (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top)
      hcoprime
  have hdvd :=
    Subgroup.card_dvd_of_injective
      (Ideal.rootsOfUnityMapQuot P.asIdeal (n : ℕ)) hinjective
  rw [hcard, Nat.card_units] at hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hdvd

/-- Away from `n`, reduction identifies the global integral `n`-th roots
of unity with the residue-field `n`-th roots of unity. -/
noncomputable def rootsOfUnityReductionEquiv
      :
    rootsOfUnity (n : ℕ) (𝓞 K) ≃*
      rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  letI : Fintype (rootsOfUnity (n : ℕ) (𝓞 K)) :=
    Fintype.ofFinite _
  let f := rootsOfUnityReduction K P (n : ℕ)
  have hinjective : Function.Injective f :=
    rootsOfUnityReduction_injective K P n hcoprime
  let zeta := Classical.choose hmu
  have hzeta := Classical.choose_spec hmu
  have hzetaK : IsPrimitiveRoot zeta (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hzeta
  have hsource :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K)) = (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    exact hzetaK.toInteger_isPrimitiveRoot.card_rootsOfUnity
  have htarget_le :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) ≤
        (n : ℕ) := by
    rw [← Nat.card_eq_fintype_card]
    apply card_rootsOfUnity
  have hsource_le_target  :=
    Fintype.card_le_of_injective f hinjective
  have htarget :
      Fintype.card (rootsOfUnity (n : ℕ) (𝓞 K ⧸ P.asIdeal)) =
        (n : ℕ) :=
    Nat.le_antisymm htarget_le (by simpa [hsource] using hsource_le_target)
  exact MulEquiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hinjective, hsource.trans htarget.symm⟩)

/-- The reduction equivalence acts by the canonical reduction homomorphism. -/
@[simp]
theorem rootsOfUnityReductionEquiv_apply
     
    (zeta : rootsOfUnity (n : ℕ) (𝓞 K)) :
    rootsOfUnityReductionEquiv K P n hmu hcoprime zeta =
      rootsOfUnityReduction K P (n : ℕ) zeta :=
  rfl
end


/-- The cardinality of the residue field is the absolute norm of the
prime ideal. -/
theorem card_primeIdealResidueField
    (P : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (𝓞 K ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
  rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- An algebraic integer prime to `P`, regarded as a unit of the residue
field. -/
def primeIdealResidueUnit
    (P : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    (𝓞 K ⧸ P.asIdeal)ˣ :=
  Units.mk0 (Ideal.Quotient.mk P.asIdeal a)
    (by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact ha)












section
variable (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hcoprime : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (a : 𝓞 K) (ha : a ∉ P.asIdeal)
include P n hmu hcoprime a ha
/-- The `n`-th power-residue symbol `(a/P)`, valued in the common group
`μₙ(𝓞 K)`. -/
noncomputable def primeIdealPowerResidueSymbol
      :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField K P]
    apply dvd_absNorm_sub_one_of_primitiveRoots <;> assumption
  (rootsOfUnityReductionEquiv K P n hmu hcoprime).symm
    (finiteFieldPowerResidueSymbol
      (𝓞 K ⧸ P.asIdeal) n hn
      (primeIdealResidueUnit K P a ha))

/-- Reduction sends `(a/P)` to the finite-field formula
`a^((N(P)-1)/n)`. -/
theorem rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol
      :
    let hn : (n : ℕ) ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) - 1 := by
      rw [card_primeIdealResidueField K P]
      apply dvd_absNorm_sub_one_of_primitiveRoots <;> assumption
    rootsOfUnityReductionEquiv K P n hmu hcoprime
        (primeIdealPowerResidueSymbol K P n hmu hcoprime a ha) =
      finiteFieldPowerResidueSymbol
        (𝓞 K ⧸ P.asIdeal) n hn
        (primeIdealResidueUnit K P a ha) := by
  dsimp only [primeIdealPowerResidueSymbol]
  exact (rootsOfUnityReductionEquiv K P n hmu hcoprime).apply_symm_apply _
end


























































/-- Multiplicity of `P` in the prime factorization of a nonzero integral
ideal. -/
def idealPrimeMultiplicity
    (P : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))  :=
  (Associates.mk P.asIdeal).count (Associates.mk I).factors




























/-- The finite set of height-one primes dividing a nonzero denominator ideal.

Naming this set keeps every finite-product presentation on the same subtype,
instead of asking typeclass inference to reconstruct definitionally equal
subtypes from separate predicate expressions. -/
def idealPrimeDivisors (I : Ideal (𝓞 K)) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {P | P.asIdeal ∣ I}






































































































































































































































































































end PowerResidueSymbols
end AlgebraicNumberTheory

end
