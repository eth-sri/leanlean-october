module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.Discriminant
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.IsAdjoinRoot

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# The Eisenstein polynomial of the `p`-power cyclotomic extension

For a primitive `p ^ m`-th root of unity `ζ`, with `m > 0`, the local
cyclotomic calculation proves that `ℚ_[p](ζ) / ℚ_[p]` is totally ramified of degree
`φ (p ^ m)`, identifies its Galois group with `(ZMod (p ^ m))ˣ`, identifies
its valuation ring with `ℤ_[p][ζ]`, and shows that `1 - ζ` is a prime
element of norm `p`.

The source is the translated cyclotomic Eisenstein polynomial
`Φ_{p^(k+1)}(X + 1)`.  We first transport its integral Eisenstein criterion
to the actual p-adic integer ring; no irreducibility or ramification
conclusion is assumed.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Polynomial
open scoped Polynomial

universe u








section
variable (p k : ℕ) [Fact p.Prime]
include p k
/-- The translated prime-power cyclotomic polynomial over the actual p-adic
integer ring. -/
def padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt
      : ℤ_[p][X] :=
  (cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)

theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map
      :
    padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k =
      (((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map
        (algebraMap ℤ ℤ_[p])) := by
  simp [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, Polynomial.map_comp]

/-- The translated cyclotomic polynomial remains Eisenstein after
completion from `ℤ` to `ℤ_[p]`. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt
      :
    (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).IsEisensteinAt
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])) := by
  let F : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)
  let G  := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k
  have hF : F.IsEisensteinAt (Ideal.span ({(p : ℤ)} : Set ℤ)) := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  have hGmonic : G.Monic := by
    dsimp [G, padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt]
    exact (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  refine hGmonic.isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top ((Ideal.span_singleton_prime PadicInt.prime_p.ne_zero).2
      PadicInt.prime_p)) ?_ ?_
  · intro i hi
    have hdeg : G.natDegree = F.natDegree := by
      change (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).natDegree = F.natDegree
      rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map]
      exact Polynomial.Monic.natDegree_map
        ((cyclotomic.monic (p ^ (k + 1)) ℤ).comp_X_add_C 1)
        (algebraMap ℤ ℤ_[p])
    have hmemF : F.coeff i ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      hF.mem (hdeg ▸ hi)
    rw [Ideal.mem_span_singleton] at hmemF ⊢
    change (p : ℤ_[p]) ∣ (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).coeff i
    rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map, coeff_map]
    obtain ⟨a, ha⟩ := hmemF
    refine ⟨(a : ℤ_[p]), ?_⟩
    simpa [F] using congrArg (algebraMap ℤ ℤ_[p]) ha
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    change (p : ℤ_[p]) ^ 2 ∣
      (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).coeff 0 at hdiv
    rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_eq_map, coeff_map] at hdiv
    have hdivZ  :=
      (PadicInt.pow_p_dvd_int_iff 2 (F.coeff 0)).mp hdiv
    exact hF.notMem (by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hdivZ)

/-- The translated polynomial is irreducible over `ℤ_[p]` by Eisenstein. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_irreducible
      :
    Irreducible (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k) := by
  have hei := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_isEisensteinAt p k
  have hprime :
      (Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p])).IsPrime :=
    (Ideal.span_singleton_prime PadicInt.prime_p.ne_zero).2 PadicInt.prime_p
  have hmonic : (padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k).Monic :=
    (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  apply hei.irreducible hprime hmonic.isPrimitive
  rw [padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt, natDegree_comp,
    show (X + 1 : ℤ_[p][X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic]
  exact (Nat.totient_pos.mpr (pow_pos (Fact.out : Nat.Prime p).pos _))

/-- The translated polynomial is irreducible over the p-adic field. -/
theorem padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible
      :
    Irreducible
      ((cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1)) := by
  let G := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt p k
  have hG : Irreducible G :=
    padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt_irreducible p k
  have hGmonic : G.Monic := (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1
  have hmap : Irreducible (G.map (algebraMap ℤ_[p] ℚ_[p])) :=
    hGmonic.irreducible_iff_irreducible_map_fraction_map.mp hG
  simpa [G, padicCyclotomicTotallyRamifiedShiftedCyclotomicPadicInt,
    Polynomial.map_comp] using hmap

/-- The prime-power cyclotomic polynomial is irreducible over `ℚ_[p]`.
This supplies the local irreducibility input for the ramification analysis. -/
theorem padicCyclotomicPolynomial_irreducible_prime_pow_succ
      :
    Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  let F : ℚ_[p][X] := cyclotomic (p ^ (k + 1)) ℚ_[p]
  have hs : Irreducible (F.comp (X + 1)) := padicCyclotomicTotallyRamifiedShiftedCyclotomicPadic_irreducible p k
  have hb := hs.map (Polynomial.algEquivAevalXAddC (-1 : ℚ_[p]))
  rw [Polynomial.algEquivAevalXAddC_apply, ← comp_eq_aeval] at hb
  simpa [F, comp_assoc] using hb
end


section CyclotomicExtension

variable {p k : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [Algebra ℚ_[p] L]

local instance padicCyclotomicTotallyRamifiedAlgebraPadicInt : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

local instance padicCyclotomicTotallyRamifiedScalarTowerPadicInt :
    IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A field generated over `ℚ_[p]` by the displayed primitive root is the
corresponding cyclotomic extension.  The generation hypothesis only spells
out the notation `ℚ_[p](ζ)`; none of the totally ramified cyclotomic theorem's conclusions is
assumed. -/
theorem padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (hgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] L := by
  let A := Algebra.adjoin ℚ_[p] ({ζ} : Set L)
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let hA : IsCyclotomicExtension {p ^ (k + 1)} ℚ_[p] A :=
    hζ.adjoin_isCyclotomicExtension ℚ_[p]
  let e  :=
    (Subalgebra.equivOfEq A ⊤ hgen).trans Subalgebra.topEquiv
  exact IsCyclotomicExtension.equiv {p ^ (k + 1)} ℚ_[p] A e

























































































































end CyclotomicExtension

end Valuations
end AlgebraicNumberTheory

end
