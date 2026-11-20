module

public import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Mathlib.Algebra.Polynomial.Lifts

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Integral closure for a unique discrete valuation extension

This file supplies the noncomplete integral-closure input used in
ramification-number theory.  For a finite Galois extension with a uniquely chosen
extension of the base discrete valuation, the Galois orbit polynomial of an
integer has coefficients in the base valuation ring.  Consequently the target
valuation ring is integral, hence finite, over the base valuation ring.

No completeness or Henselian hypothesis is used.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF
open ValuationTheory.DiscreteValuationField.Valuation
open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

/-- The full Galois-orbit polynomial of an element of the target valuation
ring.  Uniqueness of the valuation extension makes every factor integral. -/
def integralOrbitPolynomial
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) : Polynomial target.valuationSubring := ∏ σ : Gal(L/K),
    (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
          huniq σ a))

omit [IsGalois K L] in
/-- States the theorem `integralOrbitPolynomial_monic`. -/
theorem integralOrbitPolynomial_monic
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) :
    (integralOrbitPolynomial
      (base := base) (target := target) huniq a).Monic := by
  classical
  solve_by_elim [Polynomial.monic_X_sub_C, Polynomial.monic_prod_of_monic]

omit [IsGalois K L] in
/-- The orbit polynomial is invariant under every Galois automorphism. -/
theorem integralOrbitPolynomial_map_valuationSubringAut
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) (ρ : Gal(L/K)) :
    (integralOrbitPolynomial
        (base := base) (target := target) huniq a).map
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq ρ).toRingHom =
      integralOrbitPolynomial
        (base := base) (target := target) huniq a := by
  classical
  change
    (∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
          huniq σ a))).map
      (valuationSubringAutOfUniqueExtension
          huniq ρ).toRingHom =
    ∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
          huniq σ a))
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  refine Fintype.prod_equiv (Equiv.mulLeft ρ)
    (fun σ : Gal(L/K) =>
      Polynomial.X - Polynomial.C
        ((valuationSubringAutOfUniqueExtension
            huniq ρ).toRingHom
          (valuationSubringAutOfUniqueExtension
              huniq σ a)))
    (fun σ : Gal(L/K) =>
      Polynomial.X - Polynomial.C
        (valuationSubringAutOfUniqueExtension
            huniq σ a)) ?_
  intro σ
  apply congrArg (fun z : target.valuationSubring =>
    Polynomial.X - Polynomial.C z)
  exact
    (congrFun
      (RingEquiv.coe_toRingHom
        (valuationSubringAutOfUniqueExtension
            huniq ρ))
      (valuationSubringAutOfUniqueExtension
          huniq σ a)).trans
      (valuationSubringAutOfUniqueExtension_mul_apply
          huniq ρ σ a).symm

section

variable (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)

/-- Every coefficient of the integral orbit polynomial descends to the base
valuation ring. -/
theorem integralOrbitPolynomial_coeff_mem_range
    (a : target.valuationSubring) (n : ℕ) :
    (integralOrbitPolynomial
        (base := base) (target := target) huniq a).coeff n ∈
      Set.range (algebraMap base.valuationSubring target.valuationSubring) := by
  let c :=
    (integralOrbitPolynomial
        huniq a).coeff n
  have hfixed : ∀ σ : Gal(L/K), σ (c : L) = (c : L) := by
    intro σ
    have hmap := congrArg
      (fun p : Polynomial target.valuationSubring => p.coeff n)
      (integralOrbitPolynomial_map_valuationSubringAut
          huniq a σ)
    simpa [c] using congrArg Subtype.val hmap
  obtain ⟨b, hb⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed
        (c : L)).2 hfixed
  have hbmem : base.valuation b ≤ 1 := by
    apply (_root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := base.valuation) (vA := target.valuation) b).1
    rw [hb]
    exact c.property
  exact Exists.intro ⟨b, hbmem⟩ (Subtype.ext hb)

include huniq in
/-- Every target integer is integral over the base valuation ring.  The proof
uses its monic Galois-orbit polynomial and coefficient descent. -/
theorem target_valuationSubring_element_isIntegral_of_uniqueExtension
    (a : target.valuationSubring) :
    IsIntegral base.valuationSubring a := by
  let p := integralOrbitPolynomial
      huniq a
  have hplifts :
      p ∈ Polynomial.lifts
        (algebraMap base.valuationSubring target.valuationSubring) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact integralOrbitPolynomial_coeff_mem_range
        huniq a n
  rcases Polynomial.lifts_and_natDegree_eq_and_monic hplifts (integralOrbitPolynomial_monic
    huniq a) with
    ⟨q, hqmap, _hqdeg, hqmonic⟩
  refine ⟨q, hqmonic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap]
  change
    (integralOrbitPolynomial
        huniq a).eval a = 0
  classical
  change
    (∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
          huniq σ a))).eval a = 0
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Gal(L/K)))
  simp

include huniq in
/-- The target valuation ring is integral over the base valuation ring under
the standing unique-extension hypotheses of ramification-number theory. -/
theorem target_valuationSubring_isIntegral_of_uniqueExtension :
    Algebra.IsIntegral base.valuationSubring target.valuationSubring := ⟨fun a =>
    target_valuationSubring_element_isIntegral_of_uniqueExtension
        huniq a⟩

end

/-- Under the standing hypotheses, the target valuation ring is the actual
integral closure of the base valuation ring in `L`. -/
theorem target_valuationSubring_isIntegralClosure_of_uniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    IsIntegralClosure target.valuationSubring base.valuationSubring L := by
  let :=
    target_valuationSubring_isIntegral_of_uniqueExtension
        huniq
  apply valuationSubring_isIntegralClosure_of_isIntegral

/-- The target valuation ring is finite over the base valuation ring.  This
is the noncomplete replacement for the completeness-based finite-module input
formerly used by the ramification-number theory monogeneity proof. -/
theorem target_valuationSubring_moduleFinite_of_uniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    Module.Finite base.valuationSubring target.valuationSubring := by
  let :=
    base.valuationSubring_isNoetherianRing
  let :=
    target_valuationSubring_isIntegralClosure_of_uniqueExtension
        huniq
  exact moduleFinite_valuationSubring_of_isIntegralClosure
     base.valuation target.valuation

end Higher
end RamificationTheory.HilbertRamification

end
