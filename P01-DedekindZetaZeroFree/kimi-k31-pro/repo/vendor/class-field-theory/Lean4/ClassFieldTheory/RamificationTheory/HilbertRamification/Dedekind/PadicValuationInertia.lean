module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.AsSubring
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import ValuedFieldTheory.Ramification.HilbertRamification.LocalizationRamificationGroups
public import ValuedFieldTheory.Ramification.HilbertRamification.PadicLocalization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

/-!
# The global valuation/prime-ideal bridge in the global cyclotomic inertia argument

An extension `w` of the rational `p`-adic absolute value determines a
valuation subring of a number field `M`.  This file synchronizes that
valuation subring with a concrete prime ideal of `𝓞 M`, proves that the
prime lies over `(p)`, and identifies the valuation subring with the
localization of `𝓞 M` at that prime.

The final comparison sends ideal-theoretic inertia injectively to the
valuation-subring inertia group.  Thus the local cardinality bound furnished
by the localization and decomposition comparison applies to the chosen global prime without an extra compatibility
hypothesis.
-/

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open AlgebraicNumberTheory.Valuations
open AlgebraicNumberTheory.Ramification
open scoped NumberField

variable (p : ℕ) [Fact p.Prime]
variable (M : Type) [Field M] [NumberField M] [IsAbelianGalois ℚ M]

/-- The localization of a Dedekind domain at a nonzero prime, realized
inside its fraction field as a valuation subring.  This construction belongs
to the ideal/localization bridge; it is kept private here until that bridge
is factored into prime-decomposition theory. -/
def dedekindAtPrimeValuationSubring
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    _root_.ValuationSubring L := by
  let S := Localization.subalgebra L P.primeCompl
    P.primeCompl_le_nonZeroDivisors
  letI : IsLocalization P.primeCompl S := by
    dsimp [S]
    infer_instance
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hP S
  refine _root_.ValuationSubring.ofSubring S.toSubring ?_
  intro x
  obtain ⟨a, ha | ha⟩ :=
    (ValuationRing.isFractionRing_iff.mp
      (inferInstance : IsFractionRing S L)).1 x
  · left
    rw [ha]
    exact a.property
  · right
    rw [ha]
    exact a.property

/-- The valuation-subring realization of a Dedekind localization carries its
canonical algebra structure over the original domain. -/
noncomputable instance dedekindAtPrimeValuationSubringAlgebra
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    Algebra B (dedekindAtPrimeValuationSubring B (L := L) P hP) := by
  change Algebra B
    (Localization.subalgebra L P.primeCompl
      P.primeCompl_le_nonZeroDivisors)
  infer_instance

/-- The valuation-subring realization is the localization away from the
chosen prime. -/
instance dedekindAtPrimeValuationSubringIsLocalization
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    IsLocalization P.primeCompl
      (dedekindAtPrimeValuationSubring B (L := L) P hP) := by
  change IsLocalization P.primeCompl
    (Localization.subalgebra L P.primeCompl
      P.primeCompl_le_nonZeroDivisors)
  infer_instance

/-- A Dedekind localization realized as a valuation subring is again a
Dedekind domain. -/
instance dedekindAtPrimeValuationSubringIsDedekindDomain
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDedekindDomain
      (dedekindAtPrimeValuationSubring B (L := L) P hP) :=
  IsLocalization.AtPrime.isDedekindDomain B P
    (dedekindAtPrimeValuationSubring B (L := L) P hP)

/-- The valuation-subring realization of a nonzero Dedekind localization has
Krull dimension at most one. -/
instance dedekindAtPrimeValuationSubringKrullDimLE
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    Ring.KrullDimLE 1
      (dedekindAtPrimeValuationSubring B (L := L) P hP) :=
  Ring.KrullDimLE.mk₁' (fun _ a _ => IsPrime.to_maximal_ideal a)

/-- The nonarchimedean extension valuation ring attached to a global
extension of the rational `p`-adic absolute value. -/
abbrev globalPadicExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    _root_.ValuationSubring M :=
  HilbertRamification.absoluteValueExtensionValuationSubring
    (Rat.AbsoluteValue.padic p) w
    (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
      (Rat.AbsoluteValue.padic p) w
      (rationalPadicAbsoluteValue_nonarchimedean p))

omit [IsAbelianGalois ℚ M] in
/-- Every algebraic integer belongs to the valuation ring defined by `w`.
This is the integrally-closed valuation-ring argument, rather than an
additional boundedness assumption on algebraic integers. -/
theorem ringOfIntegers_mem_globalPadicExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (x : 𝓞 M) :
    (x : M) ∈ globalPadicExtensionValuationSubring p M w := by
  let A := globalPadicExtensionValuationSubring p M w
  change (x : M) ∈ A
  rw [← A.valuationSubring_valuation]
  exact Valuation.Integers.mem_of_integral
    (Valuation.valuationSubring.integers (v := A.valuation))
    (IsIntegral.tower_top
      (A := A.valuation.valuationSubring) x.property)

/-- The canonical inclusion `𝓞 M → A_w`. -/
def globalPadicRingOfIntegersToExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    𝓞 M →+* globalPadicExtensionValuationSubring p M w :=
  RingHom.codRestrict (algebraMap (𝓞 M) M)
    (globalPadicExtensionValuationSubring p M w).toSubring
    (ringOfIntegers_mem_globalPadicExtensionValuationSubring p M w)

omit [IsAbelianGalois ℚ M] in
/-- The canonical map from `𝓞 M` to the extension valuation ring agrees with
the usual inclusion into `M`. -/
@[simp] theorem globalPadicRingOfIntegersToExtensionValuationSubring_coe
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (x : 𝓞 M) :
    ((globalPadicRingOfIntegersToExtensionValuationSubring p M w x :
        globalPadicExtensionValuationSubring p M w) : M) = (x : M) :=
  rfl

/-- The prime ideal of `𝓞 M` which is the center of `w`. -/
def globalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    Ideal (𝓞 M) :=
  (IsLocalRing.maximalIdeal
      (globalPadicExtensionValuationSubring p M w)).comap
    (globalPadicRingOfIntegersToExtensionValuationSubring p M w)

omit [IsAbelianGalois ℚ M] in
/-- Membership in the synchronized prime is the strict `w`-adic
inequality. -/
theorem mem_globalPadicPrimeIdeal_iff
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (x : 𝓞 M) :
    x ∈ globalPadicPrimeIdeal p M w ↔ w.1 (x : M) < 1 := by
  let A := globalPadicExtensionValuationSubring p M w
  let f := globalPadicRingOfIntegersToExtensionValuationSubring p M w
  change f x ∈ IsLocalRing.maximalIdeal A ↔ w.1 (x : M) < 1
  simpa [A, f] using
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      w.1
      (HilbertRamification.absoluteValueExtension_nonarchimedean_of_base
        (Rat.AbsoluteValue.padic p) w
        (rationalPadicAbsoluteValue_nonarchimedean p))
      (f x))

omit [IsAbelianGalois ℚ M] in
/-- The center of a valuation ring is prime. -/
theorem globalPadicPrimeIdeal_isPrime
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsPrime := by
  unfold globalPadicPrimeIdeal
  exact Ideal.comap_isPrime _ _

omit [IsAbelianGalois ℚ M] in
/-- On rational integers, membership in the center is divisibility by `p`. -/
theorem int_mem_globalPadicPrimeIdeal_under_iff
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)
    (z : ℤ) :
    algebraMap ℤ (𝓞 M) z ∈ globalPadicPrimeIdeal p M w ↔
      (p : ℤ) ∣ z := by
  rw [mem_globalPadicPrimeIdeal_iff]
  have hz :
      ((algebraMap ℤ (𝓞 M) z : 𝓞 M) : M) =
        algebraMap ℚ M (z : ℚ) := by
    simp
  rw [hz, w.2]
  change (((padicNorm p (z : ℚ) : ℚ) : ℝ) < 1) ↔ (p : ℤ) ∣ z
  exact_mod_cast padicNorm.int_lt_one_iff (p := p) z

omit [IsAbelianGalois ℚ M] in
/-- The contraction of the synchronized prime to `ℤ` is the usual
principal ideal `(p)`. -/
theorem globalPadicPrimeIdeal_under_eq_span
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).under ℤ =
      Ideal.span ({(p : ℤ)} : Set ℤ) := by
  ext z
  change algebraMap ℤ (𝓞 M) z ∈ globalPadicPrimeIdeal p M w ↔ _
  rw [int_mem_globalPadicPrimeIdeal_under_iff, Ideal.mem_span_singleton]

omit [IsAbelianGalois ℚ M] in
/-- The synchronized prime lies over the rational height-one prime `p`. -/
theorem globalPadicPrimeIdeal_liesOver
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).LiesOver
      (rationalPrimeIdeal (⟨p, Fact.out⟩ : Nat.Primes)) := by
  constructor
  exact
    (rationalPrimeIdeal_eq_span (⟨p, Fact.out⟩ : Nat.Primes)).trans
      (globalPadicPrimeIdeal_under_eq_span p M w).symm

omit [IsAbelianGalois ℚ M] in
/-- The synchronized prime is nonzero. -/
theorem globalPadicPrimeIdeal_ne_bot
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    globalPadicPrimeIdeal p M w ≠ ⊥ := by
  let : (globalPadicPrimeIdeal p M w).LiesOver
      (rationalPrimeIdeal (⟨p, Fact.out⟩ : Nat.Primes)) :=
    globalPadicPrimeIdeal_liesOver p M w
  apply Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := rationalPrimeIdeal (⟨p, Fact.out⟩ : Nat.Primes))
  exact (Rat.HeightOneSpectrum.primesEquiv.symm
    (⟨p, Fact.out⟩ : Nat.Primes)).ne_bot

omit [IsAbelianGalois ℚ M] in
/-- In the Dedekind ring `𝓞 M`, the synchronized nonzero prime is maximal. -/
theorem globalPadicPrimeIdeal_isMaximal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsMaximal :=
  (globalPadicPrimeIdeal_isPrime p M w).isMaximal
    (globalPadicPrimeIdeal_ne_bot p M w)

/-- The center of a global `p`-adic place is a prime ideal. -/
instance instIsPrimeGlobalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsPrime :=
  globalPadicPrimeIdeal_isPrime p M w

/-- The center of a global `p`-adic place is a maximal ideal. -/
instance instIsMaximalGlobalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).IsMaximal :=
  globalPadicPrimeIdeal_isMaximal p M w

/-- The center of a global `p`-adic place lies over the rational prime
ideal generated by `p`. -/
instance instLiesOverGlobalPadicPrimeIdeal
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M) :
    (globalPadicPrimeIdeal p M w).LiesOver
      (rationalPrimeIdeal ⟨p, Fact.out⟩) :=
  globalPadicPrimeIdeal_liesOver p M w







/-! ## Comparison of ideal inertia with valuation inertia -/

















end HilbertRamification.Dedekind

end
