module

public import Mathlib

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

open scoped NumberField

variable (p : ℕ) [Fact p.Prime]
variable (M : Type) [Field M] [NumberField M] [IsAbelianGalois ℚ M]












































































/-- The nonarchimedean extension valuation ring attached to a global
extension of the rational `p`-adic absolute value. -/
abbrev globalPadicExtensionValuationSubring
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)  :=
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
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) M)  :=
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






















































































































































































































































/-! ## Comparison of ideal inertia with valuation inertia -/





















































































































































































































end HilbertRamification.Dedekind

end
