module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

namespace ValuationTheory

/-!
# The unique-extension characterization: automorphism invariance from unique extension

The pullback of an extension valuation ring by a ground-field automorphism is
again an extension valuation ring.  Hence uniqueness forces the chosen ring
to be fixed by every automorphism of the extension field.  This is the first
Galois-theoretic step in the converse direction of the unique-extension characterization.
-/

noncomputable section

open scoped Pointwise

namespace Valuations

section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (V : ValuationSubring K)
    (W : ValuationSubring L) (hW : V.valuation.HasExtension W.valuation)

include hW in
/-- Translating an extension valuation ring by a `K`-automorphism preserves
the extension property. -/
theorem algEquiv_smul_valuationSubring_hasExtension
    (σ : L ≃ₐ[K] L) :
    V.valuation.HasExtension (σ • W).valuation := by
  let := hW
  have hpullback : ∀ x : K,
      algebraMap K L x ∈ (σ • W).toSubring ↔ x ∈ V.toSubring := by
    intro x
    calc
      _ ∈ (σ • W).toSubring ↔
          algebraMap K L x ∈ (σ • W : ValuationSubring L) :=
        (σ • W).mem_toSubring (algebraMap K L x)
      _ ↔ σ⁻¹ • algebraMap K L x ∈ W :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      _ ↔ algebraMap K L x ∈ W := by
        simp
      _ ↔ x ∈ V := by
        simpa using
          (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
            V.valuation W x)
      _ ↔ x ∈ V.toSubring := (V.mem_toSubring x).symm
  apply
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
  intro x
  simpa using hpullback x

include hW in
/-- If the extension valuation ring is unique, every ground-field
automorphism stabilizes it. -/
theorem algEquiv_smul_valuationSubring_eq_of_unique_extension
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) :
    σ • W = W :=
  huniq (σ • W)
    (algEquiv_smul_valuationSubring_hasExtension V W hW σ)

end

/-- The preceding equality in elementwise form. -/
theorem algEquiv_mem_valuationSubring_iff_of_unique_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) (x : L) :
    σ x ∈ W.toSubring ↔ x ∈ W.toSubring := by
  have hstable :=
    algEquiv_smul_valuationSubring_eq_of_unique_extension V W hW huniq σ
  constructor
  · intro hx
    have : σ x ∈ σ • W := by simpa [hstable] using hx
    exact ValuationSubring.smul_mem_pointwise_smul_iff.mp this
  · intro hx
    simpa [hstable] using ValuationSubring.smul_mem_pointwise_smul σ x W hx

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (V : ValuationSubring K)
    (W : ValuationSubring L) (hW : V.valuation.HasExtension W.valuation)

/-- A ground-field automorphism restricts to an automorphism of the unique
extension valuation ring. -/
def valuationSubringEquivOfUniqueExtension
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) : W ≃+* W where
  toFun x := ⟨σ (x : L),
    (algEquiv_mem_valuationSubring_iff_of_unique_extension
      V W hW huniq σ (x : L)).2 x.2⟩
  invFun x := ⟨σ⁻¹ (x : L),
    (algEquiv_mem_valuationSubring_iff_of_unique_extension
      V W hW huniq σ⁻¹ (x : L)).2 x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

/-- The unique-extension equivalence acts on underlying valuation-ring elements as expected. -/
@[simp]
theorem coe_valuationSubringEquivOfUniqueExtension_apply
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (σ : L ≃ₐ[K] L) (x : W) :
    ((valuationSubringEquivOfUniqueExtension V W hW huniq σ x : W) : L) =
      σ (x : L) :=
  rfl

/-- The canonical homomorphism from the base valuation ring into an extension
valuation ring, without identifying either ring with the valuation subring of
its canonical valuation. -/
def valuationSubringMapOfHasExtension : V →+* W := by
  letI : V.valuation.HasExtension W.valuation := hW
  exact (algebraMap K L).restrict V.toSubring W.toSubring (fun x hx => (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
        V.valuation W x).2 (by
          simpa using hx))

end Valuations
end

end ValuationTheory
