module

public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Unramifiedness in a compositum

This file contains reusable criteria for proving that a prime in a number
field compositum is unramified from the inertia groups of its two factors.
-/

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField

attribute [local instance] Ideal.Quotient.field



/-- If a finite family of normal simple intermediate fields generates a
finite Galois number-field extension and the inertia at a prime restricts
trivially to every member of the family, then the inertia of the full
extension is trivial.  This is the finite-radical form of the compositum
argument used for the full `S`-unit Kummer extension. -/
theorem inertiaGroup_eq_bot_of_finset_adjoin_eq_top
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (T : Finset M)
    (Q : Ideal (𝓞 M))
    (hnormal :
      ∀ x : M, x ∈ T →
        Normal K (IntermediateField.adjoin K {x}))
    (hI :
      ∀ (x : M) (_ : x ∈ T),
        inertiaGroup
            (Q.under
              (𝓞 (IntermediateField.adjoin K {x})))
            Gal((IntermediateField.adjoin K {x})/K) =
          ⊥)
    (hadjoin :
      IntermediateField.adjoin K (T : Set M) = ⊤) :
    inertiaGroup Q Gal(M/K) = ⊥ := by
  apply le_antisymm
  · intro sigma hsigma
    have hfix :
        ∀ x : M, x ∈ T → sigma x = x := by
      intro x hx
      let B : IntermediateField K M :=
        IntermediateField.adjoin K {x}
      let : Normal K B := hnormal x hx
      let rB : Gal(M/K) →* Gal(B/K) :=
        AlgEquiv.restrictNormalHom B
      have hsigmaB :
          rB sigma ∈
            inertiaGroup (Q.under (𝓞 B)) Gal(B/K) := by
        rw [mem_inertiaGroup_iff]
        intro y
        change
          algebraMap (𝓞 B) (𝓞 M)
              (rB sigma • y - y) ∈ Q
        rw [map_sub]
        have hcompat :
            algebraMap (𝓞 B) (𝓞 M) (rB sigma • y) =
              sigma • algebraMap (𝓞 B) (𝓞 M) y := by
          apply RingOfIntegers.coe_injective
          change
            algebraMap B M
                (sigma.restrictNormal B y.1) =
              sigma (algebraMap B M y.1)
          exact
            AlgEquiv.restrictNormal_commutes sigma B y.1
        rw [hcompat]
        exact
          (mem_inertiaGroup_iff.mp hsigma)
            (algebraMap (𝓞 B) (𝓞 M) y)
      have hsigmaBone : rB sigma = 1 := by
        rw [← Subgroup.mem_bot, ← hI x hx]
        exact hsigmaB
      have hxB : x ∈ B :=
        IntermediateField.subset_adjoin K {x}
          (Set.mem_singleton x)
      calc
        sigma x =
            algebraMap B M
              ((rB sigma) ⟨x, hxB⟩) := by
          change
            sigma x =
              algebraMap B M
                (sigma.restrictNormal B ⟨x, hxB⟩)
          exact
            (AlgEquiv.restrictNormal_commutes
              sigma B ⟨x, hxB⟩).symm
        _ =
            algebraMap B M
              ((1 : Gal(B/K)) ⟨x, hxB⟩) :=
          congrArg
            (fun tau : Gal(B/K) =>
              algebraMap B M (tau ⟨x, hxB⟩))
            hsigmaBone
        _ = x := rfl
    have hmem :
        sigma ∈
          (IntermediateField.adjoin K
            (T : Set M)).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
          exact hfix x hx
      | algebraMap a =>
          exact sigma.commutes a
      | add x y hx hy ihx ihy =>
          rw [map_add, ihx, ihy]
      | inv x hx ihx =>
          rw [map_inv₀, ihx]
      | mul x y hx hy ihx ihy =>
          rw [map_mul, ihx, ihy]
    simpa [hadjoin] using hmem
  · exact bot_le

/-- For a finite Galois extension of number fields, ramification index
one at a prime forces the corresponding inertia group to be trivial.
The residue extension is separable because the residue field of a number
field is finite. -/
theorem inertiaGroup_eq_bot_of_ramificationIdx_eq_one
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 M))
    [p.IsPrime] [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    (hp0 : p ≠ ⊥)
    (he : P.ramificationIdx (𝓞 K) = 1) :
    inertiaGroup P Gal(M/K) = ⊥ := by
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite ((𝓞 K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField ((𝓞 K) ⧸ p) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      ((𝓞 K) ⧸ p) ((𝓞 M) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← Subgroup.card_eq_one,
    inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 M) p P Gal(M/K) hp0]
  exact he

/-- Algebraic unramifiedness at a prime of a finite Galois number-field
extension forces the corresponding inertia group to be trivial. -/
theorem inertiaGroup_eq_bot_of_isUnramifiedAt
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.IsMaximal]
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) P) :
    inertiaGroup P Gal(M/K) = ⊥ := by
  let p : Ideal (𝓞 K) := P.under (𝓞 K)
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField M)
  have hp0 : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) hP0
  let : Algebra.IsUnramifiedAt (𝓞 K) P := hunram
  apply inertiaGroup_eq_bot_of_ramificationIdx_eq_one
    (K := K) (M := M) p P hp0
  exact Ideal.ramificationIdx_eq_one P (𝓞 K)

/-- Trivial inertia at a prime of a finite Galois number-field
extension gives algebraic unramifiedness at that prime. -/
theorem isUnramifiedAt_of_inertiaGroup_eq_bot
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.IsMaximal]
    (hI : inertiaGroup P Gal(M/K) = ⊥) :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  let p : Ideal (𝓞 K) := P.under (𝓞 K)
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField M)
  have hp0 : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) hP0
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite ((𝓞 K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField ((𝓞 K) ⧸ p) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      ((𝓞 K) ⧸ p) ((𝓞 M) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have he :
      P.ramificationIdx (𝓞 K) = 1 := by
    rw [← inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 M)
      p P Gal(M/K) hp0, hI]
    simp
  exact Ideal.ramificationIdx_eq_one_iff.mp he





end HilbertRamification.Dedekind

end
