module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import ValuedFieldTheory.Valuation.Topology.Models
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Coefficients for a complete DVR expansion

This file formalizes the recursive coefficient construction in the recursive coefficient proof.  Given a section of the residue map and a uniformizer `π`, every element
of the valuation ring has uniquely determined successive representative
coefficients and remainders satisfying

`u = a 0 + a 1 * π + ... + a (n - 1) * π ^ (n - 1) + π ^ n * b n`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField

/-- A normalized system of representatives for the residue field of a local
ring.  This common structure is used both for the original valuation ring and
for the valuation ring in its completion. -/
structure residueRepresentativeSystemOf
    (O : Type u) [CommRing O] [IsLocalRing O] where
  /-- The chosen representative of each residue class. -/
  repr : IsLocalRing.ResidueField O → O
  /-- Reducing a chosen representative recovers its residue class. -/
  residue_repr : ∀ a : IsLocalRing.ResidueField O,
    IsLocalRing.residue O (repr a) = a
  /-- The zero residue class is represented by zero. -/
  repr_zero : repr 0 = 0

namespace residueRepresentativeSystemOf

variable (O : Type u) [CommRing O] [IsLocalRing O]



end residueRepresentativeSystemOf

/-- A system of representatives for the residue field of a complete DVF
valuation ring, encoded as a section of the residue map and normalized at
zero. -/
abbrev residueRepresentativeSystem
    {K : Type u} [Field K]
    (F : CompleteDVF.{u, v} K) :=
  residueRepresentativeSystemOf F.valuationSubring

namespace residueRepresentativeSystem

variable {K : Type u} [Field K]
variable (F : CompleteDVF.{u, v} K)



end residueRepresentativeSystem

variable {K : Type u} [Field K]
variable (F : CompleteDVF.{u, v} K)

/-- One step of the digit expansion: subtract the chosen residue
representative, then divide by the uniformizer. -/
theorem exists_remainder_step
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (r : F.valuationSubring) :
    ∃ b : F.valuationSubring,
      r = R.repr (F.residueMap r) + π * b := by
  have hres :
      F.residueMap (r - R.repr (F.residueMap r)) = 0 := by
    simp [map_sub, R.residue_repr]
  have hmem :
      r - R.repr (F.residueMap r) ∈ F.maximalIdeal :=
    (F.residue_eq_zero_iff _).1 hres
  have hspan :
      r - R.repr (F.residueMap r) ∈
        Ideal.span ({π} : Set F.valuationSubring) := by
    simpa [F.maximalIdeal_eq_span_uniformizer hπ] using hmem
  rcases (Ideal.mem_span_singleton.mp hspan) with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rw [sub_eq_iff_eq_add] at hb
  simpa [add_comm] using hb

/-- The recursively defined remainders in the expansion of `u`. -/
noncomputable def remainder
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) :
    ℕ → F.valuationSubring
  | 0 => u
  | n + 1 =>
      Classical.choose
        (exists_remainder_step F R π hπ
          (remainder R π hπ u n))

/-- The recursively defined representative coefficients in the expansion of
`u`. -/
noncomputable def coeff
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    F.valuationSubring :=
  R.repr (F.residueMap (remainder F R π hπ u n))

/-- The defining recursion for the remainders and coefficients. -/
theorem remainder_step
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    remainder F R π hπ u n =
      coeff F R π hπ u n +
        π * remainder F R π hπ u (n + 1) := by
  exact
    Classical.choose_spec
      (exists_remainder_step F R π hπ
        (remainder F R π hπ u n))





/-- Laurent-unit decomposition in a complete DVF: every nonzero field element
is a power of the chosen uniformizer times a valuation-ring unit. -/
theorem exists_laurent_unit
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, ∃ u : F.valuationSubring,
      IsUnit u ∧ x = (π : K) ^ m * (u : K) := by
  classical
  rcases F.valuation.valuationSubring.mem_or_inv_mem x with hxmem | hxinvmem
  · let r : F.valuationSubring := ⟨x, hxmem⟩
    have hr : r ≠ 0 := by
      intro hr0
      exact hx (by simpa [r] using congrArg (fun y : F.valuationSubring => (y : K)) hr0)
    rcases Valuation.exists_pow_Uniformizer (v := F.valuation) hr
        (Valuation.Uniformizer.mk π hπ) with ⟨n, u, hu⟩
    let u0 : F.valuationSubring := u.val
    have hu0 : IsUnit u0 := by
      simp [u0]
    have hcoe_pow :
        ((π ^ n : F.valuationSubring) : K) = (π : K) ^ n := by
      exact map_pow F.valuation.integer.subtype π n
    refine ⟨(n : ℤ), u0, hu0, ?_⟩
    calc
      x = ((π ^ n : F.valuationSubring) : K) * (u0 : K) := by
        change x = ((π ^ n : F.valuationSubring) : K) * (u0 : K) at hu
        exact hu
      _ = (π : K) ^ (n : ℤ) * (u0 : K) := by
        rw [hcoe_pow, zpow_natCast]
  · let r : F.valuationSubring := ⟨x⁻¹, hxinvmem⟩
    have hr : r ≠ 0 := by
      intro hr0
      have hxinv0 : x⁻¹ = 0 := by
        simpa [r] using congrArg (fun y : F.valuationSubring => (y : K)) hr0
      exact inv_ne_zero hx hxinv0
    rcases Valuation.exists_pow_Uniformizer (v := F.valuation) hr
        (Valuation.Uniformizer.mk π hπ) with ⟨n, u, hu⟩
    let u0 : F.valuationSubring := (u⁻¹).val
    have hu0 : IsUnit u0 := by
      simp [u0]
    have hcoe_pow :
        ((π ^ n : F.valuationSubring) : K) = (π : K) ^ n := by
      exact map_pow F.valuation.integer.subtype π n
    have huK : x⁻¹ = (π : K) ^ n * ((u.val : F.valuationSubring) : K) := by
      calc
        x⁻¹ = ((π ^ n : F.valuationSubring) : K) *
            ((u.val : F.valuationSubring) : K) := by
          change x⁻¹ = ((π ^ n : F.valuationSubring) : K) *
            ((u.val : F.valuationSubring) : K) at hu
          exact hu
        _ = (π : K) ^ n * ((u.val : F.valuationSubring) : K) := by
          rw [hcoe_pow]
    have huinv : (((u.val : F.valuationSubring) : K))⁻¹ = (u0 : K) := by
      have hmulO :
          (u.val : F.valuationSubring) * ((u⁻¹).val : F.valuationSubring) = 1 :=
        Units.mul_inv u
      have hmulK : ((u.val : F.valuationSubring) : K) * (u0 : K) = 1 := by
        change
          (((u.val : F.valuationSubring) * ((u⁻¹).val : F.valuationSubring) :
              F.valuationSubring) : K) = (1 : K)
        rw [hmulO]
        rfl
      exact inv_eq_of_mul_eq_one_right hmulK
    refine ⟨-((n : ℤ)), u0, hu0, ?_⟩
    calc
      x = (x⁻¹)⁻¹ := by rw [inv_inv]
      _ = ((π : K) ^ n * ((u.val : F.valuationSubring) : K))⁻¹ := by rw [huK]
      _ = (((u.val : F.valuationSubring) : K))⁻¹ * ((π : K) ^ n)⁻¹ := by
        rw [mul_inv_rev]
      _ = ((π : K) ^ n)⁻¹ * (((u.val : F.valuationSubring) : K))⁻¹ := by
        rw [mul_comm]
      _ = (π : K) ^ (-((n : ℤ))) * (u0 : K) := by
        rw [huinv]
        rw [zpow_neg, zpow_natCast]





/-- Finite partial sums of the `π`-adic representative expansion. -/
noncomputable def partialSum
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) :
    ℕ → F.valuationSubring
  | 0 => 0
  | n + 1 =>
      partialSum R π hπ u n +
        coeff F R π hπ u n * π ^ n

/-- Finite-stage expansion with a remainder term. -/
theorem partialSum_add_remainder
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    u =
      partialSum F R π hπ u n +
        π ^ n * remainder F R π hπ u n := by
  induction n with
  | zero =>
      simp [partialSum, remainder]
  | succ n ih =>
      calc
        u =
            partialSum F R π hπ u n +
              π ^ n * remainder F R π hπ u n := ih
        _ =
            partialSum F R π hπ u n +
              π ^ n *
                (coeff F R π hπ u n +
                  π * remainder F R π hπ u (n + 1)) := by
          rw [remainder_step F R π hπ u n]
        _ =
            partialSum F R π hπ u (n + 1) +
              π ^ (n + 1) * remainder F R π hπ u (n + 1) := by
          change
            partialSum F R π hπ u n +
                π ^ n *
                  (coeff F R π hπ u n +
                    π * remainder F R π hπ u (n + 1)) =
              (partialSum F R π hπ u n +
                  coeff F R π hπ u n * π ^ n) +
                π ^ (n + 1) * remainder F R π hπ u (n + 1)
          rw [pow_succ]
          ring

/-- The finite expansion gives the correct residue modulo `π ^ n`. -/
theorem partialSum_congr
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    u - partialSum F R π hπ u n ∈ F.maximalIdeal ^ n := by
  let ps := partialSum F R π hπ u n
  let rem := remainder F R π hπ u n
  have hsum :
      u = ps + π ^ n * rem := by
    simpa [ps, rem] using
      partialSum_add_remainder F R π hπ u n
  have hdiff :
      u - ps = π ^ n * rem := by
    nth_rewrite 1 [hsum]
    ring
  have hpow :
      π ^ n * rem ∈
        Ideal.span ({π ^ n} : Set F.valuationSubring) := by
    rw [Ideal.mem_span_singleton]
    exact ⟨rem, by rw [mul_comm]⟩
  have hspan_eq := F.maximalIdeal_pow_eq_span_uniformizer_pow hπ n
  simpa [ps, rem, hdiff, hspan_eq] using hpow

/-- Convergence of the finite partial sums in the maximal-ideal adic
topology, represented on a type-level topological copy of the valuation
ring. -/
def PartialSumsConvergeAdically
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) : Prop :=
  Filter.Tendsto
    (fun n =>
      WithTopology.toTopology F.maximalIdeal.adicTopology
        (partialSum F R π hπ u n))
    Filter.atTop
    (nhds
      (WithTopology.toTopology F.maximalIdeal.adicTopology u))

/-- The finite partial sums converge to `u` in the type-level model of the
maximal-ideal adic topology. -/
theorem partialSum_tendsto_adic
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) :
    PartialSumsConvergeAdically F R π hπ u := by
  classical
  unfold PartialSumsConvergeAdically
  apply WithTopology.tendsto_nhds_iff.mpr
  let : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
  rw [Filter.tendsto_def]
  intro s hs
  rw [Filter.mem_atTop_sets]
  rcases (Ideal.hasBasis_nhds_adic F.maximalIdeal u).mem_iff.mp hs with
    ⟨m, _hm, hms⟩
  refine ⟨m, ?_⟩
  intro n hn
  apply hms
  let ps := partialSum F R π hπ u n
  refine ⟨ps - u, ?_, ?_⟩
  · have hcongr : u - ps ∈ F.maximalIdeal ^ n := by
      simpa [ps] using partialSum_congr F R π hπ u n
    have hneg : ps - u ∈ F.maximalIdeal ^ n := by
      simpa [ps, sub_eq_add_neg] using
        (F.maximalIdeal ^ n).neg_mem hcongr
    exact Ideal.pow_le_pow_right hn hneg
  · simp [ps, sub_eq_add_neg]











end Valuations
end LubinTate

end
