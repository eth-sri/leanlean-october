module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayLocalHigherUnitMembership
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Positive-depth higher units as `1 + 𝔪ᵛⁿ`

At positive depth, every element of `1 + 𝔪ᵛⁿ` is automatically a unit in
the local integer ring. Consequently no integral-unit witness is needed in
the membership criterion below.
-/

open scoped NumberField
open NumberField IsDedekindDomain


namespace ClassFieldTheory

universe u

/-- For `n ≥ 1`, a local field unit belongs to the `n`-th higher-unit
group exactly when its value is `1 + t` for some `t` in the `n`-th power of
the maximal ideal of the local integer ring. -/
theorem mem_rayLocalHigherUnitGroup_iff_exists_one_add
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 1 ≤ n)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ t : v.adicCompletionIntegers K,
        t ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n ∧
          (x : v.adicCompletion K) =
            ((1 + t : v.adicCompletionIntegers K) : v.adicCompletion K) := by
  constructor
  · intro hx
    obtain ⟨y, hxy, hcong⟩ :=
      (mem_rayLocalHigherUnitGroup_iff v n x).mp hx
    refine ⟨(y : v.adicCompletionIntegers K) - 1, hcong, ?_⟩
    have hval := congrArg Units.val hxy
    change ((y : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (x : v.adicCompletion K) at hval
    simp_all
  · rintro ⟨t, ht, hx⟩
    have htmax : t ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
      (Ideal.pow_le_self (Nat.ne_of_gt hn)) ht
    have hnon : -t ∈ nonunits (v.adicCompletionIntegers K) :=
      by simp_all
    have hunit : IsUnit (1 + t : v.adicCompletionIntegers K) := by
      simpa only [sub_neg_eq_add] using
        (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-t) hnon)
    obtain ⟨y, hy⟩ := hunit
    apply (mem_rayLocalHigherUnitGroup_iff v n x).mpr
    refine ⟨y, ?_, ?_⟩
    · apply Units.ext
      simp_all
    simp_all
