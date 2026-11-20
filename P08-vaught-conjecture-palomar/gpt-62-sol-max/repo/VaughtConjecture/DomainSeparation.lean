/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.OrdinalCountability
public import Mathlib.SetTheory.Cardinal.Ordinal

@[expose] public section

namespace VaughtConjecture.DomainSeparation

open Cardinal Set

/-- A set of countable ordinals that is cofinal in `ω₁` has cardinality `ℵ₁`. -/
theorem aleph_one_le_mk_of_cofinal (T : Set Ordinal.{0}) (hT : ∀ ξ ∈ T, ξ < (aleph 1).ord)
    (hcof : ∀ η, η < (aleph 1).ord → ∃ ξ ∈ T, η ≤ ξ) : aleph 1 ≤ #T := by
  let U : Set (Set.Iio (aleph 1).ord) := {ξ | ξ.val ∈ T}
  have hu : IsCofinal U := by
    intro ξ
    obtain ⟨ζ, hζ, hle⟩ := hcof ξ.1 ξ.2
    exact ⟨⟨ζ, hT ζ hζ⟩, hζ, hle⟩
  have h := Order.cof_le hu
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, isRegular_aleph_one.cof_ord] at h
  exact (by simpa using h : aleph 1 ≤ #U).trans
    (Cardinal.mk_le_of_injective (f := fun ξ : U => (⟨ξ.1.1, ξ.2⟩ : T)) (by
      intro a b e
      exact Subtype.ext (Subtype.ext (congrArg (fun ξ : T => ξ.val) e))))

/-- **Exact cardinality with a countable persistent core.**  Decreasing domains, countable
complements at countable indices, a countable persistent core, and cofinally many nonempty
successor losses below `ω₁` give `#X = ℵ₁`.  No point is required to leave. -/
theorem mk_eq_aleph_one_of_countable_core {X : Type 1} (D : Ordinal.{0} → Set X)
    (hanti : Antitone D)
    (hcompl : ∀ β, β < (aleph 1).ord → (D β)ᶜ.Countable)
    (hcore : (⋂ β < (aleph 1).ord, D β).Countable)
    (hloss : ∀ η, η < (aleph 1).ord → ∃ ξ, η ≤ ξ ∧ ξ < (aleph 1).ord ∧
      (D ξ \ D (ξ + 1)).Nonempty) :
    #X = aleph 1 := by
  apply le_antisymm
  · let C := ⋂ β < (aleph 1).ord, D β
    let U := ⋃ β < (aleph 1).ord, (D β)ᶜ
    have hc : #C ≤ aleph 1 := (le_aleph0_iff_set_countable.mpr hcore).trans (aleph0_le_aleph 1)
    have hu : #U ≤ aleph 1 := mk_biUnion_le_of_le_lift (by simp) (aleph0_le_aleph 1)
      (fun β => (D β)ᶜ) fun β hβ =>
        (le_aleph0_iff_set_countable.mpr (hcompl β hβ)).trans (aleph0_le_aleph 1)
    have hcov : C ∪ U = Set.univ := by
      ext x
      simp only [C, U, mem_union, mem_iInter, mem_iUnion, mem_compl_iff, mem_univ]
      grind
    simpa [hcov] using (mk_union_le C U).trans (add_le_add hc hu)
  · -- one point from each nonempty loss; losses are pairwise disjoint by antitonicity
    classical
    let T : Set Ordinal.{0} := {ξ | ξ < (aleph 1).ord ∧ (D ξ \ D (ξ + 1)).Nonempty}
    have hT : ∀ ξ ∈ T, ξ < (aleph 1).ord := fun _ h => h.1
    have hcof : ∀ η, η < (aleph 1).ord → ∃ ξ ∈ T, η ≤ ξ := by grind
    let pick : T → X := fun ξ => ξ.2.2.some
    have hpick : ∀ ξ : T, pick ξ ∈ D ξ.1 \ D (ξ.1 + 1) := fun ξ => ξ.2.2.some_mem
    have hinj : Function.Injective pick := by
      intro ξ ζ hξζ
      by_contra hne
      rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hne) with hlt | hlt
      · have h1 : ξ.1 + 1 ≤ ζ.1 := Order.add_one_le_iff.mpr hlt
        exact (hpick ξ).2 (hξζ ▸ hanti h1 (hpick ζ).1)
      · have h1 : ζ.1 + 1 ≤ ξ.1 := Order.add_one_le_iff.mpr hlt
        exact (hpick ζ).2 (hξζ.symm ▸ hanti h1 (hpick ξ).1)
    exact (aleph_one_le_mk_of_cofinal T hT hcof).trans (Cardinal.mk_le_of_injective hinj)

end VaughtConjecture.DomainSeparation
