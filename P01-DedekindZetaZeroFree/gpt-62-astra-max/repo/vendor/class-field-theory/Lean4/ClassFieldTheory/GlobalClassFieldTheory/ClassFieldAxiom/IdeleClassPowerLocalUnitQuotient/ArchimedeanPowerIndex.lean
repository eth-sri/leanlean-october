module

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Basic.Sign.Basic
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Archimedean power indices in idele class quotients

This file defines the concrete idele-class subgroup attached to local power
conditions and computes its archimedean local indices.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

section

variable (n : ℕ+) (S T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The subgroup `C_K(S,T) = h(S,T)Kˣ/Kˣ` inside the idele class
group. -/
def ideleClassPowerLocalUnitSubgroup :
    Subgroup (IdeleClassGroup K) :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))

/-- Elementwise form of `C_K(S,T)=h(S,T)Kˣ/Kˣ`. -/
theorem mem_ideleClassPowerLocalUnitSubgroup_iff
    (c : IdeleClassGroup K) :
    c ∈ ideleClassPowerLocalUnitSubgroup (K := K) n S T ↔
      ∃ a : IdeleGroup K,
        a ∈ idelePowerLocalUnitSubgroup (K := K) n S T ∧
          QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a = c := by
  rfl

/-- The quotient whose cardinality is the index
`[C_K : C_K(S,T)]`. -/
abbrev IdeleClassPowerLocalUnitQuotient :=
  IdeleClassGroup K ⧸
    ideleClassPowerLocalUnitSubgroup (K := K) n S T

end

omit [NumberField K] in
/-- If the exponent is even, or the place is complex, every local
`n`-th power is positive in the archimedean sense. -/
theorem nthPowerSubgroup_le_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range ≤
      RayClass.infinitePositiveSubgroup w := by
  intro x hx
  obtain ⟨y, hy⟩ :=
    (MonoidHom.mem_range
      ).mp hx
  rw [powMonoidHom_apply] at hy
  subst x
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  intro hw
  rcases harch with hnEven | hwNotReal
  · rcases hnEven with ⟨m, hm⟩
    let emb :=
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    rw [Units.val_pow_eq_pow_val, map_pow, hm, pow_add, ← pow_two]
    refine sq_pos_of_ne_zero (pow_ne_zero m ?_)
    intro hzero
    apply y.ne_zero
    apply emb.injective
    simp at hzero
  · exact False.elim (hwNotReal hw)

/-- The sign of a unit at a real infinite place. -/
def realInfinitePlaceSignHom
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ →* SignTypeˣ :=
  (Units.map
      (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    (Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv).toMonoidHom

omit [NumberField K] in
/-- The positive subgroup at a real infinite place is exactly the kernel
of the sign homomorphism. -/
theorem realInfinitePlaceSignHom_ker
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    (realInfinitePlaceSignHom w hw).ker =
      RayClass.infinitePositiveSubgroup w := by
  ext x
  change
    realInfinitePlaceSignHom w hw x = 1 ↔
      x ∈ RayClass.infinitePositiveSubgroup w
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  constructor
  · intro hx hw'
    have hproof : hw' = hw := Subsingleton.elim _ _
    subst hproof
    refine sign_eq_one_iff.mp ?_
    simpa [realInfinitePlaceSignHom] using (congrArg Units.val hx)
  · intro hx
    apply Units.ext
    simp_all [realInfinitePlaceSignHom]

omit [NumberField K] in
/-- Both signs occur at a real infinite place. -/
theorem realInfinitePlaceSignHom_surjective
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Function.Surjective (realInfinitePlaceSignHom w hw) := by
  let eu :=
    Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        hw).toMulEquiv
  intro s
  cases hs : (s : SignType) with
  | zero =>
      exact False.elim (s.ne_zero hs)
  | neg =>
      refine ⟨eu.symm (-1), ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]
  | pos =>
      refine ⟨eu.symm 1, ?_⟩
      apply Units.ext
      simp [realInfinitePlaceSignHom, eu, hs]

/-- The quotient by positive units at a real place is its two-element
sign group. -/
noncomputable def realInfinitePositiveQuotientEquivSign
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    w.Completionˣ ⧸ RayClass.infinitePositiveSubgroup w ≃*
      SignTypeˣ := by
  rw [← realInfinitePlaceSignHom_ker w hw]
  exact
    QuotientGroup.quotientKerEquivOfSurjective
      (realInfinitePlaceSignHom w hw)
      (realInfinitePlaceSignHom_surjective w hw)

omit [NumberField K] in
/-- The positive-unit quotient at a real place has order two. -/
theorem card_realInfinitePositiveQuotient
    (w : InfinitePlace K)
    (hw : w.IsReal) :
    Nat.card
        (w.Completionˣ ⧸
          RayClass.infinitePositiveSubgroup w) =
      2 := by
  calc
    _ =
        Nat.card SignTypeˣ :=
      Nat.card_congr
        (realInfinitePositiveQuotientEquivSign w hw).toEquiv
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide

omit [NumberField K] in
/-- In the even-real or complex cases, the local power subgroup is
exactly the usual archimedean positive subgroup. -/
theorem nthPowerSubgroup_eq_infinitePositiveSubgroup
    (n : ℕ+)
    (w : InfinitePlace K)
    (harch : Even (n : ℕ) ∨ ¬ w.IsReal) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      RayClass.infinitePositiveSubgroup w := by
  apply le_antisymm
  · solve_by_elim [nthPowerSubgroup_le_infinitePositiveSubgroup]
  · intro x hx
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hx
    exact
      (MonoidHom.mem_range
        ).mpr ⟨y, by
          exact hy⟩

omit [NumberField K] in
/-- At a real place an odd power map on local units is surjective. -/
theorem nthPowerSubgroup_eq_top_of_real_odd
    (n : ℕ+)
    (w : InfinitePlace K)
    (hw : w.IsReal)
    (hn : Odd (n : ℕ)) :
    (powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range =
      ⊤ := by
  apply top_unique
  intro x hx
  apply
    (MonoidHom.mem_range
      (G := w.Completionˣ)).mpr
  let emb :=
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
  have hx0 : emb (x : w.Completion) ≠ 0 := by
    intro hzero
    apply x.ne_zero
    simp at hzero
  by_cases hxpos : 0 < emb (x : w.Completion)
  · have hxPositive :
        x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      exact hxpos
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos x hxPositive
    exact ⟨y, by
      exact hy⟩
  · have hxneg :=
      lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    have hnegPositive :
        -x ∈ RayClass.infinitePositiveSubgroup w := by
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hw'
      have hproof : hw' = hw := Subsingleton.elim _ _
      subst hproof
      change 0 < emb ((-x : w.Completionˣ) : w.Completion)
      simp [hxneg]
    obtain ⟨y, hy⟩ :=
      _root_.exists_infinitePositiveSubgroup_nthRoot
        w (n : ℕ) n.pos (-x) hnegPositive
    refine ⟨-y, ?_⟩
    rw [powMonoidHom_apply, hn.neg_pow, hy]
    simp

omit [NumberField K] in
/-- The archimedean factor in the local power-index product: it is `2`
exactly for an even exponent at a real place, and `1` otherwise. -/
theorem card_infinitePlace_nthPowerQuotient
    (n : ℕ+)
    (w : InfinitePlace K) :
    Nat.card
        (w.Completionˣ ⧸
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even (n : ℕ) then 2 else 1 := by
  classical
  by_cases hw : w.IsReal
  · by_cases hn : Even (n : ℕ)
    · rw [
        nthPowerSubgroup_eq_infinitePositiveSubgroup
          n w (Or.inl hn)]
      simpa [hw, hn] using
        card_realInfinitePositiveQuotient w hw
    · rw [nthPowerSubgroup_eq_top_of_real_odd n w hw ((Nat.even_or_odd (n : ℕ)).resolve_left hn)]
      simp [hw, hn]
  · have hpositive :
        RayClass.infinitePositiveSubgroup w = ⊤ := by
      ext x
      simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]
    rw [(nthPowerSubgroup_eq_infinitePositiveSubgroup
      n w (Or.inr hw)), hpositive]
    simp [hw]

end GlobalClassFieldTheory.ClassFieldAxiom

end
