/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Order.UpperLower.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A lower set of exponent vectors is a finite disjoint union of translated
coordinate orthants. Dickson's lemma supplies a threshold above which each
coordinate is either fixed or unrestricted. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {σ : Type*}

/-- Truncate every coordinate of the exponent vector `a` at `B`, giving `i ↦ min (a i) B`. -/
def clampExponent  (B : ℕ) (a : σ → ℕ) : σ → ℕ :=
  fun i => min (a i) B

/-- Membership in a lower exponent set is determined by a finite box. -/
theorem lowerSet_clamp_stabilizes  [Fintype σ]
    (S : Set (σ → ℕ)) (hS : IsLowerSet S) :
    ∃ B : ℕ, 0 < B ∧ ∀ a, a ∈ S ↔ clampExponent B a ∈ S := by
  classical
  let T := {a | Minimal (fun a => a ∉ S) a}
  have hT : T.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  let B := hT.toFinset.sup (fun a => Finset.univ.sup a) + 1
  have hbound (a : σ → ℕ) (ha : a ∈ T) (i : σ) : a i ≤ B := by
    have h₁ := Finset.le_sup (f := a) (Finset.mem_univ i)
    have h₂ := Finset.le_sup (f := fun a : σ → ℕ => Finset.univ.sup a)
      (hT.mem_toFinset.mpr ha)
    dsimp [B]
    omega
  refine ⟨B, by dsimp [B]; omega, ?_⟩
  intro a
  constructor
  · solve_by_elim [min_le_left]
  · intro ha
    by_contra hn
    have hp : (Sᶜ).IsPWO := by
      solve_by_elim [wellQuasiOrdered_le]
    obtain ⟨b, hba, hb⟩ := hp.exists_le_minimal hn
    exact hb.left (hS (fun i => le_min (hba i) (hbound b hb i)) ha)

variable {B : ℕ} (b : σ → Fin (B + 1))

/-- A truncated coordinate pattern, with value B marking its free coordinates. -/
abbrev orthantFree   :=
  {i : σ // (b i).val = B}

/-- The total degree `∑ i, b i` of the base point of the orthant with truncated coordinate
pattern `b`. -/
def orthantBaseDegree  [Fintype σ] {B : ℕ}
    (b : σ → Fin (B + 1)) : ℕ := ∑ i, (b i).val

/-- The point of the orthant with truncated pattern `b` obtained by adding `c` to the base
point `b` in the free coordinates (those where `b i = B`). -/
def orthantExpand  
    (c : orthantFree b → ℕ) : σ → ℕ :=
  fun i => (b i).val + if h : (b i).val = B then c ⟨i, h⟩ else 0

/-- Every point of the orthant with truncated pattern `b` truncates back to `b`. -/
lemma clamp_orthantExpand   (c : orthantFree b → ℕ) :
    clampExponent B (orthantExpand b c) = fun i => (b i).val := by
  grind [clampExponent, orthantExpand]

/-- The total degree of a point of the orthant with pattern `b` is the base degree of `b`
plus the total of the added free coordinates. -/
lemma orthantExpand_sum  [Fintype σ] {B : ℕ}
    (b : σ → Fin (B + 1)) (c : orthantFree b → ℕ) :
    (∑ i, orthantExpand b c i) = orthantBaseDegree b + ∑ j, c j := by
  classical
  simp only [orthantExpand, Finset.sum_add_distrib, orthantBaseDegree]
  congr 1
  have hh := Finset.sum_subtype (p := fun i => (b i).val = B) (F := inferInstance)
      (Finset.univ.filter (fun i => (b i).val = B))
      (by simp) (fun i => if h : (b i).val = B then c ⟨i, h⟩ else 0)
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => (b i).val = B),
        if h : (b i).val = B then c ⟨i, h⟩ else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (b i).val = B <;> simp [hi]
    _ = _ := hh
    _ = ∑ j, c j := Finset.sum_congr rfl (fun j _ => by simp [j.property])

/-- Every cell of the truncation map is a coordinate orthant. -/
def orthantExpandEquiv   :
    (orthantFree b → ℕ) ≃
      {a : σ → ℕ // clampExponent B a = fun i => (b i).val} where
  toFun c := ⟨orthantExpand b c, clamp_orthantExpand b c⟩
  invFun a := fun i => a.val i.val - B
  left_inv c := by
    funext i
    simp [orthantExpand, i.property]
  right_inv a := by
    apply Subtype.ext
    funext i
    have hi := congrFun a.property i
    change min (a.val i) B = (b i).val at hi
    simp only [orthantExpand]
    split_ifs with h
    · rw [h]
      omega
    · omega

/-- Truncation gives the unique cell containing any exponent vector. -/
def exponentPattern  (B : ℕ) (a : σ → ℕ) : σ → Fin (B + 1) :=
  fun i => ⟨min (a i) B, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- A bounded slice of an orthant is a bounded exponent simplex in its free
coordinates. -/
def boundedOrthantEquiv  [Fintype σ] {B N : ℕ}
    (b : σ → Fin (B + 1)) (hN : orthantBaseDegree b ≤ N) :
    {c : orthantFree b → ℕ // ∑ i, c i ≤ N - orthantBaseDegree b} ≃
      {a : σ → ℕ // clampExponent B a = (fun i => (b i).val) ∧ ∑ i, a i ≤ N} := by
  let e := orthantExpandEquiv b
  refine Equiv.ofBijective
    (fun c => ⟨orthantExpand b c.val, clamp_orthantExpand b c.val, ?_⟩) ⟨?_, ?_⟩
  · rw [orthantExpand_sum]
    omega
  · intro c d h
    have hv :=
      congrArg ((Subtype.val)) h
    apply Subtype.ext
    apply e.injective
    exact Subtype.ext hv
  · intro a
    let c := e.symm ⟨a.val, a.property.1⟩
    have he : orthantExpand b c = a.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨a.val, a.property.1⟩)
    have hc : ∑ i, c i ≤ N - orthantBaseDegree b := by
      have h := a.property.2
      rw [← he, orthantExpand_sum] at h
      omega
    exact ⟨⟨c, hc⟩, Subtype.ext he⟩

end
end CCDN
