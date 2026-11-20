module

public import Erdos821.P3LowRank.ChainBound

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! Real nonnegative alternating path sums controlled by per-operation weighted row bounds. -/

@[expose] public section

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos821.P3High

variable {β : Type*} [Fintype β]

open Erdos821.P3Lowrank (pathSum applyK tailVec pathSum_eq)

theorem tailR_bound (w : β → ℝ) :
    ∀ (n : ℕ) (G : Fin (n + 1) → β → β → ℝ) (E : Fin n → β → β → ℝ)
      (cG : Fin (n + 1) → ℝ) (cE : Fin n → ℝ),
      (∀ i s t, 0 ≤ G i s t) → (∀ i s t, 0 ≤ E i s t) →
      (∀ i, 0 ≤ cG i) → (∀ i, 0 ≤ cE i) →
      (∀ i s, ∑ t, G i s t * w t ≤ cG i * w s) →
      (∀ i s, ∑ t, E i s t * w t ≤ cE i * w s) →
      ∀ v : β → ℝ, (∀ t, 0 ≤ v t) → (∀ t, v t ≤ w t) →
      ∀ t, 0 ≤ tailVec n G E v t ∧
        tailVec n G E v t ≤ (∏ i : Fin n, cG i.succ) * (∏ i, cE i) * w t := by
  intro n
  induction n with
  | zero =>
      intro G E cG cE _ _ _ _ _ _ v hv0 hvw t
      simpa [tailVec] using And.intro (hv0 t) (hvw t)
  | succ n ih =>
      intro G E cG cE hG hE hcG hcE hGr hEr v hv0 hvw
      have IH := ih (fun i => G i.succ) (fun i => E i.succ) (fun i => cG i.succ)
        (fun i => cE i.succ) (fun i => hG i.succ) (fun i => hE i.succ)
        (fun i => hcG i.succ) (fun i => hcE i.succ) (fun i => hGr i.succ)
        (fun i => hEr i.succ) v hv0 hvw
      set T := tailVec n (fun i => G i.succ) (fun i => E i.succ) v with hT
      set K : ℝ := (∏ i : Fin n, cG i.succ.succ) * (∏ i : Fin n, cE i.succ) with hK
      have hK0 : 0 ≤ K := mul_nonneg (Finset.prod_nonneg fun i _ => hcG _)
        (Finset.prod_nonneg fun i _ => hcE _)
      have hinner : ∀ t', 0 ≤ applyK (G (Fin.succ 0)) T t' ∧
          applyK (G (Fin.succ 0)) T t' ≤ K * cG (Fin.succ 0) * w t' := by
        intro t'
        constructor
        · exact Finset.sum_nonneg fun t'' _ => mul_nonneg (hG _ _ _) (IH t'').1
        · calc applyK (G (Fin.succ 0)) T t' = ∑ t'', G (Fin.succ 0) t' t'' * T t'' := rfl
            _ ≤ ∑ t'', G (Fin.succ 0) t' t'' * (K * w t'') :=
                Finset.sum_le_sum fun t'' _ => mul_le_mul_of_nonneg_left (IH t'').2 (hG _ _ _)
            _ = K * ∑ t'', G (Fin.succ 0) t' t'' * w t'' := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun _ _ => by ring
            _ ≤ K * (cG (Fin.succ 0) * w t') := mul_le_mul_of_nonneg_left (hGr _ t') hK0
            _ = K * cG (Fin.succ 0) * w t' := by ring
      intro t
      have hprod : (∏ i : Fin (n + 1), cG i.succ) * (∏ i, cE i) =
          K * cG (Fin.succ 0) * cE 0 := by
        rw [Fin.prod_univ_succ (f := fun i : Fin (n + 1) => cG i.succ),
          Fin.prod_univ_succ (f := cE)]
        ring
      constructor
      · exact Finset.sum_nonneg fun t' _ => mul_nonneg (hE _ _ _) (hinner t').1
      · change ∑ t', E 0 t t' * applyK (G (Fin.succ 0)) T t' ≤ _
        rw [hprod]
        calc ∑ t', E 0 t t' * applyK (G (Fin.succ 0)) T t'
            ≤ ∑ t', E 0 t t' * (K * cG (Fin.succ 0) * w t') :=
              Finset.sum_le_sum fun t' _ => mul_le_mul_of_nonneg_left (hinner t').2 (hE _ _ _)
          _ = K * cG (Fin.succ 0) * ∑ t', E 0 t t' * w t' := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
          _ ≤ K * cG (Fin.succ 0) * (cE 0 * w t) := mul_le_mul_of_nonneg_left (hEr 0 t) (mul_nonneg hK0 (hcG _))
          _ = K * cG (Fin.succ 0) * cE 0 * w t := by ring

/-- The path sum is at most the product of the row constants times the weighted start mass. -/
theorem pathSumR_le (w : β → ℝ) (n : ℕ)
    (G : Fin (n + 1) → β → β → ℝ) (E : Fin n → β → β → ℝ)
    (cG : Fin (n + 1) → ℝ) (cE : Fin n → ℝ)
    (hG : ∀ i s t, 0 ≤ G i s t) (hE : ∀ i s t, 0 ≤ E i s t)
    (hcG : ∀ i, 0 ≤ cG i) (hcE : ∀ i, 0 ≤ cE i)
    (hGr : ∀ i s, ∑ t, G i s t * w t ≤ cG i * w s)
    (hEr : ∀ i s, ∑ t, E i s t * w t ≤ cE i * w s)
    (u v : β → ℝ) (hu : ∀ s, 0 ≤ u s) (hv0 : ∀ t, 0 ≤ v t) (hvw : ∀ t, v t ≤ w t) :
    pathSum n G E u v ≤ (∏ i, cG i) * (∏ i, cE i) * ∑ s, u s * w s := by
  rw [pathSum_eq]
  have hT := tailR_bound w n G E cG cE hG hE hcG hcE hGr hEr v hv0 hvw
  set K : ℝ := (∏ i : Fin n, cG i.succ) * (∏ i, cE i) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Finset.prod_nonneg fun i _ => hcG _)
    (Finset.prod_nonneg fun i _ => hcE _)
  have hprod : (∏ i, cG i) * (∏ i, cE i) = cG 0 * K := by
    rw [Fin.prod_univ_succ (f := cG)]
    ring
  rw [hprod, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc ∑ t, u s * G 0 s t * tailVec n G E v t
      ≤ ∑ t, u s * G 0 s t * (K * w t) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hT t).2
          (mul_nonneg (hu s) (hG _ _ _))
    _ = u s * K * ∑ t, G 0 s t * w t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ u s * K * (cG 0 * w s) := mul_le_mul_of_nonneg_left (hGr 0 s) (mul_nonneg (hu s) hK0)
    _ = cG 0 * K * (u s * w s) := by ring

end Erdos821.P3High
