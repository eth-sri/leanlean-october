/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.FilteredDeterminant
import CCDN.Determinant.HypersurfaceHilbert

/-! A coefficient-independent local determinant exponent for hypersurfaces.
The exponent is an explicit finite sum depending only on dimension,
multiplicity and the number of rows, and admits sharp binomial cutoff bounds. -/

namespace CCDN
section
open MvPolynomial

/-- Deficit exponent from the cumulative bound μ binomial(n+k,n), where n
is the hypersurface dimension. -/
def hypersurfaceMultiplicityExponent (n μ s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - μ * (n + k.val).choose n

lemma hypersurfaceMultiplicityExponent_le_origin {K : Type*} [Field K] {n μ s : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K)
    (hf : f ∈ idealOfVars (Fin (n + 2)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    hypersurfaceMultiplicityExponent (n + 1) μ s ≤
      filtrationExponent (fun k => Module.finrank K (originLayer f k)) s := by
  apply Finset.sum_le_sum
  intro k _
  have h : (∑ j : Fin (k.val + 1), Module.finrank K (originLayer f j.val)) ≤
      μ * (n + k.val + 1).choose (n + 1) := by
    exact (Finset.sum_le_sum (fun j _ =>
      originLayer_finrank_le_hypersurfaceLayerBound f hf hμ)).trans
        (show (∑ j : Fin (k.val + 1), hypersurfaceLayerBound (n + 1) μ j.val) ≤
              μ * (n + k.val + 1).choose (n + 1) by
            calc
              _ ≤ ∑ j : Fin (k.val + 1), μ * (n + j.val).choose n :=
                Finset.sum_le_sum fun j _ => hypersurfaceLayerBound_le_mul_choose n μ j.val
              _ = μ * (n + k.val + 1).choose (n + 1) := by
                rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (n + j).choose n)]
                simp_rw [Nat.add_comm n]
                rw [Nat.sum_range_add_choose]
                grind)
  rw [show n + k.val + 1 = n + 1 + k.val by omega] at h
  exact Nat.sub_le_sub_left h s

/-- Hockey-stick identity: `∑_{k < K} (n + k).choose n = (n + K).choose (n + 1)`. -/
lemma sum_cumulative_binomial (n K : ℕ) :
    (∑ k ∈ Finset.range K, (n + k).choose n) = (n + K).choose (n + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show n + (K + 1) = (n + K) + 1 by omega, Nat.choose_succ_succ']
    omega

section
variable (n s K : ℕ) {μ : ℕ} (hμ : 0 < μ)
include hμ

/-- Cutoffs beyond s add no positive deficits. Hence the finite
exponent controls every numerical cutoff. -/
lemma sum_hypersurface_deficits_le :
    (∑ k ∈ Finset.range K, (s - μ * (n + 1 + k).choose (n + 1))) ≤
      hypersurfaceMultiplicityExponent (n + 1) μ s := by
  unfold hypersurfaceMultiplicityExponent
  rw [Fin.sum_univ_eq_sum_range (fun k => s - μ * (n + 1 + k).choose (n + 1))]
  by_cases hK : K ≤ s
  · exact Finset.sum_le_sum_of_subset (Finset.range_mono hK)
  · have hsub : Finset.range s ⊆ Finset.range K := Finset.range_mono (by omega)
    have he := Finset.sum_subset hsub (f := fun k => s - μ * (n + 1 + k).choose (n + 1))
    apply le_of_eq (he ?_).symm
    intro k _ hk
    have hs : s ≤ k := by grind
    have hc : k + 1 ≤ μ * (n + 1 + k).choose (n + 1) := by
      have h := Nat.choose_le_choose k (show 1 + k ≤ n + 1 + k by omega)
      rw [Nat.choose_symm_add]
      rw [Nat.add_comm 1 k, Nat.choose_succ_self_right] at h
      exact h.trans (Nat.le_mul_of_pos_left _ hμ)
    omega

/-- Exact integer cutoff inequality. Optimizing K gives the leading
(n!/μ)^(1/n) * n/(n+1) * s^(1+1/n) term of CCDN's local determinant bound. -/
theorem hypersurfaceMultiplicityExponent_cutoff :
    s * K ≤ hypersurfaceMultiplicityExponent (n + 1) μ s +
      μ * (n + 1 + K).choose (n + 2) := by
  have hsum := Finset.sum_le_sum (s := Finset.range K)
    (f := fun _ => s)
    (g := fun k => (s - μ * (n + 1 + k).choose (n + 1)) +
      μ * (n + 1 + k).choose (n + 1)) (fun k _ => by omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cumulative_binomial] at hsum
  simp at hsum
  have h := sum_hypersurface_deficits_le n s K hμ
  nlinarith

end

