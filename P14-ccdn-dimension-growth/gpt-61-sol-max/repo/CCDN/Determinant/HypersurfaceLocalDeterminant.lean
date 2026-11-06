/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.LocalDeterminant

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.FilteredDeterminant
import CCDN.Determinant.HypersurfaceHilbert

/-! A coefficient-independent local determinant exponent for hypersurfaces.
The exponent is an explicit finite sum depending only on dimension,
multiplicity and the number of rows, and admits sharp binomial cutoff bounds. -/

@[expose] public section
namespace CCDN
open MvPolynomial

/-- Deficit exponent from the cumulative bound μ binomial(n+k,n), where n
is the hypersurface dimension. -/
noncomputable def hypersurfaceMultiplicityExponent (n μ s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - μ * (n + k.val).choose n


private lemma hypersurface_cumulative_capacity_ge (n k : ℕ) {μ : ℕ} (hμ : 0 < μ) :
    k + 1 ≤ μ * (n + 1 + k).choose (n + 1) := by
  have h := Nat.choose_le_choose k (show 1 + k ≤ n + 1 + k by omega)
  rw [Nat.choose_symm_add ]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right] at h
  exact h.trans (Nat.le_mul_of_pos_left _ hμ)

/-- Hockey-stick identity: `∑_{k < K} (n + k).choose n = (n + K).choose (n + 1)`. -/
lemma sum_cumulative_binomial (n K : ℕ) :
    (∑ k ∈ Finset.range K, (n + k).choose n) = (n + K).choose (n + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    grind [Finset.sum_range_succ]


/-- Exact integer cutoff inequality. Optimizing K gives the leading
(n!/μ)^(1/n) * n/(n+1) * s^(1+1/n) term of CCDN's local determinant bound. -/
theorem hypersurfaceMultiplicityExponent_cutoff (n s K : ℕ) {μ : ℕ} (hμ : 0 < μ) :
    s * K ≤ hypersurfaceMultiplicityExponent (n + 1) μ s +
      μ * (n + 1 + K).choose (n + 2) := by
  have hsum := Finset.sum_le_sum (s := Finset.range K)
    (f := fun _ => s)
    (g := fun k => (s - μ * (n + 1 + k).choose (n + 1)) +
      μ * (n + 1 + k).choose (n + 1)) (fun k _ => by omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cumulative_binomial] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have h := (show ∑ k ∈ Finset.range K, (s - μ * (n + (1 : ℕ) + k).choose (n + (1 : ℕ))) ≤
                hypersurfaceMultiplicityExponent (n + (1 : ℕ)) μ s from (by
              unfold hypersurfaceMultiplicityExponent
              rw [Fin.sum_univ_eq_sum_range (fun k => s - μ * (n + 1 + k).choose (n + 1))]
              by_cases hK : K ≤ s
              · gcongr
              · have hsub : Finset.range s ⊆ Finset.range K := Finset.range_mono (by omega)
                have he := Finset.sum_subset hsub (f := fun k => s - μ * (n + 1 + k).choose (n + 1))
                apply le_of_eq (he ?_).symm
                intro k _ hk
                have hs : s ≤ k := by simp_all
                have hc := hypersurface_cumulative_capacity_ge n k hμ
                omega))
  nlinarith

/-- Every evaluation determinant in one hypersurface residue class has the
explicit dimension/multiplicity divisor, even for zeros only modulo that power. -/
theorem hypersurface_pow_dvd_det_mod {p n μ s : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial (n + 2))
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0)
    (x : Fin s → CCDN.IntPoint (n + 2)) (hx : ∀ i j, ↑p ∣ x i j)
    (hfx : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣ eval (x i) f)
    (F : Fin s → CCDN.IntegerPolynomial (n + 2)) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (x i) (F j)).det :=
  origin_filtration_pow_dvd_det_mod f x hx
    ((by
       let inline_f := (map (Int.castRingHom (ZMod p))) f
       apply Finset.sum_le_sum
       intro k _
       have h := originLayer_cumulative_le inline_f hf hμ k.val
       rw [show n + k.val + 1 = n + 1 + k.val by omega] at h
       exact Nat.sub_le_sub_left h s)) hfx F

open Finset in
theorem hypersurfaceMultiplicityExponent_one (μ s : ℕ) (hμ : 0 < μ) :
    hypersurfaceMultiplicityExponent 1 μ s = multiplicityExponent s μ := by
  classical
  have row (i : ℕ) (hi : i < s) :
      (∑ k ∈ range s, if μ * (k + 1) ≤ i then 1 else 0 : ℕ) = i / μ := by
    rw [sum_boole]
    have he : (range s).filter (fun k => μ * (k + 1) ≤ i) = range (i / μ) := by
      ext k
      simp only [mem_filter, mem_range]
      have hd := Nat.div_le_self i μ
      rw [Nat.mul_comm μ, ← Nat.le_div_iff_mul_le hμ]
      omega
    simp [he]
  have col (k : ℕ) :
      (∑ i ∈ range s, if μ * (k + 1) ≤ i then 1 else 0 : ℕ) = s - μ * (k + 1) := by
    rw [sum_boole]
    have he : (range s).filter (fun i => μ * (k + 1) ≤ i) = Ico (μ * (k + 1)) s := by
      ext i
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    simp [he]
  unfold hypersurfaceMultiplicityExponent multiplicityExponent
  simp only [Nat.choose_one_right]
  rw [Fin.sum_univ_eq_sum_range (fun k => s - μ * (1 + k)),
    Fin.sum_univ_eq_sum_range (fun i => i / μ)]
  calc
    _ = ∑ k ∈ range s, ∑ i ∈ range s, if μ * (k + 1) ≤ i then 1 else 0 := by
      apply sum_congr rfl
      intro k hk
      simpa only [Nat.add_comm] using (col k).symm
    _ = ∑ i ∈ range s, ∑ k ∈ range s, if μ * (k + 1) ≤ i then 1 else 0 := sum_comm
    _ = _ := sum_congr rfl fun i hi => row i (mem_range.mp hi)

end CCDN
