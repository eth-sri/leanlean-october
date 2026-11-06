/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.Algebra.BinomialSectionBound
import CCDN.Algebra.GridPointInterpolation
import Mathlib.Data.Nat.Choose.Bounds

/-! A coordinate-grid bound for a proper complete intersection. The
constant depends only on the ambient dimension; the degree dependence
is quadratic. -/

namespace CCDN
section
open MvPolynomial

/-- If `f` is prime, `g` is not divisible by `f`, and both have total degree at most `d`, then the
number of distinct common zeros of `f` and `g` in the grid `Sⁿ⁺²` is at most `(n + 2) ^ n · d² · |S|
^ n`. -/
theorem proper_intersection_grid_card_le {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {n d : ℕ}
    (f g : MvPolynomial (Fin (n + 2)) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hfd : f.totalDegree ≤ d) (hgd : g.totalDegree ≤ d)
    (S : Finset K) (z : ι → Fin (n + 2) → K) (hz : Function.Injective z)
    (hzS : ∀ i j, z i j ∈ S) (hzf : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (z i) g = 0) :
    Fintype.card ι ≤ (n + 2) ^ n * d ^ 2 * S.card ^ n := by
  let L := S.card
  have hbox : Fintype.card ι ≤ L ^ (n + 2) := by
    let ψ : ι → (Fintype.piFinset (fun _ => S)) :=
      fun i => ⟨z i, Fintype.mem_piFinset.mpr (hzS i)⟩
    have hinj : Function.Injective ψ := by
      intro i j h
      grind
    simpa using Fintype.card_le_of_injective ψ hinj
  by_cases hL : L = 0
  · grind
  have hL1 : 1 ≤ L := by omega
  let N := (n + 2) * (L - 1)
  by_cases hN : f.totalDegree + g.totalDegree ≤ N
  · let I : Ideal (MvPolynomial (Fin (n + 2)) K) := Ideal.span {f, g}
    have hzI (i : ι) (q : MvPolynomial (Fin (n + 2)) K) (hq : q ∈ I) :
        eval (z i) q = 0 := by
      have hker : I ≤ RingHom.ker (eval (z i)) := by
        apply Ideal.span_le.mpr
        intro p hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp
        · simp_all
        simp_all
      exact hker hq
    have hlower :=
      grid_points_filtered_lower I S z hz hzS hzI (by aesop)
    have hupper := filteredCoordinateSpace_codim_two_bound hf hfg I (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) hN
    have hchoose : (n + N).choose n ≤ ((n + 2) * L) ^ n := by
      calc
        _ ≤ (N + 1) ^ n := by
          simpa [Nat.add_comm n N] using Nat.choose_add_le_add_one_pow N n
        _ ≤ _ := Nat.pow_le_pow_left (by aesop) n
    calc
      _ ≤ f.totalDegree * g.totalDegree * (n + N).choose n := hlower.trans hupper
      _ ≤ d * d * (((n + 2) * L) ^ n) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfd hgd) hchoose
      _ = _ := by simp [mul_pow, L]; ring
  · have htwo : 2 * (L - 1) ≤ N := Nat.mul_le_mul_right (L - 1) (by omega)
    have hconst : 1 ≤ (n + 2) ^ n :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    calc
      _ ≤ L ^ (n + 2) := hbox
      _ = L ^ 2 * L ^ n := by grind
      _ ≤ d ^ 2 * L ^ n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ (n + 2) ^ n * (d ^ 2 * L ^ n) := Nat.le_mul_of_pos_left _ hconst
      _ = _ := by grind

