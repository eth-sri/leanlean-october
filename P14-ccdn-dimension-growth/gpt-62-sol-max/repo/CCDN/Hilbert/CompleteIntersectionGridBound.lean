/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.Algebra.BinomialSectionBound
import CCDN.Algebra.GridPointInterpolation
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Data.Nat.Choose.Bounds

/-! A coordinate-grid bound for a proper complete intersection. The
constant depends only on the ambient dimension; the degree dependence
is quadratic. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- At the grid interpolation degree, the complete-intersection bound retains the
product of the two individual degrees. -/
theorem proper_intersection_grid_card_le_mul {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] {n : ℕ}
    (f g : MvPolynomial (Fin (n + 2)) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (S : Finset K) (z : ι → Fin (n + 2) → K) (hz : Function.Injective z)
    (hzS : ∀ i j, z i j ∈ S) (hzf : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (z i) g = 0)
    (hN : f.totalDegree + g.totalDegree ≤ (n + 2) * (S.card - 1)) :
    Fintype.card ι ≤ (n + 2) ^ n * f.totalDegree * g.totalDegree * S.card ^ n := by
  let N := (n + 2) * (S.card - 1)
  let I := Ideal.span {f, g}
  have hzI (i : ι) : I ≤ RingHom.ker (eval (z i)) := by
    rw [Ideal.span_le]
    simp [Set.insert_subset_iff, hzf, hzg]
  have h := (grid_points_filtered_lower I S z hz hzS (fun i _ h => hzI i h)
    (N := N) (by simp [N])).trans
    (filteredCoordinateSpace_codim_two_bound hf hfg I (Ideal.subset_span (by simp))
      (Ideal.subset_span (by simp)) hN)
  by_cases hS : S.card = 0
  · have hfpos : 0 < f.totalDegree := totalDegree_pos_of_irreducible hf.irreducible
    rw [hS] at hN
    simp at hN
    omega
  have hchoose : (n + N).choose n ≤ ((n + 2) * S.card) ^ n := by
    calc
      _ ≤ (N + 1) ^ n := by simpa [Nat.add_comm] using Nat.choose_add_le_add_one_pow N n
      _ ≤ _ := Nat.pow_le_pow_left (by
        have he : N + (n + 2) = (n + 2) * S.card := by
          dsimp only [N]
          rw [← Nat.mul_add_one, Nat.sub_add_cancel (by omega)]
        omega) n
  simpa [mul_pow, mul_left_comm, mul_comm, mul_assoc] using
    h.trans (Nat.mul_le_mul_left (f.totalDegree * g.totalDegree) hchoose)

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
  classical
  let L := S.card
  have hbox : Fintype.card ι ≤ L ^ (n + 2) := by
    let ψ : ι → (Fintype.piFinset (fun _ : Fin (n + 2) => S)) :=
      fun i => ⟨z i, Fintype.mem_piFinset.mpr (hzS i)⟩
    have hinj : Function.Injective ψ := by
      intro i j h
      exact hz (congrArg Subtype.val h)
    simpa only [Fintype.card_coe, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, L] using Fintype.card_le_of_injective ψ hinj
  by_cases hL : L = 0
  simp_all
  
  let N := (n + 2) * (L - 1)
  by_cases hN : f.totalDegree + g.totalDegree ≤ N
  · refine (proper_intersection_grid_card_le_mul f g hf hfg S z hz hzS hzf hzg hN).trans ?_
    simpa only [pow_two, ← mul_assoc] using
      Nat.mul_le_mul_right (S.card ^ n) (Nat.mul_le_mul_left ((n + 2) ^ n) (Nat.mul_le_mul hfd hgd))
  · have htwo : 2 * (L - 1) ≤ N := Nat.mul_le_mul_right (L - 1) (by omega)
    have hLd : L ≤ d := by omega
    calc
      _ ≤ L ^ (n + 2) := hbox
      _ = L ^ 2 * L ^ n := by ring
      _ ≤ d ^ 2 * L ^ n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hLd 2)
      _ ≤ (n + 2) ^ n * (d ^ 2 * L ^ n) := Nat.le_mul_of_pos_left _ (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
      _ = _ := by ring

end
end CCDN
