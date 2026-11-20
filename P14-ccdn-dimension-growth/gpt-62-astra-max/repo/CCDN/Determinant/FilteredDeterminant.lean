/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Determinant.SingularTangent
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial
import CCDN.Determinant.LocalDeterminant
import CCDN.Determinant.ModularOriginGenerators
import CCDN.Determinant.SingularApproximation
import CCDN.ForMathlib.Matrix

/-! Local determinant divisibility in arbitrary dimension. The exponent is
computed from the cumulative dimensions of the origin-adic layers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {p n s N : ℕ} (r : ℕ → ℕ) (t : Fin s ↪ ((j : Fin N) × Fin (r j.val)))

/-- The sum of the deficits below successive weights. For a graded profile
this is a lower bound for the sum of the first s weights, with multiplicity. -/
def filtrationExponent (s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - (Finset.univ.sum fun j : Fin (k.val + 1) => r j.val)

/-- Layer-cake inequality with an arbitrary cutoff `K`: counting, for each
`k < K`, the weights exceeding `k` never exceeds the total weight. -/
lemma sum_weight_tail_counts_le (w : Fin s → ℕ) (K : ℕ) :
    (∑ k : Fin K, (Finset.univ.filter fun i => k.val < w i).card) ≤ ∑ i, w i := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp [Fin.card_filter_val_lt]

/-- Distinct generators of weight at most k inject into all generators in
layers zero through k, independently of the precision used to truncate them. -/
lemma low_weight_card_le (k : ℕ) :
    (Finset.univ.filter fun i => (t i).1.val ≤ k).card ≤
      ∑ j : Fin (k + 1), r j.val := by
  classical
  let φ : {i : Fin s // (t i).1.val ≤ k} → ((j : Fin (k + 1)) × Fin (r j.val)) :=
    fun i => ⟨⟨(t i.val).1.val, by omega⟩, (t i.val).2⟩
  have hφ : Function.Injective φ := by
    intro a b h
    grind
  simpa [Fintype.card_subtype] using (Fintype.card_le_of_injective φ hφ)

private lemma filtrationExponent_le_weights :
    filtrationExponent r s ≤ ∑ i, (t i).1.val := by
  classical
  apply le_trans ?_ (by solve_by_elim [sum_weight_tail_counts_le])
  apply Finset.sum_le_sum
  intro k _
  have hlow := low_weight_card_le r t k.val
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i => (t i).1.val ≤ k.val)
  grind [Fintype.card_fin]

/-- A homogeneous local generating family gives a determinant divisor
at any precision and in any dimension. -/
theorem origin_filtration_pow_dvd_det_mod {e : ℕ} [Fact p.Prime]
    (f : IntegerPolynomial (n + 1))
    (x : Fin s → Fin (n + 1) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (he : e ≤ filtrationExponent
      (fun k => Module.finrank (ZMod p) (originLayer (residueEquation p f) k)) s)
    (hfx : ∀ i, (p : ℤ) ^ e ∣ eval (x i) f)
    (F : Fin s → IntegerPolynomial (n + 1)) :
    (p : ℤ) ^ e ∣ (valueMatrix x F).det := by
  classical
  obtain ⟨r, g, hr, hg, hrep⟩ := exists_integer_hypersurface_generators (p := p) f
  rw [← (funext hr)] at he
  let N := e
  choose c hc using fun j => integer_generators_approximate_mod f r g (hrep N) (F j)
  have hdiv (i : Fin s) (z : (k : Fin N) × Fin (r k.val)) :
      (p : ℤ) ^ z.1.val ∣ eval (x i) (g z.1.val z.2) :=
    origin_power_eval_dvd p (x i) (hx i) (homogeneous_mem_origin_power (hg _ _))
  choose U₀ hU using hdiv
  let U : Matrix (Fin s) ((k : Fin N) × Fin (r k.val)) ℤ := U₀
  let V : Matrix ((k : Fin N) × Fin (r k.val)) (Fin s) ℤ :=
    fun z j => p ^ z.1.val * c j z.1 z.2
  have hdet :=
    pow_dvd_det_of_weighted_factorization U V p (fun z => z.1.val) N
      (fun _ _ => dvd_mul_right _ _) (fun t => he.trans (filtrationExponent_le_weights r t))
  have hprod (i j : Fin s) : (U * V) i j =
      ∑ k : Fin N, ∑ l, c j k l * eval (x i) (g k.val l) := by
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hU i ⟨k, l⟩]
    ring
  have hd := Matrix.dvd_det_sub_det_of_dvd_sub (valueMatrix x F)
    (U * V) (p ^ N) (fun i j => by
      rw [valueMatrix, Matrix.of_apply, hprod]
      exact hc j (x i) (hfx i) (hx i))
  simpa using dvd_add hd hdet

end
end CCDN
