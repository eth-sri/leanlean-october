module

public import Mathlib
public import PottsDiscontinuity.SixVertex.InfinityPhase

/-! # Cyclic relabelling of the real sine product -/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

theorem prod_Ioi_castSucc_last {M : Type*} [CommMonoid M] {k : ℕ}
    (f : Fin (k + 1) → M) (a : Fin k) :
    (∏ b ∈ Ioi a.castSucc, f b) = (∏ b ∈ Ioi a, f b.castSucc) * f (Fin.last k) := by
  have h1 : Ioi a.castSucc = univ.filter (fun b : Fin (k + 1) => a.castSucc < b) := by
    grind
  have h2 : Ioi a = univ.filter (fun b : Fin k => a < b) := by
    grind
  rw [h1, h2, prod_filter, prod_filter, Fin.prod_univ_castSucc]
  simp

section
variable {M : Type*} [CommMonoid M] {k : ℕ} (f : Fin (k + 1) → Fin (k + 1) → M)
theorem pairProduct_head  :
    (∏ a, ∏ b ∈ Ioi a, f a b) =
      (∏ b : Fin k, f 0 b.succ) * (∏ a : Fin k, ∏ b ∈ Ioi a, f a.succ b.succ) := by
  rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  simp

theorem pairProduct_last  :
    (∏ a, ∏ b ∈ Ioi a, f a b) =
      (∏ a : Fin k, ∏ b ∈ Ioi a, f a.castSucc b.castSucc) *
        (∏ a : Fin k, f a.castSucc (Fin.last k)) := by
  have he : Ioi (Fin.last k) = ∅ := by
    grind
  rw [Fin.prod_univ_castSucc, he, prod_empty, mul_one]
  simp_rw [prod_Ioi_castSucc_last]
  rw [prod_mul_distrib]
end

/-- Simultaneous translation of all lifted positions leaves the sine product unchanged. -/
theorem sineLiftWeight_translate {k : ℕ} (L : ℝ) (x : Fin k → ℤ) (c : ℤ) :
    sineLiftWeight L (fun a => x a + c) = sineLiftWeight L x := by
  unfold sineLiftWeight
  simp

section
variable {k : ℕ} (P : ℤ)
/-- Move the first labelled particle to the end of the ordered integer lift. -/
def cyclicLiftLeft (x : Fin (k + 1) → ℤ) : Fin (k + 1) → ℤ :=
  Fin.snoc (fun a : Fin k => x a.succ) (x 0 + P)

/-- The real sine product is unchanged by a winding-aware cyclic relabelling.
The fixed Slater phase has already cancelled, so this holds for every particle count. -/
theorem sineLiftWeight_cyclicLiftLeft (hP : P ≠ 0)
    (x : Fin (k + 1) → ℤ) :
    sineLiftWeight (P : ℝ) (cyclicLiftLeft P x) = sineLiftWeight (P : ℝ) x := by
  unfold sineLiftWeight
  rw [pairProduct_last, pairProduct_head]
  simp only [cyclicLiftLeft, Fin.snoc_castSucc, Fin.snoc_last]
  have he : ∀ a : Fin k,
      Real.sin (Real.pi * (((x 0 + P : ℤ) : ℝ) - x a.succ) / (P : ℝ)) =
        Real.sin (Real.pi * ((x a.succ : ℝ) - x 0) / (P : ℝ)) := by
    intro a
    have hp : (P : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hP
    have ht : Real.pi * (((x 0 + P : ℤ) : ℝ) - x a.succ) / (P : ℝ) =
        Real.pi - Real.pi * ((x a.succ : ℝ) - x 0) / (P : ℝ) := by
      grind
    simp_all
  simp_rw [he]
  linarith
end

end PottsDiscontinuity.SixVertex
