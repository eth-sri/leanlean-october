/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveIntegerHeight
import Mathlib.Tactic.Module

/-! Integer points on rational affine lines. Primitive integer
directions make the line parameter integral, giving a spacing bound. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The rational affine line `{a + t • v | t ∈ ℚ}` through `a` with direction `v`. -/
def rationalAffineLine {n : ℕ} (a v : RatPoint n) : Set (RatPoint n) :=
  {x | ∃ t : ℚ, x = a + t • v}

section

variable {n : ℕ}
include n

private lemma rationalAffineLine_smul_direction (a v : RatPoint n) {c : ℚ} (hc : c ≠ 0) :
    rationalAffineLine a (c • v) = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t * c, by simpa [smul_smul] using ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t / c, by simpa [smul_smul, div_mul_cancel₀ t hc] using ht⟩

/-- Any two distinct points determine the entire parameterized rational line. -/
private lemma rationalAffineLine_eq_of_distinct_points {a v x y : RatPoint n}
    (hx : x ∈ rationalAffineLine a v) (hy : y ∈ rationalAffineLine a v) (hxy : x ≠ y) :
    rationalAffineLine x (y - x) = rationalAffineLine a v := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hts : t - s ≠ 0 := fun h => hxy (by rw [sub_eq_zero.mp h])
  rw [show (a + t • v) - (a + s • v) = (t - s) • v by module,
    rationalAffineLine_smul_direction _ _ hts]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨s + k, by rw [add_smul, add_assoc]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k - s, by module⟩

end

section

variable {n : ℕ}
include n

/-- Nonzero representatives of the same projective direction give the same line. -/
lemma rationalAffineLine_eq_of_projective_eq (a : RatPoint (n + 1))
    {v w : RatPoint (n + 1)} {hv : v ≠ 0} {hw : w ≠ 0}
    (h : Projectivization.mk ℚ v hv = Projectivization.mk ℚ w hw) :
    rationalAffineLine a v = rationalAffineLine a w := by
  obtain ⟨c, rfl⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp h
  exact rationalAffineLine_smul_direction _ _ c.ne_zero

/-- In the coordinate of maximum size, the integral line parameters lie in an
interval of length `2 * B / p.mulHeight`. -/
private theorem integral_rationalAffineLine_count (a : IntPoint (n + 1)) (p : ProjectivePoint n)
    {B : ℝ} (ha : InBox a B) :
    (count (rationalAffineLine (rationalPoint a) (rationalPoint (primitiveProjectiveRep p))) B : ℝ) ≤
      1 + 2 * B / p.mulHeight := by
  classical
  let v := primitiveProjectiveRep p
  let S := integralPoints (rationalAffineLine (rationalPoint a) (rationalPoint v)) B
  have hrep (x : S) : ∃ k : ℤ, ∀ i, x.val i = a i + k * v i := by
    obtain ⟨t, ht⟩ := (mem_integralPoints.mp x.property).2
    have hsub : rationalPoint (x.val - a) = t • rationalPoint v := by
      funext i
      have hi : (x.val i : ℚ) = (a i : ℚ) + t * v i := congrFun ht i
      simpa [rationalPoint, sub_eq_iff_eq_add, add_comm] using hi
    obtain ⟨k, rfl⟩ := integral_scalar_of_primitive (primitiveProjectiveRep_gcd p) hsub
    refine ⟨k, fun i => ?_⟩
    have hi : (x.val i : ℚ) = (a i : ℚ) + (k : ℚ) * v i := congrFun ht i
    exact_mod_cast hi
  choose k hk using hrep
  obtain ⟨j, hj⟩ := primitiveProjectiveRep_height_eq p
  have hv : (v j : ℝ) ≠ 0 := fun h => p.mulHeight_pos.ne' (by simpa [v, h] using hj.symm)
  let c : ℝ := (a j : ℝ) / (v j : ℝ)
  let r : ℝ := B / p.mulHeight
  let lo : ℤ := ⌈-r - c⌉
  let hi : ℤ := ⌊r - c⌋
  have hdiv (z : IntPoint (n + 1)) (hz : InBox z B) : |(z j : ℝ) / (v j : ℝ)| ≤ r := by
    rw [abs_div, show |(v j : ℝ)| = p.mulHeight from hj]
    exact div_le_div_of_nonneg_right (hz j) p.mulHeight_pos.le
  have h0 : -r ≤ c ∧ c ≤ r := abs_le.mp (hdiv a ha)
  have hlo : lo ≤ 0 := Int.ceil_le.mpr (by simpa only [Int.cast_zero] using sub_nonpos.mpr h0.1)
  have hhi : 0 ≤ hi := Int.le_floor.mpr (by simpa only [Int.cast_zero] using sub_nonneg.mpr h0.2)
  have hcard : S.card ≤ (Finset.Icc lo hi).card := by
    rw [← Fintype.card_coe S, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn k (fun x _ => ?_) (fun x _ y _ he => ?_)
    · have hq := hdiv x.val (mem_integralPoints.mp x.property).1
      rw [hk x j, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_right₀ _ hv] at hq
      have h := abs_le.mp (show |c + (k x : ℝ)| ≤ r from hq)
      exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by show -r - c ≤ (k x : ℝ); linarith [h.1]),
        Int.le_floor.mpr (by show (k x : ℝ) ≤ r - c; linarith [h.2])⟩
    · exact Subtype.ext (funext fun i => by rw [hk x i, hk y i, he])
  have hc : (S.card : ℤ) ≤ hi + 1 - lo := by
    rw [← Int.card_Icc_of_le lo hi (by omega)]
    exact_mod_cast hcard
  have hc' : (S.card : ℝ) ≤ (hi : ℝ) + 1 - (lo : ℝ) := by exact_mod_cast hc
  have hl : -r - c ≤ (lo : ℝ) := Int.le_ceil _
  have hh : (hi : ℝ) ≤ r - c := Int.floor_le _
  change (S.card : ℝ) ≤ _
  rw [mul_div_assoc]
  change _ ≤ 1 + 2 * r
  linarith

/-- Two distinct integral points give a projective direction of height at most
`2 * B` for the line, together with a spacing bound in that direction. -/
theorem rationalAffineLine_integer_rep_and_count (a v : RatPoint (n + 1)) {B : ℝ}
    (hcount : 1 < count (rationalAffineLine a v) B) :
    ∃ (z : IntPoint (n + 1)) (p : ProjectivePoint n), p.mulHeight ≤ 2 * B ∧
      rationalAffineLine a v = rationalAffineLine (rationalPoint z) (rationalPoint (primitiveProjectiveRep p)) ∧
      (count (rationalAffineLine a v) B : ℝ) ≤ 1 + 2 * B / p.mulHeight := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcount
  obtain ⟨hxB, hxL⟩ := mem_integralPoints.mp hx
  obtain ⟨hyB, hyL⟩ := mem_integralPoints.mp hy
  have hsub : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  let p := Projectivization.mk ℚ (rationalPoint (y - x)) (rationalPoint_ne_zero hsub)
  have he : rationalPoint (y - x) = rationalPoint y - rationalPoint x :=
    funext fun i => Int.cast_sub _ _
  have hline := (rationalAffineLine_eq_of_distinct_points hxL hyL
    ((rationalPoint_injective (n + 1)).ne hxy)).symm
  rw [← he] at hline
  have hL := hline.trans (rationalAffineLine_eq_of_projective_eq _ (primitiveProjectiveRep_mk p).symm)
  refine ⟨x, p, projective_integer_height_le _ hsub (fun i => ?_), hL, ?_⟩
  · change |((y i - x i : ℤ) : ℝ)| ≤ 2 * B
    rw [Int.cast_sub, two_mul]
    exact (abs_sub _ _).trans (add_le_add (hyB i) (hxB i))
  · rw [hL]
    exact integral_rationalAffineLine_count x p hxB

end
end
end CCDN
