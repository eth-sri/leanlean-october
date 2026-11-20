/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectivePrimitive

/-! Integer points on rational affine lines. Primitive integer
directions make the line parameter integral, giving a spacing bound. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {n : ℕ}

/-- The rational affine line `{a + t • v | t ∈ ℚ}` through `a` with direction `v`. -/
def rationalAffineLine (a v : RatPoint n) : Set (RatPoint n) :=
  {x | ∃ t : ℚ, x = a + t • v}

section

variable (a v : RatPoint n)

/-- Scaling the direction by a nonzero rational does not change the affine line. -/
lemma rationalAffineLine_smul_direction {c : ℚ} (hc : c ≠ 0) :
    rationalAffineLine a (c • v) = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t * c, by simpa only [smul_smul] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t / c, ?_⟩
    simpa only [smul_smul, div_mul_cancel₀ t hc] using ht

/-- Moving the base point along the direction does not change the affine line. -/
lemma rationalAffineLine_shift_base (s : ℚ) :
    rationalAffineLine (a + s • v) v = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨s + t, by simpa [add_smul, add_assoc] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ht.trans ?_⟩
    funext j
    dsimp
    ring

end

open Finset

private theorem int_multiple {n : ℕ} (v w : IntPoint n) (hv : univ.gcd v = 1)
    {t : ℚ} (h : rationalPoint w = t • rationalPoint v) : ∃ k : ℤ, (k:ℚ) = t := by
  obtain ⟨c,hc⟩ := gcd_eq_sum_mul univ v
  have he : (∑ j, (v j : ℚ)*c j) = 1 := by exact_mod_cast hc.symm.trans hv
  refine ⟨∑ j, w j * c j,?_⟩
  have hw (j) : (w j:ℚ) = t*v j := congrFun h j
  push_cast; simp_rw [hw,mul_assoc]; rw [← mul_sum,he,mul_one]

lemma line_eq_rep {n : ℕ} (a v : RatPoint (n+1)) (hv : v ≠ 0) (p : ProjectivePoint n)
    (hp : Projectivization.mk ℚ v hv = p) : rationalAffineLine a v = rationalAffineLine a p.rep := by
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp (hp.trans p.mk_rep.symm)
  rw [← hc]; exact rationalAffineLine_smul_direction _ _ c.ne_zero

/-- The height of the direction controls the number of integer parameters:
relative to any boxed point their absolute values are at most `2B / H`. -/
theorem primitive_line_spacing {n : ℕ} (p : ProjectivePoint n) (a : IntPoint (n+1))
    {B : ℝ} (hB : 0 ≤ B) (ha : InBox a B) :
    (count (rationalAffineLine (rationalPoint a) p.rep) B : ℝ) ≤ 4*B/p.mulHeight+1 := by
  classical
  let v := primitiveProjectiveRep p
  rw [← line_eq_rep (rationalPoint a) _ _ _ (primitiveProjectiveRep_mk p)]
  obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f:=fun i => |v i|)
  have hH : |(v j:ℝ)| = p.mulHeight := by
    rw [primitiveProjectiveRep_height,← hj,Int.cast_abs]
  have hp := zero_lt_one.trans_le p.one_le_mulHeight
  let S := integralPoints (rationalAffineLine (rationalPoint a) (rationalPoint v)) B
  have hex (x : S) : ∃ k : ℤ, x.val = a+k • v := by
    obtain ⟨t,ht⟩ := (mem_integralPoints.mp x.2).2
    obtain ⟨k,hk⟩ := int_multiple v (x.val-a) (primitiveProjectiveRep_gcd p) (t:=t) (by
      funext i; change ((x.val i-a i:ℤ):ℚ)=_; rw [Int.cast_sub]; exact sub_eq_iff_eq_add'.mpr (congrFun ht i))
    refine ⟨k,funext fun i => Int.cast_injective (α:=ℚ) ?_⟩
    change (x.val i:ℚ) = ((a i+k*v i:ℤ):ℚ); push_cast; rw [hk]; exact congrFun ht i
  choose k hk using hex
  have mem (x : S) : k x ∈ boxInterval (2*B/p.mulHeight) := by
    rw [mem_boxInterval,le_div_iff₀ hp,← hH,← abs_mul]
    have he : (k x:ℝ)*(v j:ℝ) = (x.val j:ℝ)-a j := by rw [hk x]; simp
    rw [he]; linarith [(abs_sub (x.val j:ℝ) (a j)).trans (add_le_add ((mem_integralPoints.mp x.2).1 j) (ha j))]
  have hcard := Fintype.card_le_of_injective (fun x : S => (⟨k x,mem x⟩ : boxInterval (2*B/p.mulHeight))) (fun x y h => Subtype.ext ((hk x).trans ((congrArg (fun t : ℤ => a+t • v) (congrArg Subtype.val h)).trans (hk y).symm)))
  have hc : (S.card:ℝ) ≤ (boxInterval (2*B/p.mulHeight)).card := by exact_mod_cast (by simpa only [Fintype.card_coe] using hcard : S.card ≤ _)
  exact hc.trans ((boxInterval_card (by positivity)).trans_eq (by ring))

end
end CCDN
