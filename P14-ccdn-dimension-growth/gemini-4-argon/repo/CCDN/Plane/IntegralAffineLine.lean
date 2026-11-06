/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveBox

/-! Integer points on rational affine lines. Primitive integer
directions make the line parameter integral, giving a spacing bound. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The rational affine line `{a + t • v | t ∈ ℚ}` through `a` with direction `v`. -/
def rationalAffineLine {n : ℕ} (a v : RatPoint n) : Set (RatPoint n) :=
  {x | ∃ t : ℚ, x = a + t • v}

/-- The height `max_j |v j|` of an integer vector `v`. -/
def integerDirectionHeight {n : ℕ} (v : IntPoint n) : ℕ :=
  Finset.univ.sup (fun j => (v j).natAbs)

/-- Scaling the direction by a nonzero rational does not change the affine line. -/
lemma rationalAffineLine_smul_direction {n : ℕ} (a v : RatPoint n) {c : ℚ} (hc : c ≠ 0) :
    rationalAffineLine a (c • v) = rationalAffineLine a v := by
  ext x
  exact ⟨fun ⟨t, ht⟩ => ⟨t * c, by simpa only [smul_smul] using ht⟩,
    fun ⟨t, ht⟩ => ⟨t / c, by simpa only [smul_smul, div_mul_cancel₀ t hc] using ht⟩⟩

/-- Moving the base point along the direction does not change the affine line. -/
lemma rationalAffineLine_shift_base {n : ℕ} (a v : RatPoint n) (s : ℚ) :
    rationalAffineLine (a + s • v) v = rationalAffineLine a v := by
  ext x
  exact ⟨fun ⟨t, ht⟩ => ⟨s + t, by simpa only [add_smul, add_assoc] using ht⟩,
    fun ⟨t, ht⟩ => ⟨t - s, ht.trans (by funext j; dsimp; ring)⟩⟩

/-- A nonzero integer vector has positive height. -/
lemma integerDirectionHeight_pos {n : ℕ} {v : IntPoint n} (hv : v ≠ 0) :
    0 < integerDirectionHeight v := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  exact (Int.natAbs_pos.mpr hj).trans_le
    (Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j))

private lemma exists_coordinate_integerDirectionHeight {n : ℕ} {v : IntPoint n} (hv : v ≠ 0) :
    ∃ j, |(v j : ℝ)| = integerDirectionHeight v := by
  obtain ⟨j, _⟩ := Function.ne_iff.mp hv
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
    ⟨j, Finset.mem_univ j⟩ (fun j => (v j).natAbs)
  exact ⟨k, by simpa only [Nat.cast_natAbs, Int.cast_abs] using
    (by exact_mod_cast hk.symm : ((v k).natAbs : ℝ) = integerDirectionHeight v)⟩

/-- For a nonzero primitive integer vector `v`, the multiplicative height of the projective point
`[v]` equals `max_j |v j|`. -/
theorem projective_direction_height {n : ℕ} (v : IntPoint (n + 1))
    (hv : v ≠ 0) (hprim : Finset.univ.gcd v = 1) :
    (Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv)).mulHeight =
      (integerDirectionHeight v : ℝ) := by
  rw [projective_height_primitive v hv hprim]
  have hsup : (⨆ j, |v j| : ℤ) = (integerDirectionHeight v : ℤ) := by
    refine le_antisymm (ciSup_le fun j => ?_) ?_
    · simpa only [Int.natCast_natAbs] using
        (by exact_mod_cast Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j) :
          ((v j).natAbs : ℤ) ≤ (integerDirectionHeight v : ℤ))
    · obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
      rw [← (by exact_mod_cast hj : |v j| = (integerDirectionHeight v : ℤ))]
      exact le_ciSup (Finite.bddAbove_range fun j => |v j|) j
  rw [hsup, Int.cast_natCast]

/-- Any rational affine line containing two bounded integer points has an
integer base point and primitive integer direction, with the exact spacing
estimate and the direction-height cutoff needed for summing line contributions. -/
theorem rationalAffineLine_integer_rep_and_count {n : ℕ}
    (a v : RatPoint n) {B : ℝ} (hB : 0 ≤ B)
    (hcount : 1 < count (rationalAffineLine a v) B) :
    ∃ (z w : IntPoint n), w ≠ 0 ∧ Finset.univ.gcd w = 1 ∧
      InBox z B ∧ (integerDirectionHeight w : ℝ) ≤ 2 * B ∧
      rationalAffineLine a v = rationalAffineLine (rationalPoint z) (rationalPoint w) ∧
      (count (rationalAffineLine a v) B : ℝ) ≤ 1 + 2 * B / integerDirectionHeight w := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcount
  obtain ⟨hxB, s, hxs⟩ := mem_integralPoints.mp hx
  obtain ⟨hyB, t, hty⟩ := mem_integralPoints.mp hy
  have hw0 : y - x ≠ 0 := fun h => hxy (sub_eq_zero.mp h).symm
  obtain ⟨j0, _⟩ := Function.ne_iff.mp hw0
  obtain ⟨w, hw, hprim⟩ := Finset.extract_gcd (y - x)
    (⟨j0, Finset.mem_univ j0⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
  let c := Finset.univ.gcd (y - x)
  have hvc (i) : (y - x) i = c * w i := hw i (Finset.mem_univ i)
  have hc : c ≠ 0 := fun he => hw0 (funext fun i => by simpa [he] using hvc i)
  have hw_ne : w ≠ 0 := fun he => hw0 (funext fun i => by simpa [he] using hvc i)
  obtain ⟨j_max, hj_max⟩ := exists_coordinate_integerDirectionHeight hw_ne
  have hheight : (integerDirectionHeight w : ℝ) ≤ 2 * B := by
    have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := mod_cast Int.one_le_abs hc
    have hle : |(w j_max : ℝ)| ≤ |((y - x) j_max : ℝ)| := by
      rw [hvc j_max, Int.cast_mul, abs_mul]; nlinarith [abs_nonneg (w j_max : ℝ)]
    rw [← hj_max]
    exact hle.trans (by
      change |((y j_max - x j_max : ℤ) : ℝ)| ≤ _
      rw [Int.cast_sub]
      linarith [(abs_sub (y j_max : ℝ) (x j_max : ℝ)).trans (add_le_add (hyB j_max) (hxB j_max))])
  have hts : t - s ≠ 0 := fun he => hxy (funext fun j =>
    Int.cast_injective (α := ℚ) (by
      have h1 := congrFun hxs j; have h2 := congrFun hty j
      rw [sub_eq_zero.mp he] at h2; exact h1.trans h2.symm))
  have hline : rationalAffineLine a v =
      rationalAffineLine (rationalPoint x) (rationalPoint w) := by
    rw [← rationalAffineLine_shift_base a v s, ← hxs,
      ← rationalAffineLine_smul_direction (rationalPoint x) v hts,
      show (t - s) • v = rationalPoint y - rationalPoint x by
        funext j; rw [hxs, hty]; dsimp; ring,
      show rationalPoint y - rationalPoint x = (c : ℚ) • rationalPoint w by
        funext i; change (y i : ℚ) - x i = (c : ℚ) * w i; exact_mod_cast hvc i,
      rationalAffineLine_smul_direction _ _ (mod_cast hc)]
  refine ⟨x, w, hw_ne, hprim, hxB, hheight, hline, ?_⟩
  rw [hline]
  let S := integralPoints (rationalAffineLine (rationalPoint x) (rationalPoint w)) B
  obtain ⟨u, hu⟩ := Finset.gcd_eq_sum_mul Finset.univ w
  have huQ : (∑ j, (w j : ℚ) * u j) = 1 := mod_cast hu.symm.trans hprim
  have hrep (z : S) : ∃ k : ℤ, ∀ j, z.val j = x j + k * w j := by
    obtain ⟨r, hr⟩ := (mem_integralPoints.mp z.property).2
    have hzw (j) : ((z.val - x) j : ℚ) = r * w j := by
      have hh : (z.val j : ℚ) = (x j : ℚ) + r * w j := congrFun hr j
      change ((z.val j - x j : ℤ) : ℚ) = _; push_cast; linarith
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℚ) = r := ⟨∑ i, (z.val - x) i * u i, by
      push_cast; simp_rw [hzw]
      rw [show (∑ i, r * (w i : ℚ) * u i) = r * ∑ i, (w i : ℚ) * u i by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, huQ, mul_one]⟩
    refine ⟨k, fun j => Int.cast_injective (α := ℚ) ?_⟩
    push_cast; rw [hk]; exact congrFun hr j
  choose k hk using hrep
  have hkinj : Function.Injective k := fun z₁ z₂ h =>
    Subtype.ext (funext fun j => by rw [hk z₁ j, hk z₂ j, h])
  let T : Finset ℤ := Finset.univ.image k
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hkinj, Finset.card_univ, Fintype.card_coe]
  by_cases hT : T.Nonempty
  · obtain ⟨xlo, _, hxlo⟩ := Finset.mem_image.mp (T.min'_mem hT)
    obtain ⟨xhi, _, hxhi⟩ := Finset.mem_image.mp (T.max'_mem hT)
    have hlo := (mem_integralPoints.mp xlo.property).1 j_max
    have hhi := (mem_integralPoints.mp xhi.property).1 j_max
    have hspan : ((T.max' hT : ℝ) - (T.min' hT : ℝ)) * integerDirectionHeight w ≤ 2 * B := by
      have habs := (abs_sub (xhi.val j_max : ℝ) (xlo.val j_max : ℝ)).trans (add_le_add hhi hlo)
      rw [show (xhi.val j_max : ℝ) - (xlo.val j_max : ℝ) =
          ((T.max' hT : ℝ) - (T.min' hT : ℝ)) * (w j_max : ℝ) by
        rw [hk xhi j_max, hk xlo j_max, hxhi, hxlo]; push_cast; ring,
        abs_mul, hj_max, abs_of_nonneg (sub_nonneg.mpr
          (mod_cast T.min'_le (T.max' hT) (T.max'_mem hT)))] at habs
      linarith
    have hdif := (le_div_iff₀ (by exact_mod_cast integerDirectionHeight_pos hw_ne)).mpr hspan
    have hle := Finset.card_le_card
      (fun m hm => Finset.mem_Icc.mpr ⟨T.min'_le m hm, T.le_max' m hm⟩ :
        T ⊆ Finset.Icc (T.min' hT) (T.max' hT))
    rw [Int.card_Icc, hcard] at hle
    have hmin_max := T.min'_le (T.max' hT) (T.max'_mem hT)
    have hcntZ : (S.card : ℤ) ≤ T.max' hT - T.min' hT + 1 := by
      have hh : (S.card : ℤ) ≤ ((T.max' hT + 1 - T.min' hT).toNat : ℤ) := mod_cast hle
      rw [Int.toNat_of_nonneg (by omega)] at hh; omega
    have hcnt : (S.card : ℝ) ≤ (T.max' hT : ℝ) - (T.min' hT : ℝ) + 1 := mod_cast hcntZ
    change (S.card : ℝ) ≤ _; linarith
  · have hS : S.card = 0 := by
      simpa only [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.card_empty] using hcard.symm
    change (S.card : ℝ) ≤ _; rw [hS, Nat.cast_zero]; positivity

end
end CCDN
