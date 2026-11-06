/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.ProjectiveBox

/-! Integer points on rational affine lines. Primitive integer
directions make the line parameter integral, giving a spacing bound. -/

namespace CCDN

section
variable {n : ℕ}

/-- The rational affine line `{a + t • v | t ∈ ℚ}` through `a` with direction `v`. -/
def rationalAffineLine (a v : RatPoint n) : Set (RatPoint n) :=
  {x | ∃ t : ℚ, x = a + t • v}

/-- The height `max_j |v j|` of an integer vector `v`. -/
def integerDirectionHeight (v : IntPoint n) : ℕ :=
  Finset.univ.sup (fun j => (v j).natAbs)

/-- Scaling the direction by a nonzero rational does not change the affine line. -/
lemma rationalAffineLine_smul_direction (a v : RatPoint n) {c : ℚ} (hc : c ≠ 0) :
    rationalAffineLine a (c • v) = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t * c, by simp_all [smul_smul]⟩
  · rintro ⟨t, ht⟩
    refine ⟨t / c, ?_⟩
    simp_all [smul_smul]

/-- Moving the base point along the direction does not change the affine line. -/
lemma rationalAffineLine_shift_base (a v : RatPoint n) (s : ℚ) :
    rationalAffineLine (a + s • v) v = rationalAffineLine a v := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨s + t, by simp_all [add_smul, add_assoc]⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ht.trans ?_⟩
    funext j
    dsimp
    ring

/-- Any two distinct points determine the entire parameterized rational line. -/
lemma rationalAffineLine_eq_of_distinct_points {a v x y : RatPoint n}
    (hx : x ∈ rationalAffineLine a v) (hy : y ∈ rationalAffineLine a v) (hxy : x ≠ y) :
    rationalAffineLine x (y - x) = rationalAffineLine a v := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hts : t - s ≠ 0 := by grind
  have he : (a + t • v) - (a + s • v) = (t - s) • v := by
    funext j
    dsimp
    ring
  rw [he, rationalAffineLine_smul_direction _ _ hts, rationalAffineLine_shift_base]

/-- A nonzero integer vector has positive height. -/
lemma integerDirectionHeight_pos {v : IntPoint n} (hv : v ≠ 0) :
    0 < integerDirectionHeight v := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  exact (Int.natAbs_pos.mpr hj).trans_le
    (Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j))

lemma exists_coordinate_integerDirectionHeight {v : IntPoint n} (hv : v ≠ 0) :
    ∃ j, |(v j : ℝ)| = integerDirectionHeight v := by
  obtain ⟨j, _⟩ := Function.ne_iff.mp hv
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup Finset.univ
    ⟨j, Finset.mem_univ j⟩ (fun j => (v j).natAbs)
  refine ⟨k, ?_⟩
  have hh : ((v k).natAbs : ℝ) = integerDirectionHeight v := mod_cast hk.symm
  simpa using hh

end

variable {n : ℕ}

/-- Integer points on a primitive line are spaced by its largest direction
coordinate. This counts the line's intersection with the integer box. -/
theorem integral_rationalAffineLine_count (a v : IntPoint n)
    (hv : v ≠ 0) (hprim : Finset.univ.gcd v = 1) {B : ℝ} (hB : 0 ≤ B) :
    (count (rationalAffineLine (rationalPoint a) (rationalPoint v)) B : ℝ) ≤
      1 + 2 * B / integerDirectionHeight v := by
  let S := integralPoints (rationalAffineLine (rationalPoint a) (rationalPoint v)) B
  have hrep (x : S) : ∃ k : ℤ, ∀ j, x.val j = a j + k * v j :=
    (show rationalPoint x.val ∈ rationalAffineLine (rationalPoint a) (rationalPoint v) ↔
          ∃ k : ℤ, ∀ j, x.val j = a j + k * v j by
        constructor
        · rintro ⟨t, ht⟩
          have hw (j) : ((x.val - a) j : ℚ) = t * v j := by
            have hh := congrFun ht j
            change (x.val j : ℚ) = (a j : ℚ) + t * v j at hh
            simp_all
          obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℚ) = t := by
            obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ v
            have hcQ : (∑ j, (v j : ℚ) * c j) = 1 := mod_cast (hc.symm.trans hprim)
            refine ⟨∑ j, (x.val - a) j * c j, ?_⟩
            push_cast
            simp_rw [hw]
            rw [show (∑ j, t * (v j : ℚ) * c j) = t * ∑ j, (v j : ℚ) * c j by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring, hcQ, mul_one]
          refine ⟨k, fun j => ?_⟩
          apply Int.cast_injective (α := ℚ)
          push_cast
          rw [hk]
          exact congrFun ht j
        · rintro ⟨k, hk⟩
          refine ⟨k, ?_⟩
          funext j
          change (x.val j : ℚ) = (a j : ℚ) + k * v j
          simp_all).mp (mem_integralPoints.mp x.property).2
  choose k hk using hrep
  have hkinj : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    grind
  let T : Finset ℤ := Finset.univ.image k
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hkinj]
    simp
  by_cases hT : T.Nonempty
  · have hTmem (t : ℤ) (ht : t ∈ T) : ∃ x : S, k x = t := by grind
    obtain ⟨xlo, hxlo⟩ := hTmem (T.min' hT) (T.min'_mem hT)
    obtain ⟨xhi, hxhi⟩ := hTmem (T.max' hT) (T.max'_mem hT)
    obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
    have hlo := (mem_integralPoints.mp xlo.property).1 j
    have hhi := (mem_integralPoints.mp xhi.property).1 j
    have hspan : ((T.max' hT : ℝ) - (T.min' hT : ℝ)) * integerDirectionHeight v ≤ 2 * B := by
      have he : (xhi.val j : ℝ) - (xlo.val j : ℝ) =
          ((T.max' hT : ℝ) - (T.min' hT : ℝ)) * (v j : ℝ) := by
        rw [hk xhi j, hk xlo j, hxhi, hxlo]
        push_cast
        ring
      have habs := (abs_sub (xhi.val j : ℝ) (xlo.val j : ℝ)).trans (add_le_add hhi hlo)
      rw [he, abs_mul, hj, abs_of_nonneg (by
        have hh := T.min'_le (T.max' hT) (T.max'_mem hT)
        simp_all)] at habs
      linarith
    have hheight : (0 : ℝ) < integerDirectionHeight v := by
      exact_mod_cast integerDirectionHeight_pos hv
    have hdif := (le_div_iff₀ hheight).mpr hspan
    have hcnt : T.card ≤ (T.max' hT : ℝ) - (T.min' hT : ℝ) + 1 := by
      have hsub : T ⊆ Finset.Icc (T.min' hT) (T.max' hT) := by
        intro k hk
        exact Finset.mem_Icc.mpr ⟨T.min'_le k hk, T.le_max' k hk⟩
      have hle := Finset.card_le_card hsub
      rw [Int.card_Icc] at hle
      have hnonneg : 0 ≤ T.max' hT - T.min' hT + 1 := by grind
      have hh : (T.card : ℤ) ≤ T.max' hT - T.min' hT + 1 := by grind
      exact_mod_cast hh
    rw [hcard] at hcnt
    change (S.card : ℝ) ≤ _
    linarith
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hT
    have hS : S.card = 0 := by grind
    change (S.card : ℝ) ≤ _
    rw [hS, Nat.cast_zero]
    positivity

/-- Divide an integer direction by the gcd of its coordinates. This gives
a primitive direction of no greater height on the same rational line. -/
theorem exists_primitive_integer_direction (w : IntPoint n) (hw : w ≠ 0) :
    ∃ v : IntPoint n, v ≠ 0 ∧ Finset.univ.gcd v = 1 ∧
      (∀ j, |(v j : ℝ)| ≤ |(w j : ℝ)|) ∧
      ∀ a : RatPoint n, rationalAffineLine a (rationalPoint w) =
        rationalAffineLine a (rationalPoint v) := by
  obtain ⟨j, _⟩ := Function.ne_iff.mp hw
  obtain ⟨v, hv, hprim⟩ := Finset.extract_gcd w
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨j, Finset.mem_univ j⟩)
  let c := Finset.univ.gcd w
  have hvc (i) : w i = c * v i := hv i (Finset.mem_univ i)
  have hc : c ≠ 0 := by aesop
  have hQ : rationalPoint w = c • rationalPoint v := by
    funext i
    change (w i : ℚ) = c * v i
    simp_all
  refine ⟨v, (by aesop), hprim, ?_, fun a => ?_⟩
  · intro i
    have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := mod_cast Int.one_le_abs hc
    rw [hvc i, Int.cast_mul, abs_mul]
    nlinarith [abs_nonneg (v i : ℝ)]
  · rw [hQ]
    exact rationalAffineLine_smul_direction _ _ (mod_cast hc)

/-- Two bounded integer points give a primitive integer direction of
height at most twice the box radius, representing their full rational line. -/
theorem exists_primitive_direction_of_two_integer_points
    (a b : IntPoint n) (hab : a ≠ b) {B : ℝ}
    (ha : InBox a B) (hb : InBox b B) :
    ∃ v : IntPoint n, v ≠ 0 ∧ Finset.univ.gcd v = 1 ∧
      (integerDirectionHeight v : ℝ) ≤ 2 * B ∧
      rationalAffineLine (rationalPoint a) (rationalPoint b - rationalPoint a) =
        rationalAffineLine (rationalPoint a) (rationalPoint v) := by
  have hw := fun h => hab (sub_eq_zero.mp h).symm
  obtain ⟨v, hv, hprim, hle, he⟩ := exists_primitive_integer_direction (b - a) hw
  refine ⟨v, hv, hprim, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
    rw [← hj]
    apply (hle j).trans
    change |((b j - a j : ℤ) : ℝ)| ≤ _
    grind
  · have hcast : rationalPoint (b - a) = rationalPoint b - rationalPoint a := by
      funext j
      exact Int.cast_sub _ _
    simpa [hcast] using he (rationalPoint a)

/-- For a nonzero primitive integer vector `v`, the multiplicative height of the projective point
`[v]` equals `max_j |v j|`. -/
theorem projective_direction_height (v : IntPoint (n + 1))
    (hv : v ≠ 0) (hprim : Finset.univ.gcd v = 1) :
    (Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv)).mulHeight =
      (integerDirectionHeight v : ℝ) := by
  rw [projective_height_primitive v hv hprim]
  have hsup : (⨆ j, |v j| : ℤ) = (integerDirectionHeight v : ℤ) := by
    apply le_antisymm
    · apply ciSup_le
      intro j
      have hh : (v j).natAbs ≤ integerDirectionHeight v :=
        Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j)
      grind
    · obtain ⟨j, hj⟩ := exists_coordinate_integerDirectionHeight hv
      have hjZ : |v j| = (integerDirectionHeight v : ℤ) := mod_cast hj
      rw [← hjZ]
      exact le_ciSup (Finite.bddAbove_range (fun j => |v j|)) j
  rw [hsup, Int.cast_natCast]

/-- Any rational affine line containing two bounded integer points has an
integer base point and primitive integer direction, with the exact spacing
estimate and the direction-height cutoff needed for summing line contributions. -/
theorem rationalAffineLine_integer_rep_and_count
    (a v : RatPoint n) {B : ℝ} (hB : 0 ≤ B)
    (hcount : 1 < count (rationalAffineLine a v) B) :
    ∃ (z w : IntPoint n), w ≠ 0 ∧ Finset.univ.gcd w = 1 ∧
      (integerDirectionHeight w : ℝ) ≤ 2 * B ∧
      rationalAffineLine a v = rationalAffineLine (rationalPoint z) (rationalPoint w) ∧
      (count (rationalAffineLine a v) B : ℝ) ≤ 1 + 2 * B / integerDirectionHeight w := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcount
  obtain ⟨hxB, hxline⟩ := mem_integralPoints.mp hx
  obtain ⟨hyB, hyline⟩ := mem_integralPoints.mp hy
  obtain ⟨w, hw, hprim, hheight, he⟩ :=
    exists_primitive_direction_of_two_integer_points x y hxy hxB hyB
  have hxyQ : rationalPoint x ≠ rationalPoint y := by
    intro h
    apply hxy
    funext j
    exact Int.cast_injective (congrFun h j)
  have hline :=
    (rationalAffineLine_eq_of_distinct_points hxline hyline hxyQ).symm.trans he
  refine ⟨x, w, hw, hprim, hheight, hline, ?_⟩
  rw [hline]
  exact integral_rationalAffineLine_count x w hw hprim hB

