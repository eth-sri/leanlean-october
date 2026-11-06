module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecNF

/-!
# WP-M (B3′, part 1): the box stretch

Two chains with the same vertex sequence in different host polygons have chain models that
differ only in the box radius (`Chain.radius = coordBound C.P + 1`, a sum over all host
vertices).  They are related by the **box stretch** `φ = σ × σ`, where
`σ x = x + (k - 1) (max (x - B) 0 + min (x + B) 0)`: the identity on `[-B, B]`, affine with slope
`k > 0` outside, so that `σ R = R'` for `k = (R' - B) / (R - B)` (design
`docs/design-downphase.md`, finding M6).

Contents: `stretch` and its algebra (identity inside, the affine pieces, strict monotonicity,
continuity, the inverse `stretch B k⁻¹`, oddness, the radius), the homeomorphism
`stretchHomeo`, and the box image `stretchPt '' box R = box R'`.
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set

/-- The stretch of the line: the identity on `[-B, B]`, slope `k` outside. -/
noncomputable def stretch (B k x : ℝ) : ℝ := x + (k - 1) * (max (x - B) 0 + min (x + B) 0)

variable {B k : ℝ}

theorem stretch_of_abs_le (_hB : 0 ≤ B) {x : ℝ} (hx : |x| ≤ B) : stretch B k x = x := by
  unfold stretch
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  grind

section
variable (hB : 0 ≤ B) {x : ℝ}
include hB
theorem stretch_of_ge (hx : B ≤ x) : stretch B k x = B + (x - B) * k := by
  unfold stretch
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  ring

theorem stretch_of_le (hx : x ≤ -B) :
    stretch B k x = -B + (x + B) * k := by
  core_grind


end

theorem continuous_stretch (B k : ℝ) : Continuous (stretch B k) := by
  unfold stretch; fun_prop

section
variable (hB : 0 ≤ B)
include hB
theorem stretch_neg (x : ℝ) : stretch B k (-x) = -stretch B k x := by
  core_grind

section
variable (hk : 0 < k)
include hk
/-- The stretch is strictly increasing. -/
theorem stretch_strictMono : StrictMono (stretch B k) := by
  -- slope at least `min 1 k` between any two points
  have key : ∀ x y, x < y → stretch B k x < stretch B k y := by
    intro x y hxy
    have e : ∀ z, stretch B k z = if z ≤ -B then -B + (z + B) * k else if z ≤ B then z
        else B + (z - B) * k := by
      intro z
      split_ifs with h1 h2
      · exact stretch_of_le hB h1
      · exact stretch_of_abs_le hB (abs_le.2 ⟨by linarith, h2⟩)
      · exact stretch_of_ge hB (by linarith)
    rw [e x, e y]
    split_ifs <;> nlinarith
  exact key

theorem stretch_inv (x : ℝ) : stretch B k⁻¹ (stretch B k x) = x := by
  rcases le_total x (-B) with h | h
  · have h1 : stretch B k x ≤ -B := by
      rw [stretch_of_le hB h]; nlinarith
    rw [stretch_of_le hB h1, stretch_of_le hB h]; grind
  · rcases le_total x B with h' | h'
    · rw [stretch_of_abs_le hB (abs_le.2 ⟨h, h'⟩), stretch_of_abs_le hB (abs_le.2 ⟨h, h'⟩)]
    · have h1 : B ≤ stretch B k x := by
        rw [stretch_of_ge hB h']; nlinarith
      rw [stretch_of_ge hB h1, stretch_of_ge hB h']; grind



end

end

/-- The stretch as a homeomorphism of the line. -/
noncomputable def stretchHomeoLine (hB : 0 ≤ B) (hk : 0 < k) : ℝ ≃ₜ ℝ where
  toFun := stretch B k
  invFun := stretch B k⁻¹
  left_inv := stretch_inv hB hk
  right_inv x := by
    have := stretch_inv hB (inv_pos.2 hk) x
    simp_all
  continuous_toFun := continuous_stretch B k
  continuous_invFun := continuous_stretch B k⁻¹

/-- **The box stretch** of the plane. -/
noncomputable def stretchPt (B k : ℝ) (p : Point) : Point := (stretch B k p.1, stretch B k p.2)

section
variable (hB : 0 ≤ B)
include hB
/-- The box stretch as a homeomorphism of the plane. -/
noncomputable def stretchHomeo (hk : 0 < k) : Point ≃ₜ Point :=
  (stretchHomeoLine hB hk).prodCongr (stretchHomeoLine hB hk)

theorem stretchPt_of_le {p : Point} (h1 : |p.1| ≤ B) (h2 : |p.2| ≤ B) :
    stretchPt B k p = p := by
  unfold stretchPt; rw [stretch_of_abs_le hB h1, stretch_of_abs_le hB h2]


end

/-- The slope that maps the radius `R` to `R'`. -/
noncomputable def slope (B R R' : ℝ) : ℝ := (R' - B) / (R - B)

theorem slope_pos {R R' : ℝ} (hR : B < R) (hR' : B < R') : 0 < slope B R R' :=
  div_pos (by linarith) (by linarith)

section
variable (hB : 0 ≤ B) {R R' : ℝ} (hR : B < R)
include hB hR
theorem stretch_radius :
    stretch B (slope B R R') R = R' := by
  have h : R - B ≠ 0 := by linarith
  rw [stretch_of_ge hB hR.le]; core_grind

section
variable (hR' : B < R')
include hR'
/-- The stretch maps the open interval `(-R, R)` onto `(-R', R')`. -/
theorem abs_stretch_lt_iff (x : ℝ) :
    |stretch B (slope B R R') x| < R' ↔ |x| < R := by
  have hk := slope_pos hR hR'
  have hm := stretch_strictMono hB hk
  have h1 : stretch B (slope B R R') R = R' := stretch_radius hB hR
  have h2 : stretch B (slope B R R') (-R) = -R' := by rw [stretch_neg hB, h1]
  have e1 : ∀ x, stretch B (slope B R R') x < R' ↔ x < R := fun x => by
    have := hm.lt_iff_lt (a := x) (b := R); simp_all
  have e2 : ∀ x, -R' < stretch B (slope B R R') x ↔ -R < x := fun x => by
    have := hm.lt_iff_lt (a := -R) (b := x); simp_all
  ram_grind

/-- **The box image.** -/
theorem stretchPt_mem_box_iff (p : Point) :
    stretchPt B (slope B R R') p ∈ Chazelle.Chain.box R' ↔ p ∈ Chazelle.Chain.box R := by
  simp only [Chazelle.Chain.mem_box_iff, stretchPt, abs_stretch_lt_iff hB hR hR']



end

end

end

end BoxT

end Chazelle.Core
