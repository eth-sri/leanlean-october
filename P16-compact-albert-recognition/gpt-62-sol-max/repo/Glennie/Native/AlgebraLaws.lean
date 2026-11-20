/- Native coordinate proofs. No Jordan or octonion laws are assumed. -/
module

public import Glennie.Native
public import Mathlib.Tactic.Module
@[expose] public section

namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem octMul_self_conj (x : Octonion) :
    octMul x (octConj x) = octScalar (octNormSq x) := by
  apply Prod.ext <;> simp [octMul, octConj, octScalar, octNormSq,
    Quaternion.self_mul_star, Quaternion.star_mul_self]

@[simp] theorem octNormSq_conj (x : Octonion) : octNormSq (octConj x) = octNormSq x := by
  simp [octNormSq, octConj, Quaternion.normSq_star]

theorem octMul_conj_self (x : Octonion) :
    octMul (octConj x) x = octScalar (octNormSq x) := by
  simpa using octMul_self_conj (octConj x)

theorem octScalar_smul (r s : ℝ) : r • octScalar s = octScalar (r*s) := by
  ext <;> simp [octScalar, smul_eq_mul]

local macro "coordinate_ring" : tactic => `(tactic|
  (repeat' first | apply Albert.ext | apply Prod.ext | apply Quaternion.ext) <;>
    simp [jordan_coord, oct_coord, inner_coordinates, smul_eq_mul] <;> ring)

theorem octNormSq_mul (x y : Octonion) :
    octNormSq (octMul x y) = octNormSq x * octNormSq y := by coordinate_ring

theorem octMul_right_alternative (x y : Octonion) :
    octMul (octMul x y) y = octMul x (octMul y y) := by coordinate_ring

set_option maxHeartbeats 8000000 in
theorem octMul_moufang (x y z : Octonion) :
    octMul (octMul x y) (octMul z x) = octMul (octMul x (octMul y z)) x := by coordinate_ring

theorem octDot_add_left (x y z : Octonion) :
    octDot (x+y) z = octDot x z+octDot y z := by
  simp [octDot_coordinates]
  ring

theorem octDot_smul_left (r : ℝ) (x y : Octonion) :
    octDot (r • x) y = r*octDot x y := by
  simp [octDot_coordinates, smul_eq_mul]
  ring

theorem octRe_add (x y : Octonion) : octRe (x+y) = octRe x+octRe y := by
  simp [octRe]
theorem octRe_smul (r : ℝ) (x : Octonion) : octRe (r • x) = r*octRe x := by
  simp [octRe, smul_eq_mul]
theorem octRe_sub (x y : Octonion) : octRe (x-y) = octRe x-octRe y := by
  simp [octRe]
theorem octDot_unit_left (x : Octonion) : octDot (octScalar 1) x = octRe x := by
  simp [octDot_coordinates, octScalar, octRe]
theorem octDot_add_right (x y z : Octonion) :
    octDot x (y+z) = octDot x y+octDot x z := by
  rw [octDot_comm, octDot_add_left, octDot_comm y x, octDot_comm z x]
theorem octDot_smul_right (r : ℝ) (x y : Octonion) :
    octDot x (r • y) = r*octDot x y := by
  rw [octDot_comm, octDot_smul_left, octDot_comm y x]
theorem octMul_neg_left (x y : Octonion) : octMul (-x) y = -octMul x y := by
  simpa using octMul_smul_left (-1 : ℝ) x y
theorem octMul_neg_right (x y : Octonion) : octMul x (-y) = -octMul x y := by
  simpa using octMul_smul_right (-1 : ℝ) x y
theorem octMul_sub_left (x y z : Octonion) :
    octMul (x-y) z = octMul x z-octMul y z := by
  simp [sub_eq_add_neg, octMul_add_left, octMul_neg_left]
theorem octMul_sub_right (x y z : Octonion) :
    octMul x (y-z) = octMul x y-octMul x z := by
  simp [sub_eq_add_neg, octMul_add_right, octMul_neg_right]

theorem jordan_add_left (x y z : Albert) : jordan (x+y) z = jordan x z + jordan y z := by coordinate_ring

theorem jordan_add_right (x y z : Albert) : jordan x (y+z) = jordan x y + jordan x z := by
  rw [jordan_comm, jordan_add_left, jordan_comm y x, jordan_comm z x]

theorem jordan_smul_left (r : ℝ) (x y : Albert) :
    jordan (r • x) y = r • jordan x y := by coordinate_ring

theorem jordan_smul_right (r : ℝ) (x y : Albert) :
    jordan x (r • y) = r • jordan x y := by
  rw [jordan_comm, jordan_smul_left, jordan_comm]

@[simp] theorem jordan_neg_left (x y : Albert) : jordan (-x) y = -jordan x y := by
  simpa using jordan_smul_left (-1 : ℝ) x y

@[simp] theorem jordan_neg_right (x y : Albert) : jordan x (-y) = -jordan x y := by
  simpa using jordan_smul_right (-1 : ℝ) x y

theorem jordan_sub_left (x y z : Albert) : jordan (x-y) z = jordan x z-jordan y z := by
  simp [sub_eq_add_neg, jordan_add_left]

theorem jordan_sub_right (x y z : Albert) : jordan x (y-z) = jordan x y-jordan x z := by
  simp [sub_eq_add_neg, jordan_add_right]

@[simp] theorem jordan_unit_left (x : Albert) : jordan 1 x = x := by
  apply Albert.ext
  all_goals norm_num [jordan_coord, unit, oct_coord, smul_eq_mul, Prod.mk_zero_zero, smul_smul]

@[simp] theorem jordan_unit_right (x : Albert) : jordan x 1 = x := by
  rw [jordan_comm, jordan_unit_left]

@[simp] theorem jordan_zero_left (x : Albert) : jordan 0 x = 0 := by
  simpa using jordan_smul_left (0 : ℝ) x x

@[simp] theorem jordan_zero_right (x : Albert) : jordan x 0 = 0 := by
  rw [jordan_comm, jordan_zero_left]

theorem inner_add_left (x y z : Albert) : inner (x+y) z = inner x z+inner y z := by coordinate_ring

theorem inner_add_right (x y z : Albert) : inner x (y+z) = inner x y+inner x z := by
  rw [inner_comm, inner_add_left, inner_comm x y, inner_comm x z]

theorem inner_smul_left (r : ℝ) (x y : Albert) : inner (r • x) y = r * inner x y := by coordinate_ring

theorem inner_smul_right (r : ℝ) (x y : Albert) : inner x (r • y) = r * inner x y := by
  rw [inner_comm, inner_smul_left, inner_comm x y]

@[simp] theorem inner_neg_left (x y : Albert) : inner (-x) y = -inner x y := by
  simpa using inner_smul_left (-1 : ℝ) x y

@[simp] theorem inner_neg_right (x y : Albert) : inner x (-y) = -inner x y := by
  simpa using inner_smul_right (-1 : ℝ) x y

theorem inner_sub_left (x y z : Albert) : inner (x-y) z = inner x z-inner y z := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : Albert) : inner x (y-z) = inner x y-inner x z := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_jordan_associative (x y z : Albert) :
    inner (jordan x y) z = inner x (jordan y z) := by coordinate_ring

end
end Glennie
