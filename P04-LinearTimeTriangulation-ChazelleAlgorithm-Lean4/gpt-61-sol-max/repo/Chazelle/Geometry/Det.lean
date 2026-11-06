module

public meta import Chazelle.Arithmetic

public import Chazelle.Geometry.Basic

/-!
# The orientation determinant

`Chazelle.det a b c = (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)` is twice the
signed area of the triangle `a b c`.  This file collects its algebraic properties:
symmetries, vanishing on collinear triples, affinity along segments, and the two
identities underlying barycentric coordinates
(`det_bary_sum`, `det_smul_eq_bary_combination`).
-/

namespace Chazelle

namespace Geometry

public section

/-! ### Symmetries -/

section
variable (a b c : Point)
/-- Swapping the first two arguments negates the determinant. -/
theorem det_swap12 : det b a c = - det a b c := by
  unfold det; ring

/-- Swapping the last two arguments negates the determinant. -/
theorem det_swap23 : det a c b = - det a b c := by
  unfold det; ring

/-- Swapping the outer arguments negates the determinant. -/
theorem det_swap13 : det c b a = - det a b c := by
  unfold det; ring

/-- The determinant is invariant under cyclic rotation. -/
theorem det_cyclic : det b c a = det a b c := by
  unfold det; ring

/-- The determinant is invariant under the other cyclic rotation. -/
theorem det_cyclic_right : det c a b = det a b c := by
  unfold det; ring


end

@[simp] theorem det_self_left (a c : Point) : det a a c = 0 := by
  unfold det; ring

@[simp] theorem det_self_right (a b : Point) : det a b b = 0 := by
  unfold det; ring

@[simp] theorem det_self_outer (a b : Point) : det a b a = 0 := by
  unfold det; ring

/-- A nonzero determinant forces the three points to be pairwise distinct. -/
theorem ne_of_det_ne_zero {a b c : Point} (h : det a b c ≠ 0) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  aesop

/-! ### Affinity along segments -/

/-- The determinant is affine in its last argument along `lerp`. -/
theorem det_lerp (a b p q : Point) (t : ℝ) :
    det a b (lerp p q t) = (1 - t) * det a b p + t * det a b q := by
  core_grind [det]

/-- The determinant is affine in its middle argument along `lerp`. -/
theorem det_lerp_mid (a c p q : Point) (t : ℝ) :
    det a (lerp p q t) c = (1 - t) * det a p c + t * det a q c := by
  core_grind [det]

/-- The determinant is affine in its first argument along `lerp`. -/
theorem det_lerp_left (b c p q : Point) (t : ℝ) :
    det (lerp p q t) b c = (1 - t) * det p b c + t * det q b c := by
  core_grind [det]

/-- The determinant is affine in its last argument along `x + t • v`. -/
theorem det_add_smul (a b x v : Point) (t : ℝ) :
    det a b (x + t • v) = det a b x + t * det a b (a + v) := by
  grind [det, add_fst, add_snd, smul_fst, smul_snd]

/-- The determinant vanishes on the segment: `c ∈ segment a b → det a b c = 0`. -/
theorem det_eq_zero_of_mem_segment {a b c : Point} (h : c ∈ Chazelle.segment a b) :
    det a b c = 0 := by
  obtain ⟨t, -, -, rfl⟩ := mem_segment_iff_lerp.1 h
  rw [det_lerp]; simp

/-- The determinant vanishes on the line through `a` and `b`. -/
theorem det_lerp_self (a b : Point) (t : ℝ) : det a b (lerp a b t) = 0 := by
  rw [det_lerp]; simp

/-- Converse: if `det a b c = 0` and `a ≠ b`, then `c` lies on the line through `a` and `b`. -/
theorem exists_lerp_of_det_eq_zero {a b c : Point} (hab : a ≠ b) (h : det a b c = 0) :
    ∃ t : ℝ, c = lerp a b t := by
  unfold det at h
  by_cases h1 : b.1 - a.1 = 0
  · have h2 : b.2 - a.2 ≠ 0 := by
      grind
    refine ⟨(c.2 - a.2) / (b.2 - a.2), point_ext ?_ ?_⟩
    all_goals core_grind
  · refine ⟨(c.1 - a.1) / (b.1 - a.1), point_ext ?_ ?_⟩
    all_goals core_grind

/-! ### Continuity -/

/-- `x ↦ det a b x` is continuous. -/
theorem continuous_det_right (a b : Point) : Continuous (fun x : Point => det a b x) := by
  unfold det; fun_prop

/-- `x ↦ det a x c` is continuous. -/
theorem continuous_det_mid (a c : Point) : Continuous (fun x : Point => det a x c) := by
  unfold det; fun_prop

/-- `x ↦ det x b c` is continuous. -/
theorem continuous_det_left (b c : Point) : Continuous (fun x : Point => det x b c) := by
  unfold det; fun_prop

/-! ### The barycentric identities -/

/-- The three sub-determinants of `x` in the triangle `a b c` sum to `det a b c`. -/
theorem det_bary_sum (a b c x : Point) : det x b c + det a x c + det a b x = det a b c := by
  unfold det; ring

/-- The barycentric reconstruction identity (in vector form). -/
theorem det_smul_eq_bary_combination (a b c x : Point) :
    det a b c • x = det x b c • a + det a x c • b + det a b x • c := by
  ext <;> simp_all [det, add_fst, add_snd, smul_fst, smul_snd] <;> ring

/-- Multilinearity: `det` of a convex combination in the last slot. -/
theorem det_smul_add_smul_add_smul (a b p q r : Point) (u v w : ℝ) (huvw : u + v + w = 1) :
    det a b (u • p + v • q + w • r) = u * det a b p + v * det a b q + w * det a b r := by
  grind [det, add_fst, add_snd, smul_fst, smul_snd]

end

end Geometry

end Chazelle
