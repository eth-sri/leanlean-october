module

public import Mathlib

/-! # A strictly concave incoming angular profile

For `w = sign(x) v / |x|^(1/3)` the angular tails must be exactly `|w|^α`,
so that the homogeneous lift is smooth across `x = 0`, away from `v = 0`.
Extend the left tail through `w = 0` by extending its *second derivative*.
This permits strict concavity, with a positive intercept, for every `0 < α < 1`.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
open Set Real MeasureTheory
open scoped ContDiff Topology Interval

def base (w : ℝ) : ℝ :=
  let s := smoothTransition (4 * (w + 1))
  (1 - s) * (-w) + s

private theorem base_lower (w : ℝ) : 3 / 4 ≤ base w := by
  unfold base
  dsimp only
  by_cases h : 1 ≤ 4 * (w + 1)
  · rw [smoothTransition.one_of_one_le h]; norm_num
  · have := mul_nonneg (sub_nonneg.mpr (smoothTransition.le_one (4 * (w + 1))))
        (show 0 ≤ -w - 3 / 4 by linarith)
    linarith [smoothTransition.nonneg (4 * (w + 1))]

private theorem base_left {w : ℝ} (h : w ≤ -1) : base w = -w := by
  simp [base, smoothTransition.zero_of_nonpos (show 4 * (w + 1) ≤ 0 by linarith)]

def curvature (α w : ℝ) : ℝ := α * (α - 1) * (base w) ^ (α - 2)

private theorem smooth_curvature (α : ℝ) : ContDiff ℝ ∞ (curvature α) := by
  have hs : ContDiff ℝ ∞ (fun w : ℝ => smoothTransition (4 * (w + 1))) :=
    smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))
  have hb : ContDiff ℝ ∞ base := (contDiff_const.sub hs).mul contDiff_id.neg |>.add hs
  exact contDiff_const.mul (hb.rpow_const_of_ne (fun w => ne_of_gt (by linarith [base_lower w])))

variable {α : ℝ} (ha : 0 < α) (ha1 : α < 1)

include ha ha1 in
private theorem curvature_bounds (w : ℝ) :
    -(2 * α * (1 - α)) ≤ curvature α w ∧ curvature α w < 0 := by
  have hb : 0 < base w := by linarith [base_lower w]
  have hp : (base w) ^ (α - 2) ≤ (2 : ℝ) := calc
    _ ≤ (3 / 4 : ℝ) ^ (α - 2) := rpow_le_rpow_of_nonpos (by norm_num) (base_lower w) (by linarith)
    _ ≤ (3 / 4 : ℝ) ^ ((-2 : ℤ) : ℝ) :=
      rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by push_cast; linarith)
    _ ≤ _ := by rw [rpow_intCast]; norm_num
  unfold curvature
  exact ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg ha.le (by linarith : 0 ≤ 1 - α))],
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha (by linarith)) (rpow_pos_of_pos hb _)⟩

def primitive (c : ℝ) (g : ℝ → ℝ) (w : ℝ) : ℝ := c + ∫ s in (-1 : ℝ)..w, g s

private theorem deriv_primitive {g : ℝ → ℝ} (hg : Continuous g) (c w : ℝ) :
    HasDerivAt (primitive c g) (g w) w :=
  (hg.integral_hasStrictDerivAt (-1) w).hasDerivAt.const_add c

private theorem smooth_primitive {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (c : ℝ) :
    ContDiff ℝ ∞ (primitive c g) := by
  apply contDiff_infty_iff_deriv.2
  have h := deriv_primitive hg.continuous c
  exact ⟨fun w => (h w).differentiableAt, by rwa [show deriv (primitive c g) = g from funext fun w => (h w).deriv]⟩

def slope (α : ℝ) := primitive (-α) (curvature α)
def incoming (α : ℝ) := primitive 1 (slope α)

theorem smooth_incoming : ContDiff ℝ ∞ (incoming α) :=
  smooth_primitive (smooth_primitive (smooth_curvature α) _) _

private theorem deriv_incoming : deriv (incoming α) = slope α :=
  funext fun w => (deriv_primitive (smooth_primitive (smooth_curvature α) _).continuous 1 w).deriv

include ha ha1 in
theorem incoming_concave (w : ℝ) : deriv (deriv (incoming α)) w < 0 := by
  rw [deriv_incoming, show deriv (slope α) w = _ from
    (deriv_primitive (smooth_curvature α).continuous _ w).deriv]
  exact (curvature_bounds ha ha1 w).2

section
variable {g G : ℝ → ℝ} (hg : Continuous g) (h : ∀ w ≤ -1, HasDerivAt G (g w) w) {w : ℝ}
    (hw : w ≤ -1)
include hw

include hg h in
private theorem primitive_eq_left :
    primitive (G (-1)) g w = G w := by
  unfold primitive
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z hz => h z
    ((uIcc_of_ge hw ▸ hz : z ∈ Icc w (-1)).2)) (hg.intervalIntegrable ..)]
  ring

private theorem slope_left : slope α w = -α * (-w) ^ (α - 1) := by
  let G := fun z : ℝ => -α * (-z) ^ (α - 1)
  have h (z : ℝ) (hz : z ≤ -1) : HasDerivAt G (curvature α z) z := by
    convert ((((hasDerivAt_id z).neg.rpow_const (p := α - 1) (Or.inl (by dsimp; linarith))).const_mul (-α))) using 1
    · rfl
    · rw [curvature, base_left hz]; dsimp
      ring_nf
  have hG : G (-1) = -α := by simp [G]
  simpa only [hG, slope, G] using primitive_eq_left (smooth_curvature α).continuous h hw

theorem incoming_left : incoming α w = (-w) ^ α := by
  have h (z : ℝ) (hz : z ≤ -1) : HasDerivAt (fun y : ℝ => (-y) ^ α) (slope α z) z := by
    rw [slope_left hz]
    simpa using (hasDerivAt_id z).neg.rpow_const (p := α) (Or.inl (by dsimp; linarith))
  simpa [incoming, slope] using primitive_eq_left (smooth_primitive (smooth_curvature α) _).continuous h hw

end

include ha ha1 in
theorem incoming_slope_neg {w : ℝ} (hw : -1 ≤ w) : deriv (incoming α) w < 0 := by
  rw [deriv_incoming]; unfold slope primitive
  have hi := intervalIntegral.integral_mono_on (μ := volume) hw
    ((smooth_curvature α).continuous.intervalIntegrable ..) (continuous_const.intervalIntegrable ..)
    (fun t _ => (curvature_bounds ha ha1 t).2.le)
  simpa using (add_neg_of_neg_of_nonpos (neg_lt_zero.mpr ha) (by simpa using hi))

include ha ha1 in
theorem incoming_pos {w : ℝ} (hw : w ≤ 0) : 0 < incoming α w := by
  by_cases h : w ≤ -1
  · rw [incoming_left h]; exact rpow_pos_of_pos (by linarith) _
  have hs {s : ℝ} (hs : -1 ≤ s) : -α - 2 * α * (1 - α) * (s + 1) ≤ slope α s := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hs (continuous_const.intervalIntegrable ..)
      ((smooth_curvature α).continuous.intervalIntegrable ..) (fun x _ => (curvature_bounds ha ha1 x).1)
    simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul] at hi
    unfold slope primitive
    linarith
  let L := fun s : ℝ => -α - 2 * α * (1 - α) * (s + 1)
  let G := fun s : ℝ => -α * (s + 1) - α * (1 - α) * (s + 1)^2
  have hd (s : ℝ) : HasDerivAt G (L s) s := by
    have h := (hasDerivAt_id s).add_const 1
    convert (h.const_mul (-α)).sub ((h.pow 2).const_mul (α * (1 - α))) using 1
    · rfl
    · dsimp [L]; ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) (le_of_lt (lt_of_not_ge h))
    (f := L) ((by dsimp [L]; fun_prop : Continuous L).intervalIntegrable ..)
    ((smooth_primitive (smooth_curvature α) _).continuous.intervalIntegrable ..)
    (fun s hs' => hs hs'.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by dsimp [L]; fun_prop : Continuous L).intervalIntegrable ..)] at hi
  dsimp [G] at hi
  unfold incoming primitive
  change 0 < 1 + ∫ s in (-1 : ℝ)..w, primitive (-α) (curvature α) s
  have h1 : w + 1 ≤ 1 := by linarith
  have h0 : 0 ≤ w + 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le,
    mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 2) h0 h1) (mul_nonneg ha.le (by linarith : 0 ≤ 1 - α)), sq_pos_of_pos (sub_pos.mpr ha1)]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
