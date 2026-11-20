module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileBounds
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib

/-! # Cutting off a homogeneous profile on a small gauge ball -/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ClassicalProfile
open Filter Set Real
open scoped ContDiff Topology

variable {d : ℕ} {α : ℝ} (m : ClassicalProfile d α)

/-- A single smooth regularization suffices: every other core is obtained by dilation. -/
def core (q : XV d) := smoothTransition (2 * rho q ^ 6 - 1) * m.H q

private theorem core_origin : m.core =ᶠ[𝓝 0] fun _ => 0 := by
  have hc : Continuous fun q : XV d => 2 * rho q ^ 6 - 1 := (continuous_const.mul ((continuous_rho d).pow 6)).sub continuous_const
  have he : ∀ᶠ q : XV d in 𝓝 0, 2 * rho q ^ 6 - 1 < 0 := (isOpen_lt hc continuous_const).mem_nhds (by simp)
  filter_upwards [he] with q hq
  simp [core,smoothTransition.zero_of_nonpos hq.le]

theorem core_smooth : ContDiff ℝ ∞ m.core := by
  rw [contDiff_iff_contDiffAt]; intro q
  by_cases hq : q = 0
  · subst q; exact contDiffAt_const.congr_of_eventuallyEq m.core_origin
  have hh := m.smooth.contDiffAt (isOpen_compl_singleton.mem_nhds hq)
  have hp : ContDiff ℝ ∞ (fun q : XV d => rho q ^ 6) := by
    simp_rw [rho_pow_six]; exact (PDE.contDiff_vecNormSq.comp contDiff_fst).add
      ((PDE.contDiff_vecNormSq.comp contDiff_snd).pow 3)
  exact (smoothTransition.contDiff.comp ((contDiff_const.mul hp).sub contDiff_const)).contDiffAt.mul hh

theorem core_eq {q : XV d} (hq : 1 ≤ rho q) : m.core q = m.H q := by
  have hp : 1 ≤ rho q ^ 6 := one_le_pow₀ hq
  simp [core,smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*rho q^6-1)]

/-- Replace the singularity by a flat core of gauge radius `r`. -/
def regular (r : ℝ) (q : XV d) := r^α * m.core (dilate r⁻¹ q)

theorem regular_smooth (r : ℝ) : ContDiff ℝ ∞ (m.regular r) :=
  contDiff_const.mul (m.core_smooth.comp (dilationLinearMap d r⁻¹).contDiff)

theorem regular_eq {r : ℝ} (hr : 0 < r) {q : XV d} (hq : r ≤ rho q) : m.regular r q = m.H q := by
  unfold regular
  rw [m.core_eq (by rwa [rho_dilate _ (inv_pos.mpr hr), inv_mul_eq_div, one_le_div hr]),
    m.homogeneous _ (inv_pos.mpr hr), inv_rpow hr.le, ← mul_assoc, mul_inv_cancel₀ (rpow_pos_of_pos hr _).ne', one_mul]

@[simp] theorem regular_zero (r : ℝ) : m.regular r 0 = 0 := by simp [regular,m.core_origin.eq_of_nhds]

theorem regular_nonneg {r : ℝ} (hr : 0 < r) (q : XV d) : 0 ≤ m.regular r q := by
  by_cases hq : dilate r⁻¹ q = 0
  · simp [regular,hq,m.core_origin.eq_of_nhds]
  · exact mul_nonneg (rpow_nonneg hr.le _) (mul_nonneg (smoothTransition.nonneg _) (m.positive _ hq).le)

/-- Outside a fixed ball the test profile dominates any prescribed height, uniformly in
all small regularization scales. -/
theorem regular_large (ha : 0 < α) (L : ℝ) : ∃ R ≥ (1:ℝ), ∀ r, 0 < r → r ≤ 1 →
    ∀ q : XV d, R ≤ rho q → L ≤ m.regular r q := by
  have hz := m.homogeneous 2 (by norm_num) 0
  simp only [dilate_zero] at hz
  have hzero : m.H 0 = 0 := by nlinarith [one_lt_rpow (by norm_num : 1 < (2:ℝ)) ha]
  obtain ⟨c, C, hc, _, h⟩ := homogeneous_profile_comparison α ha m.H hzero m.smooth m.positive m.homogeneous
  obtain ⟨R,hR⟩ := eventually_atTop.1 ((tendsto_rpow_atTop ha).eventually_ge_atTop (L/c))
  refine ⟨max 1 R,le_max_left _ _,fun r hr hs q hq => ?_⟩
  rw [m.regular_eq hr ((hs.trans (le_max_left _ _)).trans hq)]
  exact (div_le_iff₀' hc).mp (hR _ ((le_max_right _ _).trans hq)) |>.trans (h q).1

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ClassicalProfile
