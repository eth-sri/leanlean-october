/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Smooth cutoffs for the Ward rational function `g(x) = x (x − 1)/(z − x)`

For `z : ℂ` the rational function `bpzG z x = x (x − 1)/(z − x)` has a simple pole at `z` and
vanishes at `0` and `1`. We build smooth compactly supported cutoffs `bpzCutoffSeq z n`, vanishing
near `0`, `1` and `z` and equal to `1` near every fixed point of the regular region `bpzReg z`
once `n` is large, such that the truncations `g χ_n` are smooth with gradient and
difference-quotient bounds governed by the weight `1 + ‖ξ − z‖ ^ (-2)`, uniformly in `n`.

## Construction

Fix the smooth bump `ψ = bpzPsi` on `ℂ` (a `ContDiffBump` with radii `1 < 2`: `ψ = 1` on the unit
disc, `ψ = 0` off the disc of radius `2`, `0 ≤ ψ ≤ 1`). For `m = n + 1`,
`χ_n(x) = (1 − ψ(m (x − z))) (1 − ψ(m x)) (1 − ψ(m (x − 1))) ψ(x / m)`.

Each factor has values in `[0, 1]`, and its gradient is bounded by `2 ‖dψ‖_∞ / d` where `d` is
the distance to its centre, because it is non-constant only where `m d ≤ 2` (resp. `‖x‖ ≤ 2m`).
Hence `‖∇χ_n(ξ)‖ ≲ 1/‖ξ − z‖ + 1/‖ξ‖ + 1/‖ξ − 1‖`, uniformly in `n`; against `g` this is at
most a constant times `1 + ‖ξ − z‖ ^ (-2)`.

## Remarks

* Smoothness is `C^∞`, written `ContDiff ℝ (⊤ : ℕ∞)`. (With `⊤ : WithTop ℕ∞` the statement
  `ContDiff ℝ ⊤ f` means *analyticity* in the current Mathlib, which no nonzero compactly
  supported function on `ℂ` satisfies.)
* None of the estimates needs `z ≠ 0` or `z ≠ 1`; where these hypotheses appear in a statement
  they are kept, as unused `_hz0 _hz1`, for interface uniformity. -/

@[expose] public section
noncomputable section

open Filter Topology

namespace DOZZ.Proofs

variable {z : ℂ}


/-- The rational function of the Ward identity: `g(x) = x (x − 1)/(z − x)`. -/
def bpzG (z x : ℂ) : ℂ := x * (x - 1) / (z - x)

/-- The open region away from `0`, `1`, `z`. -/
def bpzReg (z : ℂ) : Set ℂ := {x | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ z}

/-! ### Elementary real inequalities -/

section
variable {t : ℝ} (ht : 0 ≤ t)
include ht

theorem bpz_rpow_neg_two : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
  rw [Real.rpow_neg ht, Real.rpow_two]

theorem bpz_rpow_neg_two_nonneg : 0 ≤ t ^ (-2 : ℝ) :=
  Real.rpow_nonneg ht _


end
private lemma norm_sub_ge (x y c : ℂ) : ‖x - c‖ - ‖y - x‖ ≤ ‖y - c‖ := by
  linarith [norm_sub_le (y - c) (y - x), show ‖(y - c) - (y - x)‖ = ‖x - c‖ from congrArg norm (by ring)]

private lemma norm_bpzG_le {z ξ : ℂ} (hξ : ξ ≠ z) :
    ‖bpzG z ξ‖ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) * ‖ξ - z‖ := by
  have ht : 0 < ‖ξ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hξ)
  rw [bpzG, norm_div, norm_mul, norm_sub_rev z ξ, bpz_rpow_neg_two ht.le, div_le_iff₀ ht,
    show (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + (‖ξ - z‖ ^ 2)⁻¹) * ‖ξ - z‖ * ‖ξ - z‖ =
      (1 + ‖z‖) * (1 + ‖z - 1‖) * (‖ξ - z‖ ^ 2 + 1) by field_simp]
  have hp : ‖ξ‖ ≤ ‖ξ - z‖ + ‖z‖ := by simpa using norm_add_le (ξ - z) z
  have hq : ‖ξ - 1‖ ≤ ‖ξ - z‖ + ‖z - 1‖ := by simpa using norm_add_le (ξ - z) (z - 1)
  have ha := norm_nonneg z
  have hb := norm_nonneg (z - 1)
  refine (mul_le_mul hp hq (norm_nonneg _) (by positivity)).trans ?_
  linarith [mul_nonneg ha (sq_nonneg (‖ξ - z‖ - 1 / 2)),
    mul_nonneg hb (sq_nonneg (‖ξ - z‖ - 1 / 2)),
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖ξ - z‖)]


/-- Growth of `g` relative to the singular weight. -/
theorem norm_bpzG_div_le (_hz0 : z ≠ 0) (_hz1 : z ≠ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℂ, ξ ≠ z → ξ ≠ 0 → ξ ≠ 1 →
      ‖bpzG z ξ‖ / ‖ξ - z‖ + ‖bpzG z ξ‖ / ‖ξ‖ + ‖bpzG z ξ‖ / ‖ξ - 1‖ ≤
        A * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  have bpzG_div_le_aux {t X K : ℝ} (ht : 0 < t) (h : X * t ≤ K * (t ^ 2 + 1)) : X / t ≤ K * (1 + t ^ (-2 : ℝ)) := by
    rw [bpz_rpow_neg_two ht.le, show K * (1 + (t ^ 2)⁻¹) = K * (t ^ 2 + 1) / t ^ 2 by field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith [div_mul_cancel₀ X ht.ne']
  refine ⟨(1 + ‖z‖) * (1 + ‖z - 1‖) + (1 + ‖z - 1‖) + (1 + ‖z‖), by positivity,
    fun ξ hξz hξ0 hξ1 => ?_⟩
  have ht : 0 < ‖ξ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hξz)
  have h1 : ‖bpzG z ξ‖ / ‖ξ - z‖ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) :=
    (div_le_iff₀ ht).2 (norm_bpzG_le hξz)
  have h2 : ‖bpzG z ξ‖ / ‖ξ‖ ≤ (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
    rw [bpzG, norm_div, norm_mul, norm_sub_rev z ξ, div_right_comm,
      mul_div_cancel_left₀ _ (norm_ne_zero_iff.2 hξ0)]
    refine bpzG_div_le_aux ht ?_
    have hq : ‖ξ - 1‖ ≤ ‖ξ - z‖ + ‖z - 1‖ := by simpa using norm_add_le (ξ - z) (z - 1)
    nlinarith [norm_nonneg (z - 1), sq_nonneg (‖ξ - z‖ - 1 / 2)]
  have h3 : ‖bpzG z ξ‖ / ‖ξ - 1‖ ≤ (1 + ‖z‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
    rw [bpzG, norm_div, norm_mul, norm_sub_rev z ξ, div_right_comm,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hξ1))]
    refine bpzG_div_le_aux ht ?_
    have hp : ‖ξ‖ ≤ ‖ξ - z‖ + ‖z‖ := by simpa using norm_add_le (ξ - z) z
    nlinarith [norm_nonneg z, sq_nonneg (‖ξ - z‖ - 1 / 2)]
  linarith

/-! ### The fixed bump function and its rescalings -/

/-- A fixed smooth bump on `ℂ`: `1` on the closed unit disc and `0` outside the disc of
radius `2`. -/
def bpzBump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The underlying function `ψ` of the fixed bump `bpzBump`. -/
def bpzPsi : ℂ → ℝ := bpzBump

/-- The rescaled and recentred bump `x ↦ ψ (r (x − c))`. -/
def bpzBumpAt (r : ℝ) (c x : ℂ) : ℝ := bpzPsi (r • (x - c))

private lemma bpzBumpAt_bounds (r : ℝ) (c x : ℂ) : 0 ≤ bpzBumpAt r c x ∧ bpzBumpAt r c x ≤ 1 :=
  ⟨bpzBump.nonneg, bpzBump.le_one⟩

section
variable {r : ℝ} {c x : ℂ} (hr : 0 ≤ r)
include c x hr

private lemma bpzBumpAt_eq_one (h : r * ‖x - c‖ ≤ 1) :
    bpzBumpAt r c x = 1 :=
  bpzBump.one_of_mem_closedBall (by simpa [bpzBump, norm_smul, Real.norm_of_nonneg hr] using h)

private lemma bpzBumpAt_eq_zero (h : 2 ≤ r * ‖x - c‖) :
    bpzBumpAt r c x = 0 :=
  bpzBump.zero_of_le_dist (by simpa [bpzBump, norm_smul, Real.norm_of_nonneg hr] using h)


end
private lemma contDiff_bpzBumpAt (r : ℝ) (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (bpzBumpAt r c) :=
  bpzBump.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r)


/-! ### The cutoff -/

/-- The cutoff at scale `m`: the product of the three inner cutoffs `1 - ψ(m (x - c))`, for
`c ∈ {z, 0, 1}`, and the outer cutoff `ψ(x / m)`. -/
def bpzCut (m : ℝ) (z x : ℂ) : ℝ :=
  (1 - bpzBumpAt m z x) * (1 - bpzBumpAt m 0 x) * (1 - bpzBumpAt m 1 x) * bpzBumpAt m⁻¹ 0 x

/-- The cutoff sequence
`χ_n(x) = (1 − ψ(m (x − z))) (1 − ψ(m x)) (1 − ψ(m (x − 1))) ψ(x / m)` with `m = n + 1`. -/
def bpzCutoffSeq (z : ℂ) (n : ℕ) : ℂ → ℝ := bpzCut ((n : ℝ) + 1) z

/-- The cutoffs are nonnegative. -/
theorem bpzCutoffSeq_nonneg (z : ℂ) (n : ℕ) (x : ℂ) : 0 ≤ bpzCutoffSeq z n x := by
  have h (r c) : 0 ≤ 1 - bpzBumpAt r c x := sub_nonneg.2 (bpzBumpAt_bounds r c x).2
  exact mul_nonneg (mul_nonneg (mul_nonneg (h _ _) (h _ _)) (h _ _)) (bpzBumpAt_bounds _ _ _).1

/-- The cutoffs are at most `1`. -/
theorem bpzCutoffSeq_le_one (z : ℂ) (n : ℕ) (x : ℂ) : bpzCutoffSeq z n x ≤ 1 := by
  have h (r c) : 0 ≤ 1 - bpzBumpAt r c x ∧ 1 - bpzBumpAt r c x ≤ 1 :=
    ⟨sub_nonneg.2 (bpzBumpAt_bounds r c x).2, sub_le_self _ (bpzBumpAt_bounds r c x).1⟩
  have b := bpzBumpAt_bounds ((n : ℝ) + 1)⁻¹ 0 x
  have h12 : (1 - bpzBumpAt ((n : ℝ) + 1) z x) * (1 - bpzBumpAt ((n : ℝ) + 1) 0 x) ≤ 1 :=
    (mul_le_of_le_one_left (h _ _).1 (h _ _).2).trans (h _ _).2
  have h123 := (mul_le_of_le_one_left (h ((n : ℝ) + 1) 1).1 h12).trans (h ((n : ℝ) + 1) 1).2
  exact (mul_le_of_le_one_left b.1 h123).trans b.2

private lemma tsupport_bpzCut_sub {m : ℝ} (hm : 0 < m) (z : ℂ) :
    tsupport (bpzCut m z) ⊆
      {x | 1 ≤ m * ‖x - z‖ ∧ 1 ≤ m * ‖x‖ ∧ 1 ≤ m * ‖x - 1‖ ∧ ‖x‖ ≤ 2 * m} := by
  refine closure_minimal (fun x hx => ⟨?_, ?_, ?_, ?_⟩) ?_
  · contrapose! hx; simp [bpzCut, bpzBumpAt_eq_one hm.le hx.le]
  · contrapose! hx; simp [bpzCut, bpzBumpAt_eq_one hm.le (by simpa using hx.le : m * ‖x - 0‖ ≤ 1)]
  · contrapose! hx; simp [bpzCut, bpzBumpAt_eq_one hm.le hx.le]
  · contrapose! hx
    simp [bpzCut, bpzBumpAt_eq_zero (inv_nonneg.2 hm.le)
      (by rw [sub_zero, inv_mul_eq_div, le_div_iff₀ hm]; linarith : 2 ≤ m⁻¹ * ‖x - 0‖)]
  · have hc (c : ℂ) : IsClosed {x : ℂ | 1 ≤ m * ‖x - c‖} := isClosed_le continuous_const (by fun_prop)
    have h0 : IsClosed {x : ℂ | 1 ≤ m * ‖x‖} := by simpa using hc 0
    exact (hc z).inter (h0.inter ((hc 1).inter (isClosed_le continuous_norm continuous_const)))

/-- The cutoffs have compact support. -/
theorem hasCompactSupport_bpzCutoffSeq (z : ℂ) (n : ℕ) : HasCompactSupport (bpzCutoffSeq z n) :=
  (isCompact_closedBall (0 : ℂ) (2 * ((n : ℝ) + 1))).of_isClosed_subset (isClosed_tsupport _)
    fun _ hx => by simpa using (tsupport_bpzCut_sub (Nat.cast_add_one_pos n) z hx).2.2.2

/-- The cutoffs are supported in the region away from `0`, `1`, `z`. -/
theorem tsupport_bpzCutoffSeq_subset (z : ℂ) (n : ℕ) :
    tsupport (bpzCutoffSeq z n) ⊆ bpzReg z := by
  intro x hx
  obtain ⟨h1, h2, h3, -⟩ := tsupport_bpzCut_sub (Nat.cast_add_one_pos n) z hx
  exact ⟨by rintro rfl; norm_num at h2, by rintro rfl; norm_num at h3, by rintro rfl; norm_num at h1⟩

/-- The cutoffs equal `1` near any fixed point of the regular region, for `n` large. -/
theorem bpzCutoffSeq_eventually_eq_one {z x : ℂ} (hx : x ∈ bpzReg z) :
    ∀ᶠ n in atTop, bpzCutoffSeq z n =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨hx0, hx1, hxz⟩ := hx
  let d := min ‖x - z‖ (min ‖x‖ ‖x - 1‖)
  have hd : 0 < d := lt_min (norm_pos_iff.2 (sub_ne_zero.2 hxz))
    (lt_min (norm_pos_iff.2 hx0) (norm_pos_iff.2 (sub_ne_zero.2 hx1)))
  obtain ⟨N, hN⟩ := exists_nat_gt (max (4 / d) (2 * ‖x‖))
  filter_upwards [eventually_ge_atTop N] with n hn
  let m : ℝ := (n : ℝ) + 1
  have hm_max : max (4 / d) (2 * ‖x‖) ≤ m := by
    have : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    dsimp [m]; linarith
  have hm : 0 < m := by positivity
  have hmd : 4 ≤ m * d := by linarith [(div_le_iff₀ hd).1 ((le_max_left _ _).trans hm_max)]
  have hmx : 2 * ‖x‖ ≤ m := (le_max_right _ _).trans hm_max
  filter_upwards [Metric.ball_mem_nhds x (half_pos hd)] with y hy
  have hyx : ‖y - x‖ < d / 2 := by simpa [dist_eq_norm] using hy
  have hfar (c : ℂ) (hdc : d ≤ ‖x - c‖) : bpzBumpAt m c y = 0 :=
    bpzBumpAt_eq_zero hm.le (by nlinarith [norm_sub_ge x y c])
  have hdz : d ≤ ‖x - z‖ := min_le_left _ _
  have hd0 : d ≤ ‖x - 0‖ := by
    rw [sub_zero]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : d ≤ ‖x - 1‖ := (min_le_right _ _).trans (min_le_right _ _)
  have h4 : bpzBumpAt m⁻¹ 0 y = 1 := bpzBumpAt_eq_one (inv_nonneg.2 hm.le) (by
    rw [sub_zero, inv_mul_le_iff₀ hm]
    have : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by simpa using norm_add_le x (y - x)
    rw [sub_zero] at hd0; linarith)
  change bpzCut m z y = 1
  simp [bpzCut, hfar z hdz, hfar 0 hd0, hfar 1 hd1, h4]

/-! ### Gradient of the cutoff and truncated function -/

private lemma contDiffAt_bpzG {z ξ : ℂ} (h : ξ ≠ z) : ContDiffAt ℝ (⊤ : ℕ∞) (bpzG z) ξ :=
  ((contDiffAt_id.mul (contDiffAt_id.sub contDiffAt_const)).div
    (contDiffAt_const.sub contDiffAt_id) (sub_ne_zero.2 h.symm)).restrict_scalars ℝ

private lemma contDiff_bpzCutoffSeq (z : ℂ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bpzCutoffSeq z n) := by
  have h (r c) : ContDiff ℝ (⊤ : ℕ∞) fun x => 1 - bpzBumpAt r c x :=
    contDiff_const.sub (contDiff_bpzBumpAt r c)
  exact (((h _ z).mul (h _ 0)).mul (h _ 1)).mul (contDiff_bpzBumpAt _ 0)

/-- The truncated function. -/
theorem contDiff_bpzG_mul_cutoff (z : ℂ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = z
  · subst hξ
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt (by fun_prop : Continuous fun x => ((n : ℝ) + 1) * ‖x - ξ‖)
      continuous_const).mem_nhds (by simp : ((n : ℝ) + 1) * ‖ξ - ξ‖ < 1)] with x hx
    simp [bpzCutoffSeq, bpzCut, bpzBumpAt_eq_one (Nat.cast_add_one_pos n).le hx.le]
  · exact (contDiffAt_bpzG hξ).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (contDiff_bpzCutoffSeq z n).contDiffAt)


section
variable (_hz0 : z ≠ 0) (_hz1 : z ≠ 1)
include _hz0 _hz1

/-- Uniform gradient bound, singular only at `z`. -/
theorem norm_fderiv_bpzG_mul_cutoff_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (ξ : ℂ), ξ ≠ z →
      ‖fderiv ℝ (fun x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) ξ‖ ≤
        A * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  have norm_fderiv_mul_le {f g : ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hf1 : |f x| ≤ 1) (hg1 : |g x| ≤ 1) : ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ g x‖ := by
    rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, add_comm]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hg1)
      (mul_le_of_le_one_left (norm_nonneg _) hf1)
  have norm_fderiv_bpzBumpAt_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ w, ‖fderiv ℝ bpzPsi w‖ ≤ C) {r : ℝ} (hr : 0 ≤ r) {c x : ℂ} (hx : x ≠ c) : ‖fderiv ℝ (bpzBumpAt r c) x‖ ≤ 2 * C / ‖x - c‖ := by
    have hd : HasFDerivAt (bpzBumpAt r c)
        ((fderiv ℝ bpzPsi (r • (x - c))).comp (r • ContinuousLinearMap.id ℝ ℂ)) x :=
      (((bpzBump.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) _).hasFDerivAt).comp x
        (((hasFDerivAt_id x).sub_const c).const_smul r)
    rw [hd.fderiv]
    by_cases h2 : 2 < r * ‖x - c‖
    · have hev : bpzPsi =ᶠ[𝓝 (r • (x - c))] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
          (by simpa [norm_smul, Real.norm_of_nonneg hr] using h2)] with v hv
        exact bpzBump.zero_of_le_dist (by simpa [bpzBump] using hv.le)
      rw [hev.fderiv_eq]; simp; positivity
    · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul (hC _) (?_ : _ ≤ r) (norm_nonneg _) hC0).trans ?_)
      · rw [norm_smul, Real.norm_of_nonneg hr]
        exact mul_le_of_le_one_right hr ContinuousLinearMap.norm_id_le
      · rw [le_div_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hx))]
        nlinarith [not_lt.1 h2]
  obtain ⟨C, hC⟩ := ((bpzBump.contDiff (n := (⊤ : ℕ∞))).continuous_fderiv
    (by simp)).bounded_above_of_compact_support (bpzBump.hasCompactSupport.fderiv ℝ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨A₂, hA₂0, hA₂⟩ := norm_bpzG_div_le _hz0 _hz1
  let A₁ := 1 + ‖z * (z - 1)‖
  refine ⟨A₁ + 4 * C * A₂, by positivity, fun n ξ hξ => ?_⟩
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 ≤ m := (Nat.cast_add_one_pos n).le
  have hg' : ‖fderiv ℝ (bpzG z) ξ‖ ≤ A₁ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
    have h1 : HasDerivAt (fun y : ℂ => y * (y - 1)) (1 * (ξ - 1) + ξ * 1) ξ :=
      (hasDerivAt_id ξ).mul ((hasDerivAt_id ξ).sub_const 1)
    have h2 : HasDerivAt (fun y : ℂ => z - y) (-1) ξ := (hasDerivAt_id ξ).const_sub z
    have hd : HasDerivAt (bpzG z) (-1 + z * (z - 1) / (z - ξ) ^ 2) ξ :=
      (h1.div h2 (sub_ne_zero.2 hξ.symm)).congr_deriv (by field_simp; ring)
    rw [hd.complexToReal_fderiv.fderiv, norm_smul, norm_one, mul_one]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_one, norm_div, norm_pow, norm_sub_rev z ξ,
      bpz_rpow_neg_two (norm_nonneg _), div_eq_mul_inv]
    dsimp [A₁]
    nlinarith [norm_nonneg (z * (z - 1)), inv_nonneg.2 (sq_nonneg ‖ξ - z‖)]
  have hprod : ‖fderiv ℝ (fun x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) ξ‖ ≤
      ‖fderiv ℝ (bpzG z) ξ‖ + ‖bpzG z ξ‖ * ‖fderiv ℝ (bpzCutoffSeq z n) ξ‖ := by
    have hfun : (fun x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) =
        fun x => bpzCutoffSeq z n x • bpzG z x :=
      funext fun _ => by rw [Complex.real_smul, mul_comm]
    rw [hfun, ((((contDiff_bpzCutoffSeq z n).differentiable (by simp)) ξ).hasFDerivAt.fun_smul
      (((contDiffAt_bpzG hξ).differentiableAt (by simp)).hasFDerivAt)).fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bpzCutoffSeq_nonneg z n ξ),
      ContinuousLinearMap.norm_smulRight_apply, mul_comm ‖fderiv ℝ (bpzCutoffSeq z n) ξ‖]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (bpzCutoffSeq_le_one z n ξ)) le_rfl
  by_cases h01 : ξ = 0 ∨ ξ = 1
  · have hg0 : bpzG z ξ = 0 := by rcases h01 with rfl | rfl <;> simp [bpzG]
    rw [hg0, norm_zero, zero_mul, add_zero] at hprod
    have : 0 ≤ 4 * C * A₂ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by positivity
    linarith
  · push Not at h01
    obtain ⟨h0, h1'⟩ := h01
    have hB (r c) : DifferentiableAt ℝ (bpzBumpAt r c) ξ :=
      ((contDiff_bpzBumpAt r c).differentiable (by simp)) ξ
    have hF (r c) : DifferentiableAt ℝ (fun y => 1 - bpzBumpAt r c y) ξ := (hB r c).const_sub 1
    have h1b (r c) : |1 - bpzBumpAt r c ξ| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.2 (bpzBumpAt_bounds r c ξ).2)]
      linarith [(bpzBumpAt_bounds r c ξ).1]
    have v12 : |(1 - bpzBumpAt m z ξ) * (1 - bpzBumpAt m 0 ξ)| ≤ 1 := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (h1b _ _)).trans (h1b _ _)
    have v123 : |(1 - bpzBumpAt m z ξ) * (1 - bpzBumpAt m 0 ξ) * (1 - bpzBumpAt m 1 ξ)| ≤ 1 := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) v12).trans (h1b _ _)
    have v4 : |bpzBumpAt m⁻¹ 0 ξ| ≤ 1 := by
      rw [abs_of_nonneg (bpzBumpAt_bounds _ _ _).1]; exact (bpzBumpAt_bounds _ _ _).2
    have hcut : ‖fderiv ℝ (bpzCutoffSeq z n) ξ‖ ≤
        2 * C * (1 / ‖ξ - z‖ + 2 / ‖ξ‖ + 1 / ‖ξ - 1‖) := by
      change ‖fderiv ℝ (bpzCut m z) ξ‖ ≤ _
      refine (norm_fderiv_mul_le (((hF m z).mul (hF m 0)).mul (hF m 1)) (hB m⁻¹ 0) v123 v4).trans ?_
      refine (add_le_add (norm_fderiv_mul_le ((hF m z).mul (hF m 0)) (hF m 1) v12 (h1b _ _)) le_rfl).trans ?_
      refine (add_le_add (add_le_add (norm_fderiv_mul_le (hF m z) (hF m 0) (h1b _ _) (h1b _ _)) le_rfl) le_rfl).trans ?_
      simp only [fderiv_const_sub, norm_neg]
      have b1 := norm_fderiv_bpzBumpAt_le hC0 hC hm hξ
      have b2 : ‖fderiv ℝ (bpzBumpAt m 0) ξ‖ ≤ 2 * C / ‖ξ‖ := by
        simpa using norm_fderiv_bpzBumpAt_le hC0 hC hm h0
      have b3 := norm_fderiv_bpzBumpAt_le hC0 hC hm h1'
      have b4 : ‖fderiv ℝ (bpzBumpAt m⁻¹ 0) ξ‖ ≤ 2 * C / ‖ξ‖ := by
        simpa using norm_fderiv_bpzBumpAt_le hC0 hC (inv_nonneg.2 hm) h0
      exact (add_le_add (add_le_add (add_le_add b1 b2) b3) b4).trans_eq (by ring)
    have hmul := mul_le_mul_of_nonneg_left hcut (norm_nonneg (bpzG z ξ))
    have hdiv := hA₂ ξ hξ h0 h1'
    have : 0 ≤ ‖bpzG z ξ‖ / ‖ξ - z‖ := by positivity
    have : 0 ≤ ‖bpzG z ξ‖ / ‖ξ - 1‖ := by positivity
    have : 0 ≤ ‖bpzG z ξ‖ / ‖ξ‖ := by positivity
    have hle2 : ‖bpzG z ξ‖ / ‖ξ - z‖ + 2 * (‖bpzG z ξ‖ / ‖ξ‖) + ‖bpzG z ξ‖ / ‖ξ - 1‖ ≤
        2 * (A₂ * (1 + ‖ξ - z‖ ^ (-2 : ℝ))) := by linarith
    have hmul2 := (hmul.trans_eq (by ring)).trans (mul_le_mul_of_nonneg_left hle2 (by positivity : 0 ≤ 2 * C))
    linarith

/-- Uniform difference-quotient bound. -/
theorem norm_bpzG_mul_cutoff_sub_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (x y : ℂ), x ≠ z → y ≠ z →
      ‖bpzG z x * (bpzCutoffSeq z n x : ℂ) - bpzG z y * (bpzCutoffSeq z n y : ℂ)‖ ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) * ‖x - y‖ := by
  obtain ⟨A₂, hA₂0, hA₂⟩ := norm_fderiv_bpzG_mul_cutoff_le _hz0 _hz1
  let K := (1 + ‖z‖) * (1 + ‖z - 1‖)
  have hK0 : 0 ≤ K := by positivity
  refine ⟨4 * A₂ + 4 * K, by positivity, fun n x y hx hy => ?_⟩
  let H : ℂ → ℂ := fun w => bpzG z w * (bpzCutoffSeq z n w : ℂ)
  have hH : Differentiable ℝ H := (contDiff_bpzG_mul_cutoff z n).differentiable (by simp)
  have hnear {u v : ℂ} (hu : u ≠ z) (huv : ‖u - v‖ ≤ ‖u - z‖ / 2) :
      ‖H u - H v‖ ≤ 4 * A₂ * (1 + ‖u - z‖ ^ (-2 : ℝ)) * ‖u - v‖ := by
    have ht : 0 < ‖u - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
    have hbd : ∀ w ∈ Metric.closedBall u (‖u - z‖ / 2),
        ‖fderiv ℝ H w‖ ≤ A₂ * (1 + 4 * ‖u - z‖ ^ (-2 : ℝ)) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have hwz : ‖u - z‖ / 2 ≤ ‖w - z‖ := by linarith [norm_sub_ge u w z]
      have hw0 : w ≠ z := by rintro rfl; simp at hwz; linarith
      refine (hA₂ n w hw0).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hA₂0)
      have hs0 : 0 < ‖w - z‖ := by linarith
      rw [bpz_rpow_neg_two hs0.le, bpz_rpow_neg_two ht.le]
      exact (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hwz 2)).trans_eq (by field_simp; norm_num)
    rw [norm_sub_rev (H u), ← norm_sub_rev v u]
    refine ((convex_closedBall u _).norm_image_sub_le_of_norm_fderiv_le (fun w _ => hH w) hbd
      (Metric.mem_closedBall_self (by positivity))
      (by rwa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev])).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have sx := bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))
  have sy := bpz_rpow_neg_two_nonneg (norm_nonneg (y - z))
  by_cases h1 : ‖x - y‖ ≤ ‖x - z‖ / 2
  · exact (hnear hx h1).trans (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))
  by_cases h2 : ‖y - x‖ ≤ ‖y - z‖ / 2
  · have h := hnear hy h2
    rw [norm_sub_rev (H y), norm_sub_rev y x] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _))
  · have h1' : ‖x - z‖ ≤ 2 * ‖x - y‖ := by linarith [not_le.1 h1]
    have h2' : ‖y - z‖ ≤ 2 * ‖x - y‖ := by have := not_le.1 h2; rw [norm_sub_rev y x] at this; linarith
    have hHG (w : ℂ) (hw : w ≠ z) : ‖H w‖ ≤ K * (1 + ‖w - z‖ ^ (-2 : ℝ)) * ‖w - z‖ := by
      refine (show ‖H w‖ ≤ ‖bpzG z w‖ by
        dsimp [H]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bpzCutoffSeq_nonneg z n w)]
        exact mul_le_of_le_one_right (norm_nonneg _) (bpzCutoffSeq_le_one z n w)).trans
        (norm_bpzG_le hw)
    refine (norm_sub_le (H x) (H y)).trans ((add_le_add (hHG x hx) (hHG y hy)).trans ?_)
    have hx' := mul_le_mul_of_nonneg_left h1' (by positivity : 0 ≤ K * (1 + ‖x - z‖ ^ (-2 : ℝ)))
    have hy' := mul_le_mul_of_nonneg_left h2' (by positivity : 0 ≤ K * (1 + ‖y - z‖ ^ (-2 : ℝ)))
    refine (add_le_add hx' hy').trans ?_
    rw [show K * (1 + ‖x - z‖ ^ (-2 : ℝ)) * (2 * ‖x - y‖) + K * (1 + ‖y - z‖ ^ (-2 : ℝ)) * (2 * ‖x - y‖) =
      (2 * K * (1 + ‖x - z‖ ^ (-2 : ℝ)) + 2 * K * (1 + ‖y - z‖ ^ (-2 : ℝ))) * ‖x - y‖ by ring]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)


end
end DOZZ.Proofs
