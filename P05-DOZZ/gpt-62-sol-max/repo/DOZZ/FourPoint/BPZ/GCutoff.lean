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

open Filter Topology

namespace DOZZ.Proofs

/-- The rational function of the Ward identity: `g(x) = x (x − 1)/(z − x)`. -/
noncomputable def bpzG (z x : ℂ) : ℂ := x * (x - 1) / (z - x)

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

theorem bpz_rpow_neg_two_le_four_mul {t s : ℝ} (ht : 0 < t) (hs : t / 2 ≤ s) :
    s ^ (-2 : ℝ) ≤ 4 * t ^ (-2 : ℝ) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  rw [bpz_rpow_neg_two hs0.le, bpz_rpow_neg_two ht.le]
  have h1 : (t / 2) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have h2 : (s ^ 2)⁻¹ ≤ ((t / 2) ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
  calc (s ^ 2)⁻¹ ≤ ((t / 2) ^ 2)⁻¹ := h2
    _ = 4 * (t ^ 2)⁻¹ := by
        field_simp
        norm_num

/-- Comparison of `X` with the singular weight `1 + t ^ (-2)`, in polynomial form. -/
theorem bpz_le_mul_one_add_rpow {t X K : ℝ} (ht : 0 < t) (h : X * t ^ 2 ≤ K * (t ^ 2 + 1)) :
    X ≤ K * (1 + t ^ (-2 : ℝ)) := by
  rw [bpz_rpow_neg_two ht.le]
  have h2 : 0 < t ^ 2 := by positivity
  have e : K * (1 + (t ^ 2)⁻¹) = K * (t ^ 2 + 1) / t ^ 2 := by field_simp
  rw [e, le_div_iff₀ h2]
  exact h

theorem bpz_norm_sub_ge (x y c : ℂ) : ‖x - c‖ - ‖y - x‖ ≤ ‖y - c‖ := by
  calc ‖x - c‖ - ‖y - x‖ = ‖(y - c) - (y - x)‖ - ‖y - x‖ := by congr 2; ring
    _ ≤ ‖y - c‖ := by linarith [norm_sub_le (y - c) (y - x)]

theorem bpz_norm_le_add (z ξ : ℂ) : ‖ξ‖ ≤ ‖ξ - z‖ + ‖z‖ := by
  calc ‖ξ‖ = ‖(ξ - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖ξ - z‖ + ‖z‖ := norm_add_le _ _

theorem bpz_norm_sub_one_le_add (z ξ : ℂ) : ‖ξ - 1‖ ≤ ‖ξ - z‖ + ‖z - 1‖ := by
  calc ‖ξ - 1‖ = ‖(ξ - z) + (z - 1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖ξ - z‖ + ‖z - 1‖ := norm_add_le _ _

/-! ### Estimates for `g` -/

theorem bpzG_zero (z : ℂ) : bpzG z 0 = 0 := by simp [bpzG]

theorem bpzG_one (z : ℂ) : bpzG z 1 = 0 := by simp [bpzG]

theorem norm_bpzG_eq (z ξ : ℂ) : ‖bpzG z ξ‖ = ‖ξ‖ * ‖ξ - 1‖ / ‖ξ - z‖ := by
  rw [bpzG, norm_div, norm_mul, norm_sub_rev z ξ]

/-- `g(x) = −(x + z − 1) + z (z − 1)/(z − x)` has complex derivative `−1 + z (z − 1)/(z − x)²`. -/
theorem hasDerivAt_bpzG {z x : ℂ} (h : x ≠ z) :
    HasDerivAt (bpzG z) (-1 + z * (z - 1) / (z - x) ^ 2) x := by
  have hd : z - x ≠ 0 := sub_ne_zero.2 h.symm
  have h1 : HasDerivAt (fun y : ℂ => y * (y - 1)) (1 * (x - 1) + x * 1) x :=
    (hasDerivAt_id x).mul ((hasDerivAt_id x).sub_const 1)
  have h2 : HasDerivAt (fun y : ℂ => z - y) (-1) x := (hasDerivAt_id x).const_sub z
  refine (h1.div h2 hd).congr_deriv ?_
  field_simp
  ring

theorem contDiffAt_bpzG {z ξ : ℂ} (h : ξ ≠ z) {n : WithTop ℕ∞} : ContDiffAt ℝ n (bpzG z) ξ := by
  have h1 : ContDiffAt ℂ n (fun x : ℂ => x * (x - 1)) ξ :=
    contDiffAt_id.mul (contDiffAt_id.sub contDiffAt_const)
  have h2 : ContDiffAt ℂ n (fun x : ℂ => z - x) ξ := contDiffAt_const.sub contDiffAt_id
  exact (h1.div h2 (sub_ne_zero.2 h.symm)).restrict_scalars ℝ

theorem norm_fderiv_bpzG_le_aux {z x : ℂ} (h : x ≠ z) :
    ‖fderiv ℝ (bpzG z) x‖ ≤ 1 + ‖z * (z - 1)‖ * ‖x - z‖ ^ (-2 : ℝ) := by
  rw [(hasDerivAt_bpzG h).complexToReal_fderiv.fderiv, norm_smul, norm_one, mul_one]
  calc ‖-1 + z * (z - 1) / (z - x) ^ 2‖ ≤ ‖(-1 : ℂ)‖ + ‖z * (z - 1) / (z - x) ^ 2‖ :=
        norm_add_le _ _
    _ = 1 + ‖z * (z - 1)‖ * ‖x - z‖ ^ (-2 : ℝ) := by
      rw [norm_neg, norm_one, norm_div, norm_pow, norm_sub_rev z x,
        bpz_rpow_neg_two (norm_nonneg _), div_eq_mul_inv]

theorem bpz_exists_norm_fderiv_bpzG_le (z : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℂ, ξ ≠ z → ‖fderiv ℝ (bpzG z) ξ‖ ≤ A * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  refine ⟨1 + ‖z * (z - 1)‖, by positivity, fun ξ hξ => ?_⟩
  have h := norm_fderiv_bpzG_le_aux hξ
  have hs : 0 ≤ ‖ξ - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  linarith [norm_nonneg (z * (z - 1)), mul_nonneg (norm_nonneg (z * (z - 1))) hs]

theorem bpz_mul_norm_le (z ξ : ℂ) :
    ‖ξ‖ * ‖ξ - 1‖ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (‖ξ - z‖ ^ 2 + 1) := by
  have hp := bpz_norm_le_add z ξ
  have hq := bpz_norm_sub_one_le_add z ξ
  have ht : 0 ≤ ‖ξ - z‖ := norm_nonneg _
  have ha : 0 ≤ ‖z‖ := norm_nonneg _
  have hb : 0 ≤ ‖z - 1‖ := norm_nonneg _
  calc ‖ξ‖ * ‖ξ - 1‖ ≤ (‖ξ - z‖ + ‖z‖) * (‖ξ - z‖ + ‖z - 1‖) :=
        mul_le_mul hp hq (norm_nonneg _) (by positivity)
    _ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (‖ξ - z‖ ^ 2 + 1) := by
        linarith [mul_nonneg ha (sq_nonneg (‖ξ - z‖ - 1 / 2)),
          mul_nonneg hb (sq_nonneg (‖ξ - z‖ - 1 / 2)),
          mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖ξ - z‖)]

/-- Growth of `g` relative to the distance to `z`; there are no exceptional points. -/
theorem norm_bpzG_le {z ξ : ℂ} (hξ : ξ ≠ z) :
    ‖bpzG z ξ‖ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) * ‖ξ - z‖ := by
  have ht : 0 < ‖ξ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hξ)
  have h := bpz_mul_norm_le z ξ
  rw [bpz_rpow_neg_two ht.le, norm_bpzG_eq, div_le_iff₀ ht]
  have e : (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + (‖ξ - z‖ ^ 2)⁻¹) * ‖ξ - z‖ * ‖ξ - z‖ =
      (1 + ‖z‖) * (1 + ‖z - 1‖) * (‖ξ - z‖ ^ 2 + 1) := by
    field_simp
  rw [e]
  exact h

private theorem bpz_div_le_weight {a t b : ℝ} (ht : 0 < t) (hb : 0 ≤ b) (ha : a ≤ t + b) :
    a / t ≤ (1 + b) * (1 + t ^ (-2 : ℝ)) := by
  apply bpz_le_mul_one_add_rpow ht
  have he : a / t * t ^ 2 = a * t := by field_simp
  rw [he]
  linarith [mul_le_mul_of_nonneg_right ha ht.le, mul_nonneg hb (sq_nonneg (t - 1 / 2))]

section
variable (z ξ : ℂ) (hξz : ξ ≠ z)
include hξz

/-- `‖g ξ‖ / ‖ξ‖ = ‖ξ - 1‖ / ‖ξ - z‖` against the singular weight. -/
theorem bpzG_div_norm_le (hξ0 : ξ ≠ 0) :
    ‖bpzG z ξ‖ / ‖ξ‖ ≤ (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  rw [norm_bpzG_eq, mul_div_assoc, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hξ0)]
  exact bpz_div_le_weight (norm_pos_iff.mpr (sub_ne_zero.mpr hξz)) (norm_nonneg _)
    (bpz_norm_sub_one_le_add z ξ)

/-- `‖g ξ‖ / ‖ξ - 1‖ = ‖ξ‖ / ‖ξ - z‖` against the singular weight. -/
theorem bpzG_div_norm_sub_one_le (hξ1 : ξ ≠ 1) :
    ‖bpzG z ξ‖ / ‖ξ - 1‖ ≤ (1 + ‖z‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  rw [norm_bpzG_eq, mul_comm ‖ξ‖, mul_div_assoc,
    mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hξ1))]
  exact bpz_div_le_weight (norm_pos_iff.mpr (sub_ne_zero.mpr hξz)) (norm_nonneg _)
    (bpz_norm_le_add z ξ)

end

theorem bpz_exists_norm_bpzG_div_le (z : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℂ, ξ ≠ z → ξ ≠ 0 → ξ ≠ 1 →
      ‖bpzG z ξ‖ / ‖ξ - z‖ + ‖bpzG z ξ‖ / ‖ξ‖ + ‖bpzG z ξ‖ / ‖ξ - 1‖ ≤
        A * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  refine ⟨(1 + ‖z‖) * (1 + ‖z - 1‖) + (1 + ‖z - 1‖) + (1 + ‖z‖), by positivity,
    fun ξ hξz hξ0 hξ1 => ?_⟩
  have ht : 0 < ‖ξ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hξz)
  have h1 : ‖bpzG z ξ‖ / ‖ξ - z‖ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
    rw [div_le_iff₀ ht]
    exact norm_bpzG_le hξz
  have h2 := bpzG_div_norm_le z ξ hξz hξ0
  have h3 := bpzG_div_norm_sub_one_le z ξ hξz hξ1
  calc _ ≤ (1 + ‖z‖) * (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) +
        (1 + ‖z - 1‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) + (1 + ‖z‖) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) :=
        add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

theorem bpz_exists_norm_bpzG_le (z : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ ξ : ℂ, ξ ≠ z → ‖bpzG z ξ‖ ≤ K * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) * ‖ξ - z‖ :=
  ⟨(1 + ‖z‖) * (1 + ‖z - 1‖), by positivity, fun _ hξ => norm_bpzG_le hξ⟩

/-! ### The fixed bump function and its rescalings -/

/-- A fixed smooth bump on `ℂ`: `1` on the closed unit disc and `0` outside the disc of
radius `2`. -/
noncomputable def bpzBump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The underlying function `ψ` of the fixed bump `bpzBump`. -/
noncomputable def bpzPsi : ℂ → ℝ := bpzBump

theorem contDiff_bpzPsi : ContDiff ℝ (⊤ : ℕ∞) bpzPsi := bpzBump.contDiff

theorem bpzPsi_nonneg (w : ℂ) : 0 ≤ bpzPsi w := bpzBump.nonneg

theorem bpzPsi_le_one (w : ℂ) : bpzPsi w ≤ 1 := bpzBump.le_one

theorem bpzPsi_eq_one {w : ℂ} (h : ‖w‖ ≤ 1) : bpzPsi w = 1 :=
  bpzBump.one_of_mem_closedBall (by simpa [bpzBump] using h)

theorem bpzPsi_eq_zero {w : ℂ} (h : 2 ≤ ‖w‖) : bpzPsi w = 0 :=
  bpzBump.zero_of_le_dist (by simpa [bpzBump] using h)

theorem hasCompactSupport_bpzPsi : HasCompactSupport bpzPsi := bpzBump.hasCompactSupport

theorem fderiv_bpzPsi_eq_zero {w : ℂ} (h : 2 < ‖w‖) : fderiv ℝ bpzPsi w = 0 := by
  have hev : bpzPsi =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
    have hmem : {v : ℂ | 2 < ‖v‖} ∈ 𝓝 w :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds h
    filter_upwards [hmem] with v hv using bpzPsi_eq_zero hv.le
  rw [hev.fderiv_eq]
  simp

theorem exists_norm_fderiv_bpzPsi_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖fderiv ℝ bpzPsi w‖ ≤ C := by
  obtain ⟨C, hC⟩ := (contDiff_bpzPsi.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hasCompactSupport_bpzPsi.fderiv ℝ)
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

/-- The rescaled and recentred bump `x ↦ ψ (r (x − c))`. -/
noncomputable def bpzBumpAt (r : ℝ) (c x : ℂ) : ℝ := bpzPsi (r • (x - c))

theorem contDiff_bpzBumpAt (r : ℝ) (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (bpzBumpAt r c) :=
  contDiff_bpzPsi.comp ((contDiff_id.sub contDiff_const).const_smul r)

section
variable (r : ℝ) (c x : ℂ)

theorem bpzBumpAt_nonneg : 0 ≤ bpzBumpAt r c x := bpzPsi_nonneg _

theorem bpzBumpAt_le_one : bpzBumpAt r c x ≤ 1 := bpzPsi_le_one _

end

section
variable {r : ℝ} {c x : ℂ} (hr : 0 ≤ r)
include hr

theorem bpzBumpAt_eq_one (h : r * ‖x - c‖ ≤ 1) :
    bpzBumpAt r c x = 1 := by
  apply bpzPsi_eq_one
  rwa [norm_smul, Real.norm_of_nonneg hr]

theorem bpzBumpAt_eq_zero (h : 2 ≤ r * ‖x - c‖) :
    bpzBumpAt r c x = 0 := by
  apply bpzPsi_eq_zero
  rwa [norm_smul, Real.norm_of_nonneg hr]

end

theorem hasFDerivAt_bpzBumpAt (r : ℝ) (c x : ℂ) :
    HasFDerivAt (bpzBumpAt r c)
      ((fderiv ℝ bpzPsi (r • (x - c))).comp (r • ContinuousLinearMap.id ℝ ℂ)) x := by
  have h1 : HasFDerivAt (fun y : ℂ => r • (y - c)) (r • ContinuousLinearMap.id ℝ ℂ) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul r
  have h2 : HasFDerivAt bpzPsi (fderiv ℝ bpzPsi (r • (x - c))) (r • (x - c)) :=
    ((contDiff_bpzPsi.differentiable (by simp)) _).hasFDerivAt
  exact h2.comp x h1

/-- The gradient of a rescaled bump is controlled by the inverse distance to its centre. -/
theorem norm_fderiv_bpzBumpAt_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ w, ‖fderiv ℝ bpzPsi w‖ ≤ C)
    {r : ℝ} (hr : 0 ≤ r) {c x : ℂ} (hx : x ≠ c) :
    ‖fderiv ℝ (bpzBumpAt r c) x‖ ≤ 2 * C / ‖x - c‖ := by
  have ht : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [(hasFDerivAt_bpzBumpAt r c x).fderiv]
  by_cases h2 : 2 < r * ‖x - c‖
  · have h0 : fderiv ℝ bpzPsi (r • (x - c)) = 0 :=
      fderiv_bpzPsi_eq_zero (by rwa [norm_smul, Real.norm_of_nonneg hr])
    rw [h0]
    simp only [ContinuousLinearMap.zero_comp, norm_zero]
    positivity
  · have h2' : r * ‖x - c‖ ≤ 2 := not_lt.1 h2
    calc ‖(fderiv ℝ bpzPsi (r • (x - c))).comp (r • ContinuousLinearMap.id ℝ ℂ)‖
        ≤ ‖fderiv ℝ bpzPsi (r • (x - c))‖ * ‖r • ContinuousLinearMap.id ℝ ℂ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * r := by
          refine mul_le_mul (hC _) ?_ (norm_nonneg _) hC0
          calc ‖r • ContinuousLinearMap.id ℝ ℂ‖ = ‖r‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ :=
                norm_smul _ _
            _ ≤ r := by
                rw [Real.norm_of_nonneg hr]
                exact mul_le_of_le_one_right hr (ContinuousLinearMap.norm_id_le)
      _ ≤ 2 * C / ‖x - c‖ := by
          rw [le_div_iff₀ ht]
          linarith only [mul_le_mul_of_nonneg_left h2' hC0]

/-! ### The cutoff -/

/-- The cutoff at scale `m`: the product of the three inner cutoffs `1 - ψ(m (x - c))`, for
`c ∈ {z, 0, 1}`, and the outer cutoff `ψ(x / m)`. -/
noncomputable def bpzCut (m : ℝ) (z x : ℂ) : ℝ :=
  (1 - bpzBumpAt m z x) * (1 - bpzBumpAt m 0 x) * (1 - bpzBumpAt m 1 x) * bpzBumpAt m⁻¹ 0 x

private noncomputable def bpzCutFactors (m : ℝ) (z : ℂ) : Fin 4 → ℂ → ℝ :=
  ![fun x => 1 - bpzBumpAt m z x, fun x => 1 - bpzBumpAt m 0 x,
    fun x => 1 - bpzBumpAt m 1 x, bpzBumpAt m⁻¹ 0]

private theorem bpzCut_eq_prod (m : ℝ) (z : ℂ) :
    bpzCut m z = fun x => ∏ i, bpzCutFactors m z i x := by
  ext x
  simp [bpzCut, bpzCutFactors, Fin.prod_univ_succ, mul_assoc]

private theorem bpzCutFactors_mem_Icc (m : ℝ) (z x : ℂ) (i : Fin 4) :
    bpzCutFactors m z i x ∈ Set.Icc 0 1 := by
  have h (r : ℝ) (c : ℂ) : 1 - bpzBumpAt r c x ∈ Set.Icc 0 1 :=
    ⟨sub_nonneg.mpr (bpzBumpAt_le_one r c x),
      sub_le_self _ (bpzBumpAt_nonneg r c x)⟩
  fin_cases i <;> simp only [bpzCutFactors, Fin.isValue, Fin.reduceFinMk,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals first | exact h .. | exact ⟨bpzBumpAt_nonneg .., bpzBumpAt_le_one ..⟩

private theorem contDiff_bpzCutFactors (m : ℝ) (z : ℂ) (i : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (bpzCutFactors m z i) := by
  have h (r : ℝ) (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun x => 1 - bpzBumpAt r c x) :=
    contDiff_const.sub (contDiff_bpzBumpAt r c)
  fin_cases i <;> first | exact h .. | exact contDiff_bpzBumpAt .. 

/-- The cutoff sequence
`χ_n(x) = (1 − ψ(m (x − z))) (1 − ψ(m x)) (1 − ψ(m (x − 1))) ψ(x / m)` with `m = n + 1`. -/
noncomputable def bpzCutoffSeq (z : ℂ) (n : ℕ) : ℂ → ℝ := bpzCut ((n : ℝ) + 1) z

theorem contDiff_bpzCut (m : ℝ) (z : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (bpzCut m z) := by
  rw [bpzCut_eq_prod]
  exact contDiff_prod fun i _ => contDiff_bpzCutFactors m z i

section
variable (m : ℝ) (z x : ℂ)

theorem bpzCut_nonneg : 0 ≤ bpzCut m z x := by
  rw [bpzCut_eq_prod]
  exact Finset.prod_nonneg fun i _ => (bpzCutFactors_mem_Icc m z x i).1

theorem bpzCut_le_one : bpzCut m z x ≤ 1 := by
  rw [bpzCut_eq_prod]
  exact Finset.prod_le_one₀ (fun i _ => (bpzCutFactors_mem_Icc m z x i).1)
    (fun i _ => (bpzCutFactors_mem_Icc m z x i).2)

end

section
variable {m : ℝ} (hm : 0 ≤ m) {z x : ℂ}
include hm

theorem bpzCut_eq_zero_of_le_z (h : m * ‖x - z‖ ≤ 1) :
    bpzCut m z x = 0 := by
  simp [bpzCut, bpzBumpAt_eq_one hm h]

theorem bpzCut_eq_zero_of_le_zero (h : m * ‖x‖ ≤ 1) :
    bpzCut m z x = 0 := by
  have h' : m * ‖x - 0‖ ≤ 1 := by simpa using h
  simp [bpzCut, bpzBumpAt_eq_one hm h']

theorem bpzCut_eq_zero_of_le_one (h : m * ‖x - 1‖ ≤ 1) :
    bpzCut m z x = 0 := by
  simp [bpzCut, bpzBumpAt_eq_one hm h]

end

section
variable {m : ℝ} (hm : 0 < m)
include hm

theorem bpzCut_eq_zero_of_ge {z x : ℂ} (h : 2 * m ≤ ‖x‖) :
    bpzCut m z x = 0 := by
  have h' : 2 ≤ m⁻¹ * ‖x - 0‖ := by
    rw [sub_zero, inv_mul_eq_div, le_div_iff₀ hm]
    linarith
  simp [bpzCut, bpzBumpAt_eq_zero (inv_nonneg.2 hm.le) h']

theorem bpzCut_eq_one_of_far {z x : ℂ} (h1 : 2 ≤ m * ‖x - z‖)
    (h2 : 2 ≤ m * ‖x‖) (h3 : 2 ≤ m * ‖x - 1‖) (h4 : ‖x‖ ≤ m) : bpzCut m z x = 1 := by
  have e2 : bpzBumpAt m 0 x = 0 := bpzBumpAt_eq_zero hm.le (by simpa using h2)
  have e4 : bpzBumpAt m⁻¹ 0 x = 1 :=
    bpzBumpAt_eq_one (inv_nonneg.2 hm.le) (by rw [sub_zero, inv_mul_le_iff₀ hm]; linarith)
  simp [bpzCut, bpzBumpAt_eq_zero hm.le h1, e2, bpzBumpAt_eq_zero hm.le h3, e4]

theorem bpzCut_support_subset (z : ℂ) :
    Function.support (bpzCut m z) ⊆
      {x | 1 ≤ m * ‖x - z‖ ∧ 1 ≤ m * ‖x‖ ∧ 1 ≤ m * ‖x - 1‖ ∧ ‖x‖ ≤ 2 * m} := by
  intro x hx
  have hx' : bpzCut m z x ≠ 0 := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    exact hx' (bpzCut_eq_zero_of_le_z hm.le (not_le.1 h).le)
  · by_contra h
    exact hx' (bpzCut_eq_zero_of_le_zero hm.le (not_le.1 h).le)
  · by_contra h
    exact hx' (bpzCut_eq_zero_of_le_one hm.le (not_le.1 h).le)
  · by_contra h
    exact hx' (bpzCut_eq_zero_of_ge hm (not_le.1 h).le)

end

theorem isClosed_bpzCutSet (m : ℝ) (z : ℂ) :
    IsClosed {x : ℂ | 1 ≤ m * ‖x - z‖ ∧ 1 ≤ m * ‖x‖ ∧ 1 ≤ m * ‖x - 1‖ ∧ ‖x‖ ≤ 2 * m} := by
  have h1 : IsClosed {x : ℂ | 1 ≤ m * ‖x - z‖} := isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {x : ℂ | 1 ≤ m * ‖x‖} := isClosed_le continuous_const (by fun_prop)
  have h3 : IsClosed {x : ℂ | 1 ≤ m * ‖x - 1‖} := isClosed_le continuous_const (by fun_prop)
  have h4 : IsClosed {x : ℂ | ‖x‖ ≤ 2 * m} := isClosed_le (by fun_prop) continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

section
variable {m : ℝ} (hm : 0 < m) (z : ℂ)
include hm

theorem tsupport_bpzCut_subset :
    tsupport (bpzCut m z) ⊆
      {x | 1 ≤ m * ‖x - z‖ ∧ 1 ≤ m * ‖x‖ ∧ 1 ≤ m * ‖x - 1‖ ∧ ‖x‖ ≤ 2 * m} :=
  closure_minimal (bpzCut_support_subset hm z) (isClosed_bpzCutSet m z)

theorem tsupport_bpzCut_subset_reg :
    tsupport (bpzCut m z) ⊆ bpzReg z := by
  intro x hx
  obtain ⟨h1, h2, h3, -⟩ := tsupport_bpzCut_subset hm z hx
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    norm_num at h2
  · rintro rfl
    norm_num at h3
  · rintro rfl
    norm_num at h1

theorem hasCompactSupport_bpzCut : HasCompactSupport (bpzCut m z) :=
  (isCompact_closedBall (0 : ℂ) (2 * m)).of_isClosed_subset (isClosed_tsupport _) fun x hx => by
    simpa using (tsupport_bpzCut_subset hm z hx).2.2.2

end

theorem bpzCut_eventuallyEq_one {z x : ℂ} (hx : x ∈ bpzReg z) :
    ∃ R : ℝ, ∀ m : ℝ, R ≤ m → bpzCut m z =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨hx0, hx1, hxz⟩ := hx
  have hz' : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  have h0' : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h1' : 0 < ‖x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hx1)
  obtain ⟨d, hdpos, hdz, hd0, hd1⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ ‖x - z‖ ∧ d ≤ ‖x‖ ∧ d ≤ ‖x - 1‖ :=
    ⟨min ‖x - z‖ (min ‖x‖ ‖x - 1‖), lt_min hz' (lt_min h0' h1'), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨max (4 / d) (2 * ‖x‖), fun m hm => ?_⟩
  have hm1 : 4 / d ≤ m := (le_max_left _ _).trans hm
  have hm2 : 2 * ‖x‖ ≤ m := (le_max_right _ _).trans hm
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hmd : 4 ≤ m * d := by
    have := (div_le_iff₀ hdpos).1 hm1
    linarith
  filter_upwards [Metric.ball_mem_nhds x (half_pos hdpos)] with y hy
  have hyx : ‖y - x‖ < d / 2 := by simpa [dist_eq_norm] using hy
  have hnear (c : ℂ) (hc : d ≤ ‖x - c‖) : 2 ≤ m * ‖y - c‖ := by
    have := bpz_norm_sub_ge x y c
    have hle : d / 2 ≤ ‖y - c‖ := by linarith
    linarith [mul_le_mul_of_nonneg_left hle hmpos.le]
  refine bpzCut_eq_one_of_far hmpos (hnear z hdz) (by simpa using hnear 0 (by simpa using hd0))
    (hnear 1 hd1) ?_
  linarith [bpz_norm_le_add x y]

section
variable (z : ℂ) (n : ℕ)

/-- The cutoffs are nonnegative. -/
theorem bpzCutoffSeq_nonneg (x : ℂ) : 0 ≤ bpzCutoffSeq z n x :=
  bpzCut_nonneg _ z x

/-- The cutoffs are at most `1`. -/
theorem bpzCutoffSeq_le_one (x : ℂ) : bpzCutoffSeq z n x ≤ 1 :=
  bpzCut_le_one _ z x

/-- The cutoffs have compact support. -/
theorem hasCompactSupport_bpzCutoffSeq : HasCompactSupport (bpzCutoffSeq z n) :=
  hasCompactSupport_bpzCut (Nat.cast_add_one_pos n) z

/-- The cutoffs are supported in the region away from `0`, `1`, `z`. -/
theorem tsupport_bpzCutoffSeq_subset :
    tsupport (bpzCutoffSeq z n) ⊆ bpzReg z :=
  tsupport_bpzCut_subset_reg (Nat.cast_add_one_pos n) z

end

/-- The cutoffs equal `1` near any fixed point of the regular region, for `n` large. -/
theorem bpzCutoffSeq_eventually_eq_one {z x : ℂ} (hx : x ∈ bpzReg z) :
    ∀ᶠ n in atTop, bpzCutoffSeq z n =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨R, hR⟩ := bpzCut_eventuallyEq_one hx
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with n hn
  refine hR _ ?_
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-! ### Gradient of the cutoff -/

private theorem norm_fderiv_prod_le_of_mem_Icc {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → ℂ → ℝ} {x : ℂ} (hd : ∀ i ∈ s, DifferentiableAt ℝ (f i) x)
    (hf : ∀ i ∈ s, f i x ∈ Set.Icc 0 1) :
    ‖fderiv ℝ (fun y => ∏ i ∈ s, f i y) x‖ ≤ ∑ i ∈ s, ‖fderiv ℝ (f i) x‖ := by
  rw [fderiv_finsetProd hd]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have h₀ j (hj : j ∈ s.erase i) := (hf j (Finset.mem_of_mem_erase hj)).1
  rw [norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg h₀)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Finset.prod_le_one₀ h₀ (fun j hj => (hf j (Finset.mem_of_mem_erase hj)).2))

/-- Gradient bound for the cutoff at a point away from `0`, `1`, `z`. -/
theorem norm_fderiv_bpzCut_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ w, ‖fderiv ℝ bpzPsi w‖ ≤ C)
    {m : ℝ} (hm : 0 < m) {z ξ : ℂ} (hξz : ξ ≠ z) (hξ0 : ξ ≠ 0) (hξ1 : ξ ≠ 1) :
    ‖fderiv ℝ (bpzCut m z) ξ‖ ≤ 2 * C * (1 / ‖ξ - z‖ + 2 / ‖ξ‖ + 1 / ‖ξ - 1‖) := by
  rw [bpzCut_eq_prod]
  refine (norm_fderiv_prod_le_of_mem_Icc (fun i _ =>
    (contDiff_bpzCutFactors m z i).contDiffAt.differentiableAt (by simp))
    (fun i _ => bpzCutFactors_mem_Icc m z ξ i)).trans ?_
  have h {r : ℝ} {c : ℂ} (hr : 0 ≤ r) (hc : ξ ≠ c) :
      ‖fderiv ℝ (fun x => 1 - bpzBumpAt r c x) ξ‖ ≤ 2 * C / ‖ξ - c‖ := by
    rw [fderiv_const_sub, norm_neg]
    exact norm_fderiv_bpzBumpAt_le hC0 hC hr hc
  have h₀ := h hm.le hξ0
  have h₁ := norm_fderiv_bpzBumpAt_le hC0 hC (inv_nonneg.mpr hm.le) hξ0
  simp only [sub_zero] at h₀ h₁
  have H := add_le_add (h hm.le hξz) (add_le_add h₀ (add_le_add (h hm.le hξ1) h₁))
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, bpzCutFactors,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact H.trans_eq (by ring)

/-! ### The truncated function `g χ_n` -/

theorem bpz_mul_ofReal_eq_smul (a : ℂ) (r : ℝ) : a * (r : ℂ) = r • a := by
  rw [Complex.real_smul, mul_comm]

theorem contDiff_bpzG_mul_bpzCut {m : ℝ} (hm : 0 < m) (z : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => bpzG z x * (bpzCut m z x : ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = z
  · subst hξ
    have hev : (fun x => bpzG ξ x * (bpzCut m ξ x : ℂ)) =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      have hmem : {x : ℂ | m * ‖x - ξ‖ < 1} ∈ 𝓝 ξ :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
      filter_upwards [hmem] with x hx
      simp [bpzCut_eq_zero_of_le_z hm.le hx.le]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (contDiffAt_bpzG hξ).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (contDiff_bpzCut m z).contDiffAt)

/-- The truncated function. -/
theorem contDiff_bpzG_mul_cutoff (z : ℂ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) :=
  contDiff_bpzG_mul_bpzCut (Nat.cast_add_one_pos n) z

theorem bpz_norm_fderiv_bpzG_mul_bpzCut_le {m : ℝ} {z ξ : ℂ} (hξ : ξ ≠ z) :
    ‖fderiv ℝ (fun x => bpzG z x * (bpzCut m z x : ℂ)) ξ‖ ≤
      ‖fderiv ℝ (bpzG z) ξ‖ + ‖bpzG z ξ‖ * ‖fderiv ℝ (bpzCut m z) ξ‖ := by
  have hfun : (fun x => bpzG z x * (bpzCut m z x : ℂ)) = fun x => bpzCut m z x • bpzG z x :=
    funext fun x => bpz_mul_ofReal_eq_smul _ _
  have hg : HasFDerivAt (bpzG z) (fderiv ℝ (bpzG z) ξ) ξ :=
    ((contDiffAt_bpzG hξ (n := (⊤ : ℕ∞))).differentiableAt (by simp)).hasFDerivAt
  have hc : HasFDerivAt (bpzCut m z) (fderiv ℝ (bpzCut m z) ξ) ξ :=
    (((contDiff_bpzCut m z).differentiable (by simp)) ξ).hasFDerivAt
  rw [hfun, (hc.fun_smul hg).fderiv]
  calc ‖bpzCut m z ξ • fderiv ℝ (bpzG z) ξ + (fderiv ℝ (bpzCut m z) ξ).smulRight (bpzG z ξ)‖
      ≤ ‖bpzCut m z ξ • fderiv ℝ (bpzG z) ξ‖ +
          ‖(fderiv ℝ (bpzCut m z) ξ).smulRight (bpzG z ξ)‖ := norm_add_le _ _
    _ = |bpzCut m z ξ| * ‖fderiv ℝ (bpzG z) ξ‖ +
          ‖fderiv ℝ (bpzCut m z) ξ‖ * ‖bpzG z ξ‖ := by
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ ‖fderiv ℝ (bpzG z) ξ‖ + ‖bpzG z ξ‖ * ‖fderiv ℝ (bpzCut m z) ξ‖ := by
        rw [abs_of_nonneg (bpzCut_nonneg m z ξ), mul_comm ‖fderiv ℝ (bpzCut m z) ξ‖]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (bpzCut_le_one m z ξ)) le_rfl

/-- Uniform gradient bound for the truncations, at any scale `m > 0`. -/
theorem bpz_exists_norm_fderiv_bpzG_mul_bpzCut_le (z : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℝ, 0 < m → ∀ ξ : ℂ, ξ ≠ z →
      ‖fderiv ℝ (fun x => bpzG z x * (bpzCut m z x : ℂ)) ξ‖ ≤ A * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fderiv_bpzPsi_le
  obtain ⟨A₁, hA₁0, hA₁⟩ := bpz_exists_norm_fderiv_bpzG_le z
  obtain ⟨A₂, hA₂0, hA₂⟩ := bpz_exists_norm_bpzG_div_le z
  refine ⟨A₁ + 4 * C * A₂, by positivity, fun m hm ξ hξ => ?_⟩
  have h1 := bpz_norm_fderiv_bpzG_mul_bpzCut_le (m := m) hξ
  have hg' := hA₁ ξ hξ
  have hs : 0 ≤ ‖ξ - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  by_cases h01 : ξ = 0 ∨ ξ = 1
  · have hg0 : bpzG z ξ = 0 := by
      rcases h01 with rfl | rfl
      · exact bpzG_zero z
      · exact bpzG_one z
    rw [hg0, norm_zero, zero_mul, add_zero] at h1
    have : 0 ≤ 4 * C * A₂ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by positivity
    linarith only [h1, hg', this]
  · push Not at h01
    obtain ⟨h0, h1'⟩ := h01
    have hχ := norm_fderiv_bpzCut_le hC0 hC hm hξ h0 h1'
    have hdiv := hA₂ ξ hξ h0 h1'
    have hg0 : 0 ≤ ‖bpzG z ξ‖ := norm_nonneg _
    have hx : 0 ≤ ‖bpzG z ξ‖ / ‖ξ - z‖ := by positivity
    have hw : 0 ≤ ‖bpzG z ξ‖ / ‖ξ - 1‖ := by positivity
    have hy : 0 ≤ ‖bpzG z ξ‖ / ‖ξ‖ := by positivity
    have h2 : ‖bpzG z ξ‖ * ‖fderiv ℝ (bpzCut m z) ξ‖ ≤
        2 * C * (2 * (A₂ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)))) := by
      calc ‖bpzG z ξ‖ * ‖fderiv ℝ (bpzCut m z) ξ‖
          ≤ ‖bpzG z ξ‖ * (2 * C * (1 / ‖ξ - z‖ + 2 / ‖ξ‖ + 1 / ‖ξ - 1‖)) :=
            mul_le_mul_of_nonneg_left hχ hg0
        _ = 2 * C * (‖bpzG z ξ‖ / ‖ξ - z‖ + 2 * (‖bpzG z ξ‖ / ‖ξ‖) +
              ‖bpzG z ξ‖ / ‖ξ - 1‖) := by ring
        _ ≤ 2 * C * (2 * (A₂ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc ‖fderiv ℝ (fun x => bpzG z x * (bpzCut m z x : ℂ)) ξ‖
        ≤ A₁ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) +
          2 * C * (2 * (A₂ * (1 + ‖ξ - z‖ ^ (-2 : ℝ)))) := h1.trans (add_le_add hg' h2)
      _ = (A₁ + 4 * C * A₂) * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by ring

/-- Uniform gradient bound, singular only at `z`. -/
theorem norm_fderiv_bpzG_mul_cutoff_le {z : ℂ} (_hz0 : z ≠ 0) (_hz1 : z ≠ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (ξ : ℂ), ξ ≠ z →
      ‖fderiv ℝ (fun x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) ξ‖ ≤
        A * (1 + ‖ξ - z‖ ^ (-2 : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := bpz_exists_norm_fderiv_bpzG_mul_bpzCut_le z
  exact ⟨A, hA0, fun n ξ hξ => hA _ (Nat.cast_add_one_pos n) ξ hξ⟩

/-! ### Uniform difference-quotient bound -/

/-- A gradient bound with the singular weight yields a difference-quotient bound for points that
are close compared to their distance to `z`. -/
theorem bpz_norm_sub_le_near {z : ℂ} {H : ℂ → ℂ} {A : ℝ} (hA0 : 0 ≤ A)
    (hH : Differentiable ℝ H)
    (hA : ∀ ξ : ℂ, ξ ≠ z → ‖fderiv ℝ H ξ‖ ≤ A * (1 + ‖ξ - z‖ ^ (-2 : ℝ))) {x y : ℂ}
    (hx : x ≠ z) (hxy : ‖x - y‖ ≤ ‖x - z‖ / 2) :
    ‖H x - H y‖ ≤ 4 * A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * ‖x - y‖ := by
  have ht : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hconv : Convex ℝ (Metric.closedBall x (‖x - z‖ / 2)) := convex_closedBall _ _
  have hxs : x ∈ Metric.closedBall x (‖x - z‖ / 2) := Metric.mem_closedBall_self (by positivity)
  have hys : y ∈ Metric.closedBall x (‖x - z‖ / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact hxy
  have hbound : ∀ w ∈ Metric.closedBall x (‖x - z‖ / 2),
      ‖fderiv ℝ H w‖ ≤ A * (1 + 4 * ‖x - z‖ ^ (-2 : ℝ)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hwz : ‖x - z‖ / 2 ≤ ‖w - z‖ := by
      have := bpz_norm_sub_ge x w z
      linarith
    have hwz0 : w ≠ z := by
      rintro rfl
      simp only [sub_self, norm_zero] at hwz
      linarith
    calc ‖fderiv ℝ H w‖ ≤ A * (1 + ‖w - z‖ ^ (-2 : ℝ)) := hA w hwz0
      _ ≤ A * (1 + 4 * ‖x - z‖ ^ (-2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (bpz_rpow_neg_two_le_four_mul ht hwz)) hA0
  have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le (fun w _ => hH w) hbound hxs hys
  have hu : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  rw [norm_sub_rev (H x)]
  calc ‖H y - H x‖ ≤ A * (1 + 4 * ‖x - z‖ ^ (-2 : ℝ)) * ‖y - x‖ := hmv
    _ = A * (1 + 4 * ‖x - z‖ ^ (-2 : ℝ)) * ‖x - y‖ := by rw [norm_sub_rev y x]
    _ ≤ 4 * A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * ‖x - y‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        linarith only [hA0]

theorem bpz_norm_bpzG_mul_bpzCut_le (m : ℝ) (z x : ℂ) :
    ‖bpzG z x * (bpzCut m z x : ℂ)‖ ≤ ‖bpzG z x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bpzCut_nonneg m z x)]
  exact mul_le_of_le_one_right (norm_nonneg _) (bpzCut_le_one m z x)

/-- Uniform difference-quotient bound. -/
theorem norm_bpzG_mul_cutoff_sub_le (z : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (x y : ℂ), x ≠ z → y ≠ z →
      ‖bpzG z x * (bpzCutoffSeq z n x : ℂ) - bpzG z y * (bpzCutoffSeq z n y : ℂ)‖ ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) * ‖x - y‖ := by
  obtain ⟨A₂, hA₂0, hA₂⟩ := bpz_exists_norm_fderiv_bpzG_mul_bpzCut_le z
  obtain ⟨K, hK0, hK⟩ := bpz_exists_norm_bpzG_le z
  refine ⟨4 * A₂ + 4 * K, by positivity, fun n x y hx hy => ?_⟩
  have hm : (0 : ℝ) < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  have hH := (contDiff_bpzG_mul_bpzCut hm z).differentiable (by simp)
  have hA := fun ξ hξ => hA₂ _ hm ξ hξ
  have sx : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  have sy : 0 ≤ ‖y - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  have hd : 0 ≤ ‖x - y‖ := norm_nonneg _
  show ‖bpzG z x * (bpzCut ((n : ℝ) + 1) z x : ℂ) - bpzG z y * (bpzCut ((n : ℝ) + 1) z y : ℂ)‖ ≤
    (4 * A₂ + 4 * K) * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) * ‖x - y‖
  by_cases h1 : ‖x - y‖ ≤ ‖x - z‖ / 2
  · refine (bpz_norm_sub_le_near hA₂0 hH hA hx h1).trans ?_
    linarith [mul_nonneg hK0 (mul_nonneg hd (add_nonneg sx sy)), mul_nonneg hK0 hd,
      mul_nonneg hA₂0 (mul_nonneg hd sy)]
  by_cases h2 : ‖y - x‖ ≤ ‖y - z‖ / 2
  · have h := bpz_norm_sub_le_near hA₂0 hH hA hy h2
    rw [norm_sub_rev (bpzG z y * _), norm_sub_rev y x] at h
    refine h.trans ?_
    linarith [mul_nonneg hK0 (mul_nonneg hd (add_nonneg sx sy)), mul_nonneg hK0 hd,
      mul_nonneg hA₂0 (mul_nonneg hd sx)]
  · have h1' : ‖x - z‖ < 2 * ‖x - y‖ := by linarith [not_le.1 h1]
    have h2' : ‖y - z‖ < 2 * ‖x - y‖ := by
      have := not_le.1 h2
      rw [norm_sub_rev y x] at this
      linarith
    have gx := hK x hx
    have gy := hK y hy
    have hKx : 0 ≤ K * (1 + ‖x - z‖ ^ (-2 : ℝ)) := by positivity
    have hKy : 0 ≤ K * (1 + ‖y - z‖ ^ (-2 : ℝ)) := by positivity
    calc _ ≤ ‖bpzG z x * (bpzCut ((n : ℝ) + 1) z x : ℂ)‖ +
          ‖bpzG z y * (bpzCut ((n : ℝ) + 1) z y : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖bpzG z x‖ + ‖bpzG z y‖ :=
          add_le_add (bpz_norm_bpzG_mul_bpzCut_le _ _ _) (bpz_norm_bpzG_mul_bpzCut_le _ _ _)
      _ ≤ K * (1 + ‖x - z‖ ^ (-2 : ℝ)) * ‖x - z‖ + K * (1 + ‖y - z‖ ^ (-2 : ℝ)) * ‖y - z‖ :=
          add_le_add gx gy
      _ ≤ K * (1 + ‖x - z‖ ^ (-2 : ℝ)) * (2 * ‖x - y‖) +
            K * (1 + ‖y - z‖ ^ (-2 : ℝ)) * (2 * ‖x - y‖) :=
          add_le_add (mul_le_mul_of_nonneg_left h1'.le hKx) (mul_le_mul_of_nonneg_left h2'.le hKy)
      _ ≤ (4 * A₂ + 4 * K) * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) * ‖x - y‖ := by
          linarith [mul_nonneg hK0 (mul_nonneg hd sx), mul_nonneg hK0 (mul_nonneg hd sy),
            mul_nonneg hA₂0 (mul_nonneg hd (add_nonneg (add_nonneg zero_le_one sx) sy)),
            mul_nonneg hK0 hd]

end DOZZ.Proofs
