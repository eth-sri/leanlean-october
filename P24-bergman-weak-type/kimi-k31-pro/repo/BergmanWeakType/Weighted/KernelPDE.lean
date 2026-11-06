/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! # The real differential equation for the positive weighted kernel

The calculations use Cartesian coordinates and ordinary one-variable derivatives in each
coordinate. The resulting second-order operator is the Laplacian with radial drift from the
source proof.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace BergmanWeakType.Weighted

/-- The squared denominator in Cartesian coordinates. -/
def denominator (a b x y : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) - 2 * (a * x + b * y) + 1

/-- A real power of the squared denominator. -/
def powerKernel (q a b x y : ℝ) : ℝ := denominator a b x y ^ q

theorem denominator_hasDerivAt_x (a b x y : ℝ) :
    HasDerivAt (fun u ↦ denominator a b u y)
      (2 * ((a ^ 2 + b ^ 2) * x - a)) x := by
  convert (((((hasDerivAt_id x).pow 2).add_const (y ^ 2)).const_mul (a ^ 2 + b ^ 2)).sub
    ((((hasDerivAt_id x).const_mul a).add_const (b * y)).const_mul 2)).add_const 1 using 1
  · rfl
  · norm_num
    ring

theorem powerKernel_hasDerivAt_x (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ powerKernel q a b u y)
      (2 * q * ((a ^ 2 + b ^ 2) * x - a) * denominator a b x y ^ (q - 1)) x := by
  convert (denominator_hasDerivAt_x a b x y).rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · ring

theorem powerKernel_deriv_x (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    deriv (fun u ↦ powerKernel q a b u y) x =
      2 * q * ((a ^ 2 + b ^ 2) * x - a) * denominator a b x y ^ (q - 1) :=
  (powerKernel_hasDerivAt_x q a b x y hd).deriv

theorem powerKernel_hasDerivAt_deriv_x (q a b x y : ℝ)
    (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ deriv (fun v ↦ powerKernel q a b v y) u)
      (2 * q * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) +
        4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 *
          denominator a b x y ^ (q - 2)) x := by
  have hpow := (denominator_hasDerivAt_x a b x y).rpow_const (p := q - 1) (Or.inl hd.ne')
  have hlin := ((hasDerivAt_id x).const_mul (a ^ 2 + b ^ 2)).sub_const a
  have hformula : HasDerivAt
      (fun u ↦ 2 * q * ((a ^ 2 + b ^ 2) * u - a) * denominator a b u y ^ (q - 1))
      (2 * q * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) +
        4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 *
          denominator a b x y ^ (q - 2)) x := by
    convert (hlin.mul hpow).const_mul (2 * q) using 1
    · funext u
      dsimp
      ring
    · simp only [show q - 1 - 1 = q - 2 by ring, id_eq]
      ring
  apply hformula.congr_of_eventuallyEq
  have hpos : ∀ᶠ u in nhds x, 0 < denominator a b u y :=
    (denominator_hasDerivAt_x a b x y).continuousAt.eventually (lt_mem_nhds hd)
  exact hpos.mono fun u hu ↦ powerKernel_deriv_x q a b u y hu

/-- The Cartesian denominator is exactly the squared modulus of the Bergman denominator. -/
theorem denominator_eq_norm_sq (z w : ℂ) :
    denominator w.re w.im z.re z.im = ‖1 - z * star w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.one_im,
    Complex.mul_im]
  unfold denominator
  ring

end BergmanWeakType.Weighted
