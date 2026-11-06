module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosPlanarWindow

@[expose] public section
set_option maxHeartbeats 0


                                                                           

noncomputable section


open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosFinitePrefix {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (H : ℕ) : ℂ :=
  ∑ j ∈ Finset.range H, f (j : ZMod N)

def sargosPrefixKernel {N : ℕ} [NeZero N] (H : ℕ) (k : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N))

section
variable {N : ℕ} [NeZero N]
include N

theorem sargos_stdAddChar_norm  (k : ZMod N) :
    ‖ZMod.stdAddChar k‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem sargosFinitePrefix_eq_fourier 
    (f : ZMod N → ℂ) (H : ℕ) :
    sargosFinitePrefix f H =
      ∑ k : ZMod N, sargosPrefixKernel H k*ZMod.dft f k := by
  unfold sargosFinitePrefix sargosPrefixKernel
  calc
    _ = ∑ j ∈ Finset.range H, (N : ℂ)⁻¹ *
        ∑ k : ZMod N, ZMod.stdAddChar (k*(j : ZMod N))*ZMod.dft f k := by
      apply Finset.sum_congr rfl
      intro j hj
      conv_lhs => rw [← ZMod.dft.symm_apply_apply f]
      rw [ZMod.invDFT_apply]
      simp only [smul_eq_mul]
    _ = _ := by
      simp_rw [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      ring

theorem sargosPrefixKernel_zero  (H : ℕ) :
    sargosPrefixKernel H (0 : ZMod N) = (H : ℂ)/(N : ℂ) := by
  simp [sargosPrefixKernel,div_eq_mul_inv,mul_comm]

theorem norm_sargosPrefixKernel_zero  (H : ℕ) :
    ‖sargosPrefixKernel H (0 : ZMod N)‖ = (H : ℝ)/(N : ℝ) := by
  rw [sargosPrefixKernel_zero,norm_div,Complex.norm_natCast,Complex.norm_natCast]
end


theorem norm_sargosPrefixKernel_zero_le_one {N H : ℕ} [NeZero N]
    (hH : H ≤ N) :
    ‖sargosPrefixKernel H (0 : ZMod N)‖ ≤ 1 := by
  rw [norm_sargosPrefixKernel_zero]
  exact (div_le_one (by exact_mod_cast NeZero.pos N)).mpr (by exact_mod_cast hH)

section
variable {N : ℕ} [NeZero N] (H : ℕ) (k : ZMod N)
include N H k

theorem sargos_sum_stdAddChar_eq_geom  :
    (∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N))) =
      ∑ j ∈ Finset.range H, (ZMod.stdAddChar k)^j := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm,← nsmul_eq_mul,AddChar.map_nsmul_eq_pow]

theorem sargos_sum_stdAddChar_mul_sub_one  :
    (∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N)))*
      (ZMod.stdAddChar k-1) = (ZMod.stdAddChar k)^H-1 := by
  rw [sargos_sum_stdAddChar_eq_geom,geom_sum_mul]
end



