module

public import OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneous

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def dyadicLength (U : ℝ) : ℕ := HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1

structure Witness {ι : Type*} (χ : ι→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  label : ι
  zero : ℂ
  zero_eq : LFunction (χ label) zero=0
  zero_lower : a≤zero.re
  zero_height : |zero.im|≤(3*i : ℕ)*T
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  nu : ℝ
  r : ℝ
  m : ℝ
  nu_bound : ‖nu‖≤allowance
  left_scale : U^r=(2 : ℝ)^left.val
  right_scale : U^m=(2 : ℝ)^right.val
  inverse_length_lower : tstar-1/2-76*ε≤r
  inverse_length_upper : r≤tstar+ε
  plain_length_lower : 0≤m
  plain_length_upper : m≤1/2+75*ε
  inverse_spike : U^((2*a-1)*r-2*ε)≤
    ‖polynomial (χ label) true
      (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
      (U^r) zero.re (2*Real.pi*nu-zero.im)‖^2
  plain_spike : U^((2*a-1)*m-2*ε)≤
    ‖polynomial (χ label) false positiveAnnular (U^m) zero.re (2*Real.pi*nu-zero.im)‖^2

def Witness.frequency {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : ℝ := 2*Real.pi*w.nu-w.zero.im

theorem Witness.frequency_bound {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) :
    |w.frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T := by
  have hnu : |w.nu|≤allowance := by simpa only [Real.norm_eq_abs] using w.nu_bound
  have hh := abs_sub_le (2*Real.pi*w.nu) 0 w.zero.im
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hnu (by positivity)) w.zero_height)

theorem Witness.real_part_upper {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : w.zero.re≤1 := by
  by_contra hn
  exact LFunction_ne_zero_of_one_lt_re (χ w.label) (lt_of_not_ge hn) w.zero_eq

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
