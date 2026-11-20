module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib

/-! # A convex regularization of absolute value, fixing zero -/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Real
open scoped ContDiff

def hyp (ε x : ℝ) := √(x^2+ε^2)
def modulus (ε x : ℝ) := hyp ε x - ε

variable {ε : ℝ} (hε : 0 < ε)

include hε

private theorem hp (x : ℝ) : 0 < hyp ε x := by dsimp [hyp]; positivity
omit hε in
private theorem hsq (x : ℝ) : hyp ε x ^ 2 = x^2+ε^2 := sq_sqrt (by positivity)

theorem sm_modulus : ContDiff ℝ ∞ (modulus ε) :=
  (((contDiff_id.pow 2).add contDiff_const).sqrt fun x => (by positivity : x^2+ε^2 ≠ 0)).sub contDiff_const

@[simp] theorem modulus_zero : modulus ε 0 = 0 := by simp [modulus,hyp,sqrt_sq hε.le]

variable (x : ℝ)

private theorem hd : HasDerivAt (hyp ε) (x / hyp ε x) x := by
  have h : HasDerivAt (fun y : ℝ => y^2+ε^2) (2*x) x := by
    simpa only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] using! ((hasDerivAt_id x).pow 2).add_const (ε^2)
  convert h.sqrt (by dsimp; positivity) using 1
  · rfl
  · unfold hyp; ring

theorem dmodulus : deriv (modulus ε) x = x / hyp ε x := (show HasDerivAt (modulus ε) _ x from (hd hε x).sub_const ε).deriv

theorem modulus_convex : 0 ≤ deriv (deriv (modulus ε)) x := by
  have H : HasDerivAt (fun y : ℝ => y / hyp ε y) _ x := (hasDerivAt_id x).div (hd hε x) (hp hε x).ne'
  rw [funext (dmodulus hε), H.deriv]
  apply div_nonneg _ (sq_nonneg _); rw [one_mul,id_eq,sub_nonneg,← mul_div_assoc,div_le_iff₀ (hp hε x)]
  nlinarith [hsq (ε := ε) x]

theorem modulus_bounds : 0 ≤ modulus ε x ∧ modulus ε x ≤ |x| ∧ |x| ≤ modulus ε x + ε := by
  have hs := hsq (ε := ε) x; have h := (hp hε x).le; dsimp [modulus]
  have ha := abs_nonneg x; have hsx := sq_abs x
  constructor; · nlinarith [sq_nonneg x]
  constructor; · nlinarith [mul_nonneg hε.le ha]
  nlinarith [sq_nonneg ε]

theorem slope_bound : |deriv (modulus ε) x| ≤ 1 := by
  rw [dmodulus hε,abs_div,abs_of_pos (hp hε x),div_le_one (hp hε x)]
  simpa [modulus] using (modulus_bounds hε x).2.2

theorem defect_bound : |modulus ε x - deriv (modulus ε) x * x| ≤ ε := by
  have h := dmodulus hε x; have hp' := hp hε x; have he := (modulus_bounds hε x).1
  rw [h,modulus,div_mul_eq_mul_div,abs_le]; dsimp [modulus] at he
  constructor <;> (field_simp; nlinarith [hsq (ε := ε) x, mul_nonneg hε.le he])

end HypoellipticAleksandrov.Parabolic.Transposition
